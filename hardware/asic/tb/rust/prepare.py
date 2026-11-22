"""Install verification-only hooks in the designated hbox build copy."""
from pathlib import Path
import sys

root = Path(sys.argv[1]).resolve()
if root != Path("/var/tmp/deep5-qsagni/rust-unified"):
    raise SystemExit("prepare the hbox source copy under /var/tmp/deep5-qsagni/rust-unified")
here = Path(__file__).resolve().parent
crate = root / "crates/qsag-agg"
v2 = crate / "src/zk_hem/v2"
def edit(path, old, new):
    text = path.read_text()
    if new in text:
        return
    assert text.count(old) == 1, (path, old)
    path.write_text(text.replace(old,new))

def install(source, dest):
    data = source.read_bytes()
    if not dest.exists() or dest.read_bytes() != data:
        dest.write_bytes(data)

install(here/"port.rs",v2/"port.rs")
for name in ["kat","live"]:
    install(here/f"{name}.rs",crate/f"examples/deep5_{name}.rs")
edit(v2.with_suffix(".rs"),"pub mod hash;", "pub mod hash;\npub mod port;")
for name,domain in [("tree_into",6),("fs_into",7)]:
    sig=f"fn {name}(self, input: &[u8], out: &mut [u8]) {{"
    edit(v2/"hash.rs",sig,sig+f"""
        if self.turbo && super::port::with(|p| p.hash({domain}, input, out)).is_some() {{ return; }}""")
# Use the first active leaf as the path for MERKLE_PATH_V2. Its siblings may
# themselves be reconstructed subtrees from a Steiner opening. Other parents
# use Hasher::node, which also dispatches to the hardware sponge.
edit(v2/"hash.rs","    let mut cursor = 0usize;", """    let live = super::port::with(|_| ()).is_some();
    let mut first_path = Vec::new();
    let mut cursor = 0usize;""")
edit(v2/"hash.rs", "            active[write] = (u >> 1, hasher.node((u >> 1) as u32, &left, &right));",
"""            active[write] = if live && write == 0 {
                first_path.push(hs);
                (u >> 1, hu) // carried leaf, reduced by the hardware path command at the end
            } else {
                (u >> 1, hasher.node((u >> 1) as u32, &left, &right))
            };""")
edit(v2/"hash.rs","    cursor == siblings.len()\n", """    if live {
        return cursor == siblings.len() && active.len() == 1 && active[0].0 == 1 &&
            super::port::with(|p| p.path(stage,log_leaves,sorted_leaves[0].0,
                &sorted_leaves[0].1,&first_path,root)).unwrap();
    }
    cursor == siblings.len()
""")
edit(v2/"protocol.rs", "        let at_one = round.iter().fold(E::ZERO, |acc, &c| acc + c);",
"""        if super::port::with(|_| ()).is_some() {
            tr.absorb_fp5_slice(label,round);
            let r = tr.squeeze_fp5(label);
            claim = super::port::with(|p| p.round(round,r,claim)).unwrap()?;
            point.push(r);
            continue;
        }
        let at_one = round.iter().fold(E::ZERO, |acc, &c| acc + c);""")
edit(v2/"pcs.rs","    if kernel.apply(final_coeffs) != claim {",
"""    let applied = kernel.apply(final_coeffs);
    if !super::port::with(|p| p.eq(applied,claim)).unwrap_or(applied == claim) {""")
edit(v2/"pcs.rs",".all(|&(y, v)| eval_at_base(final_coeffs, y) == v)",
""".all(|&(y, v)| super::port::with(|p| {
            let computed = p.horner(final_coeffs,Fp5::from_base(y));
            p.eq(computed,v)
        }).unwrap_or_else(|| eval_at_base(final_coeffs,y) == v))""")
edit(v2/"pcs.rs","            vals[t] = g + (alpha + beta.mul_base(xt.square())) * (f + theta * g);",
"""            let gamma = alpha + beta.mul_base(xt.square());
            let slope = f + theta * g;
            vals[t] = super::port::with(|p| p.fold_affine(g,slope,gamma))
                .unwrap_or_else(|| g + gamma * slope);""")
# All challenge-field arithmetic during live verification runs on the shared
# multiplier. Software remains the unmodified numerical oracle before connect().
field=v2/"field5.rs"
for sig,operation in [
    ("mul_add(self, rhs: Self, addend: Self)", "p.muladd(self,rhs,addend)"),
    ("const_add(self, rhs: Self)","p.linear(0x21,self,rhs)"),
    ("const_sub(self, rhs: Self)","p.linear(0x22,self,rhs)"),
    ("square(self)","p.muladd(self,self,Self::ZERO)"),
    ("mul_base(self, s: Goldilocks)","p.linear(0x27,self,Self::from_base(s))"),
    ("inv(self)","p.inverse(self)"),
]:
    old=f"pub const fn {sig} -> Self {{"
    edit(field,old, f"pub fn {sig} -> Self {{\n        if let Some(x) = super::port::with(|p| {operation}) {{ return x; }}")
# Runtime instrumentation requires non-const callers in the verifier build.
for name in ["const_mul","const_neg","double","conjugate_product","norm_to_base","norm","inverse","pow","pow_limbs"]:
    s=field.read_text().replace(f"const fn {name}(",f"fn {name}(")
    if s != field.read_text():
        field.write_text(s)
