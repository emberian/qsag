#!/usr/bin/env python3
"""Instrument an isolated remote copy only. Export primitive calls during a real
QSAGSTA1 root-verifier test; never instrument proving and never modify upstream.
The fixture uses a small pinned-public-input relation, NOT full signature recursion.
"""
import pathlib,sys
root=pathlib.Path(sys.argv[1]); src=root/'crates/qsag-agg/src'
p=src/'lib.rs';s=p.read_text();s+='''
#[cfg(test)]
pub(crate) mod asic_trace {
    use std::cell::RefCell;
    use std::io::Write;
    std::thread_local! { static OUT: RefCell<Option<std::io::BufWriter<std::fs::File>>> = const { RefCell::new(None) }; }
    pub fn start() { OUT.with(|o| *o.borrow_mut() = Some(std::io::BufWriter::new(std::fs::File::create(std::env::var("QSAG_ASIC_TRACE").unwrap()).unwrap()))); }
    pub fn end() { OUT.with(|o| { if let Some(mut f) = o.borrow_mut().take() { f.flush().unwrap(); } }); }
    pub fn words(op: &str, words: &[u64]) { OUT.with(|o| { if let Some(f) = o.borrow_mut().as_mut() { write!(f, "{}",op).unwrap(); for w in words { write!(f," {:016x}",w).unwrap(); } writeln!(f).unwrap(); } }); }
}
''';p.write_text(s)
p=src/'sponge.rs';s=p.read_text();needle='pub fn poseidon2_perm12(st: &mut [Goldilocks; 12]) {';assert s.count(needle)==1
s=s.replace(needle,needle+'\n    #[cfg(test)] crate::asic_trace::words("p2", &st.map(Goldilocks::to_canonical_u64));');p.write_text(s)
p=src/'field.rs';s=p.read_text();needle='''    fn mul(self, rhs: Self) -> Self {
        self.const_mul(rhs)
    }''';assert s.count(needle)==1
s=s.replace(needle,'''    fn mul(self, rhs: Self) -> Self {
        #[cfg(test)] crate::asic_trace::words("ext4", &[
          self.c0.c0.to_canonical_u64(),self.c0.c1.to_canonical_u64(),self.c1.c0.to_canonical_u64(),self.c1.c1.to_canonical_u64(),
          rhs.c0.c0.to_canonical_u64(),rhs.c0.c1.to_canonical_u64(),rhs.c1.c0.to_canonical_u64(),rhs.c1.c1.to_canonical_u64()]);
        self.const_mul(rhs)
    }''');p.write_text(s)
p=src/'recursive.rs';s=p.read_text();a=s.index('    fn roster_root_verifier_and_native_merge_binding()');b=s.index('\n    #[test]',a);t=s[a:b]
# Use the real Poseidon2 backend so all hashing primitives have RTL command coverage.
t=t.replace('WhirSecurityRegime::TurboShakeCdhz25JohnsonQrom128','WhirSecurityRegime::Poseidon2Cdhz25JohnsonQrom128')
needle='''        assert!(verify_succinct_subtree_aggregate_against_roster_root(
            root_vk, &statement, &proof
        ));''';assert t.count(needle)==1
t=t.replace(needle,'        crate::asic_trace::start();\n'+needle+'\n        crate::asic_trace::end();')
t=t.replace('        let wire = proof.to_bytes();','''        let wire = proof.to_bytes();
        assert_eq!(&wire[..8], b"QSAGSTA1");
        std::fs::write(std::env::var("QSAG_ASIC_PROOF").unwrap(), &wire).unwrap();
        std::println!("ASIC QSAGSTA1 bytes={} pinned-statement relation; native verifier accepted",wire.len());''')
s=s[:a]+t+s[b:];p.write_text(s)
