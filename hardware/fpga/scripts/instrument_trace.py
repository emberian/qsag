#!/usr/bin/env python3
"""Instrument ONLY an isolated scratch copy. Never point this at the working repository.
Captures the accepted QSAGSTA1 root verification of the existing small pinned-statement test.
The relation is explicitly NOT a signature-authorization/recursive-merge benchmark.
"""
from pathlib import Path
import sys
repo=Path(sys.argv[1]).resolve()
assert str(repo).startswith('/home/build/qsag-ni-fpga/work/')
p=repo/'crates/qsag-agg/src/fpga_trace.rs'
p.write_text('''use crate::field::GoldilocksExt4 as E;
use std::{fs::File, io::{BufWriter, Write}, sync::Mutex};
static TRACE: Mutex<Option<BufWriter<File>>> = Mutex::new(None);
pub fn start() { *TRACE.lock().unwrap() = Some(BufWriter::new(File::create(std::env::var("QSAG_FPGA_TRACE").unwrap()).unwrap())); }
pub fn stop() { if let Some(mut w) = TRACE.lock().unwrap().take() { w.flush().unwrap(); } }
pub fn words(kind: &str, xs: &[u64]) {
    if let Some(w) = TRACE.lock().unwrap().as_mut() {
        write!(w, "{} {}", kind, xs.len()).unwrap();
        for x in xs { write!(w, " {:016x}", x).unwrap(); }
        writeln!(w).unwrap();
    }
}
pub fn ext(kind: &str, xs: &[E]) {
    let mut out = std::vec::Vec::new();
    for x in xs { out.extend(x.to_limbs().map(|x| x.to_canonical_u64())); }
    words(kind, &out);
}
''')
p=repo/'crates/qsag-agg/src/lib.rs';p.write_text(p.read_text()+'\nmod fpga_trace;\n')
p=repo/'crates/qsag-agg/src/sponge.rs';s=p.read_text();s=s.replace('pub(super) const fn permute(input:', 'pub(super) fn permute(input:')
a=s.index('    pub(super) fn permute(');b=s.index('\n}\n',a)
seg=s[a:b];assert seg.count('        st\n    }')==1
seg=seg.replace('        st\n    }','''        let mut trace = [0u64;24]; trace[..12].copy_from_slice(input); trace[12..].copy_from_slice(&st);
        crate::fpga_trace::words("P", &trace);
        st
    }''');s=s[:a]+seg+s[b:]
a=s.index('pub fn poseidon2_compress12_ff(');b=s.index('\n}\n',a)
seg=s[a:b];seg=seg.replace('    qsag_asm::volatile_fill(&mut perm,', '''    let mut trace = [0u64;16];
    trace[..12].copy_from_slice(&st.map(Goldilocks::to_canonical_u64));
    trace[12..].copy_from_slice(&out.map(Goldilocks::to_canonical_u64));
    crate::fpga_trace::words("J", &trace);
    qsag_asm::volatile_fill(&mut perm,''');s=s[:a]+seg+s[b:];p.write_text(s)
p=repo/'crates/qsag-agg/src/field.rs';s=p.read_text().replace('self.mul_add(rhs, Self::ZERO)','self.const_mul_add(rhs, Self::ZERO)')
s=s.replace('pub const fn mul_add(self, rhs: Self, addend: Self) -> Self {','''pub fn mul_add(self, rhs: Self, addend: Self) -> Self {
        let out = self.const_mul_add(rhs, addend);
        crate::fpga_trace::ext("E", &[self, rhs, addend, out]); out
    }
    pub const fn const_mul_add(self, rhs: Self, addend: Self) -> Self {''')
a=s.index('impl Mul for GoldilocksExt4');b=s.index('impl MulAssign',a);seg=s[a:b].replace('self.const_mul(rhs)','self.mul_add(rhs, Self::ZERO)');s=s[:a]+seg+s[b:];p.write_text(s)
p=repo/'crates/qsag-agg/src/zk_hem/protocol.rs';s=p.read_text();old='''        claim = eval_poly(round, c);
        point.push(c);''';new='''        let prev = claim;
        claim = eval_poly(round, c);
        let mut trace = round.clone(); trace.extend([c, prev, claim]);
        crate::fpga_trace::ext("S", &trace);
        point.push(c);''';assert old in s;s=s.replace(old,new);p.write_text(s)
p=repo/'crates/qsag-agg/src/recursive.rs';s=p.read_text();a=s.index('    fn roster_root_verifier_and_native_merge_binding()');b=s.index('\n    #[',a);seg=s[a:b]
seg=seg.replace('WhirSecurityRegime::TurboShakeCdhz25JohnsonQrom128','WhirSecurityRegime::Poseidon2Cdhz25JohnsonQrom128')
needle='''        assert!(verify_succinct_subtree_aggregate_against_roster_root(
            root_vk, &statement, &proof
        ));'''
assert needle in seg
seg=seg.replace(needle,'''        let wire = proof.to_bytes();
        assert_eq!(&wire[..8], b"QSAGSTA1");
        let decoded = SuccinctSubtreeAggregate::from_bytes_canonical(root_vk, &wire).unwrap();
        std::fs::write(std::env::var("QSAG_FPGA_PROOF").unwrap(), &wire).unwrap();
        crate::fpga_trace::start();
        assert!(verify_succinct_subtree_aggregate_against_roster_root(
            root_vk, &statement, &decoded
        ));
        crate::fpga_trace::stop();
        std::println!("FPGA_REAL_QSAGSTA1 proof_bytes={} accepted=true pinned_statement=true", wire.len());''')
s=s[:a]+seg+s[b:];p.write_text(s)
print('instrumented isolated Rust verifier:',repo)
