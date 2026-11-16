# One-time migration for an already instrumented isolated copy. New copies use instrument.py.
import pathlib,sys
p=pathlib.Path(sys.argv[1])/'crates/qsag-agg/src/sponge.rs';s=p.read_text();needle='pub(super) const fn permute(input: &[u64; 12]) -> [u64; 12] {';assert s.count(needle)==1
s=s.replace(needle,'pub(super) fn permute(input: &[u64; 12]) -> [u64; 12] {\n        #[cfg(test)] crate::asic_trace::words("p2", input);');p.write_text(s)
