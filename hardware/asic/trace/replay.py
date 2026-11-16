#!/usr/bin/env python3
"""Convert recorded real native-verifier primitive inputs to checked ASIC commands.
Counts describe primitive replay including operand traffic, not complete verifier
latency: branch checks, base-field operations, and parsing stay on the host.
"""
import pathlib,sys,collections,json,hashlib
root=pathlib.Path(__file__).resolve().parents[1];sys.path.insert(0,str(root/'gen'))
from gen_vectors import Emu
source=root/'trace/sta1_calls.txt';out=root/'vec/trace_sta1_real.hex';e=Emu(out);counts=collections.Counter()
e.mark(0)
for line in source.read_text().splitlines():
    op,*ws=line.split();ws=[int(x,16) for x in ws];counts[op]+=1
    if op=='p2':
        assert len(ws)==12;e.wr_all(ws);e.perm()
        for i in range(12):e.rd_st(i)
    elif op=='ext4':
        assert len(ws)==8;e.wr_all(ws+[0]*4);e.emuladd();e.rd4()
    else:raise ValueError(op)
e.mark(400);e.f.close()
proof=root/'trace/sta1.bin';assert proof.read_bytes()[:8]==b'QSAGSTA1'
info={'proof_bytes':proof.stat().st_size,'proof_sha256':hashlib.sha256(proof.read_bytes()).hexdigest(),'call_trace_sha256':hashlib.sha256(source.read_bytes()).hexdigest(),'calls':dict(counts),'scope':'accepted QSAGSTA1 pinned-statement relation; primitive-call replay; not full signature recursion or complete RTL verifier'}
(root/'trace/sta1_manifest.json').write_text(json.dumps(info,indent=2)+'\n');print(json.dumps(info))
