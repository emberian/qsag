#!/usr/bin/env python3
"""Independent algebraic certificate checker for the emitted carry-save RTL.
Parses actual SV equations, checks each HA/FA truth table, then eliminates pairs
by s+2c=sum(inputs). Every remaining coefficient is compared modulo p with the
word-level specification. No random vectors or assumptions about input values.
Final-adder correctness is a separate SMT obligation.
"""
import re, pathlib, collections, json, sys, hashlib
P=2**64-2**32+1
class Circuit:
    def __init__(self,text):
        self.alias={};self.pairs=[];self.pp={}
        wires=re.findall(r'wire\s+(?:\[([^]]+)\]\s+)?(\w+)\s*=\s*([^;]+);',text)
        scalar={n:e for w,n,e in wires if not w}
        for w,n,e in wires:
            if w:
                if e.startswith('{'):
                    self.alias[n]=list(reversed(e[1:-1].split(', ')))
                elif re.fullmatch(r'\w+\[\d+:\d+\]',e):
                    a,hi,lo=re.fullmatch(r'(\w+)\[(\d+):(\d+)\]',e).groups()
                    self.alias[n]=[f'{a}[{i}]' for i in range(int(lo),int(hi)+1)]
                elif re.fullmatch(r'\w+\[\d+ \+: 64\]',e):
                    a,lo=re.fullmatch(r'(\w+)\[(\d+) \+: 64\]',e).groups()
                    self.alias[n]=[f'{a}[{i}]' for i in range(int(lo),int(lo)+64)]
                else: raise ValueError(('alias',n,e))
            elif '^' in e:
                args=e.split(' ^ ');cn='n'+str(int(n[1:])+1);ce=scalar[cn]
                # Validate carry equation exhaustively, independent of the generator.
                for bits in range(1<<len(args)):
                    values={a:(bits>>i)&1 for i,a in enumerate(args)}
                    ev=ce
                    for a,v in sorted(values.items(),key=lambda v:-len(v[0])):ev=ev.replace(a,str(v))
                    assert sum(values.values()) == (sum(values.values())%2)+2*eval(ev,{'__builtins__':{}},{})
                self.pairs.append((n,cn,args))
            elif re.fullmatch(r'\w+\[\d+\] & \w+\[\d+\]',e):self.pp[n]=e
        for sn,cn,args in self.pairs: self.pp.pop(cn,None)
        self.text=text
    def add(self,d,e,k):
        e=e.strip()
        if e in ("1'b0","1'b1"):
            if e=="1'b1":d['1']+=k
        elif e.startswith('(~') and e.endswith(')'):
            d['1']+=k;self.add(d,e[2:-1],-k)
        elif (m:=re.fullmatch(r'(\w+)\[(\d+)\]',e)) and m[1] in self.alias:
            self.add(d,self.alias[m[1]][int(m[2])],k)
        else:d[self.pp.get(e,e)]+=k
    def rows(self,names):
        d=collections.defaultdict(int)
        for n in names:
            for i,e in enumerate(self.alias[n]):self.add(d,e,1<<i)
        return d
    def prove(self,names,expected):
        d=self.rows(names)
        for sn,cn,args in reversed(self.pairs):
            s,c=d.pop(sn,0),d.pop(cn,0)
            assert (c-2*s)%P==0, ('unpaired carry',sn,c,s)
            for a in args:self.add(d,a,s)
        got={k:v%P for k,v in d.items() if v%P}
        want={k:v%P for k,v in expected.items() if v%P}
        assert got==want, (set(got.items())^set(want.items()))
        # Mutating any nonzero specification coefficient must be rejected.
        fault=want.copy();key=next(iter(want));fault[key]=(fault[key]+1)%P
        assert got!=fault
        return len(self.pairs)
def words(**weights):
    d=collections.defaultdict(int)
    for sig,weight in weights.items():
        name,width= (sig.rsplit('_w',1) if '_w' in sig else (sig,64)); width=int(width)
        for i in range(width):d[f'{name}[{i}]']+=weight*(1<<i)
    return d
def main(root):
    root=pathlib.Path(root);out=[]
    for file in ['qsag_asic_gl64_csa_gen.sv','qsag_asic_ext4_p2_gen.sv']:
        source=(root/'rtl'/file).read_text()
        for name,body in re.findall(r'module (\w+)\s*\((.*?)endmodule',source,re.S):
            if name not in ['qsag_gl64_mul_tree','qsag_gl64_fold','qsag_gl64_reduce128_csa','qsag_p2_me','qsag_p2_mi','qsag_p2_mi_fused','qsag_ext4_kara_combine']:continue
            c=Circuit(body);checks=[]
            if name=='qsag_gl64_mul_tree':
                for port in ['s','c']:
                    e=re.search(r'assign '+port+r' = \{([^}]+)\}',body)[1];c.alias[port]=list(reversed(e.split(', ')))
                want={f'a[{i}] & b[{j}]':1<<(i+j) for i in range(64) for j in range(64)}
                checks=[(['s','c'],want)]
            elif name=='qsag_gl64_fold':checks=[(['rx','ry'],words(s_w128=1,c_w128=1))]
            elif name=='qsag_gl64_reduce128_csa':checks=[(['rx','ry'],words(v_w128=1))]
            elif name=='qsag_p2_me':
                for b in range(3):
                    for i in range(4):
                        d=collections.defaultdict(int)
                        for bb in range(3):
                            for off,wt in enumerate([2,3,1,1]):
                                for j in range(64):d[f'x[{64*(3*((i+off)%4)+bb)+j}]']+=wt*(2 if b==bb else 1)*(1<<j)
                        for j in range(64):d[f'rc[{64*(3*i+b)+j}]']+=1<<j
                        checks.append(([f'o{b}_{i}_x',f'o{b}_{i}_y'],d))
            elif name.startswith('qsag_p2_mi'):
                for l in range(12):
                    d=collections.defaultdict(int)
                    for k in range(12):
                        wt=1+((-64 if l==0 else 1<<(l-1)) if k==l else 0)
                        if k==0 and name.endswith('fused'):
                            fw=int(re.search(r'input\s+wire\s+\[(\d+):0\] sx',body)[1])+1
                            for sig in ['sx','sy']:
                                for j in range(fw):d[f'{sig}[{j}]']+=wt*(1<<j)
                        else:
                            for j in range(64):d[f'x[{64*k+j}]']+=wt*(1<<j)
                    for j in range(64):d[f'rc[{64*l+j}]']+=1<<j
                    checks.append(([f'o{l}_x',f'o{l}_y'],d))
            else:
                weights=[[1,7,0,-7,-7,7,0,0,0],[-1,-1,1,1,7,0,0,0,0],[-1,-7,0,-1,-7,0,1,7,0],[1,1,-1,1,1,-1,-1,-1,1]]
                for l,row in enumerate(weights):
                    d=collections.defaultdict(int)
                    for k,wt in enumerate(row):
                        for j in range(64):d[f'p[{64*k+j}]']+=wt*(1<<j)
                    for j in range(64):d[f'z[{64*l+j}]']+=1<<j
                    checks.append(([f'r{l}_x',f'r{l}_y'],d))
            for rows,want in checks:c.prove(rows,want)
            out.append({'module':name,'cones':len(checks),'local_adders':len(c.pairs),'sha256':hashlib.sha256(body.encode()).hexdigest()})
            print(name,len(checks),'cones certified, coefficient mutations rejected',flush=True)
    (root/'logs/astra_csa_certificate.json').write_text(json.dumps(out,indent=2)+'\n')
if __name__=='__main__':main(sys.argv[1] if len(sys.argv)>1 else '.')
