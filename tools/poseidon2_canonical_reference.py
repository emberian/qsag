"""Independent dense-matrix arithmetic reference for the QSAG canonical profile.
No Rust/Lean build; the resulting vectors are checked by both implementations.
"""
P=2**64-2**32+1
IV=0x504f53325f474c31
MASK=2**64-1
M4=[[2,3,1,1],[1,2,3,1],[1,1,2,3],[3,1,1,2]]
ME=[[M4[i//3][j//3]*(1+(i%3==j%3)) for j in range(12)] for i in range(12)]
MI=[[1+((-64 if i==0 else 2**(i-1)) if i==j else 0) for j in range(12)] for i in range(12)]
def mv(m,x): return [sum(a*b for a,b in zip(row,x))%P for row in m]
def inv(m):
 a=[[v%P for v in row]+[int(i==j) for j in range(12)] for i,row in enumerate(m)]
 for i in range(12):
  k=next(k for k in range(i,12) if a[k][i]);a[i],a[k]=a[k],a[i]
  d=pow(a[i][i],-1,P);a[i]=[v*d%P for v in a[i]]
  for k in range(12):
   if k!=i:
    d=a[k][i];a[k]=[(v-d*w)%P for v,w in zip(a[k],a[i])]
 return [r[12:] for r in a]
def mix(x):
 x=(x+0x9e3779b97f4a7c15)&MASK;x=((x^(x>>30))*0xbf58476d1ce4e5b9)&MASK;x=((x^(x>>27))*0x94d049bb133111eb)&MASK;return x^(x>>31)
def rc(t,r,i):return mix(mix(mix(IV^t)^r)^i)%P
def perm(x):
 x=mv(ME,x)
 for t,n in [(0,4),(1,22),(2,4)]:
  for r in range(n):
   if t==1:x[0]=pow((x[0]+rc(t,r,0))%P,7,P);x=mv(MI,x)
   else:x=mv(ME,[pow((v+rc(t,r,i))%P,7,P) for i,v in enumerate(x)])
 return x
def perm_inv(x):
 e=pow(7,-1,P-1);ei=inv(ME);ii=inv(MI)
 for t,n in [(2,4),(1,22),(0,4)]:
  for r in reversed(range(n)):
   if t==1:x=mv(ii,x);x[0]=(pow(x[0],e,P)-rc(t,r,0))%P
   else:x=[(pow(v,e,P)-rc(t,r,i))%P for i,v in enumerate(mv(ei,x))]
 return mv(ei,x)
def hash32(msg):
 msg=msg+b'\x01';msg+=b'\0'*((-len(msg))%7)
 limbs=[int.from_bytes(msg[i:i+7],'big') for i in range(0,len(msg),7)]
 z=(8-(len(limbs)+1)%8)%8
 limbs+=([2**56+1] if z==0 else [1]+[0]*(z-1)+[2**56])
 x=[0]*8+[8,4,32,IV]
 for i in range(0,len(limbs),8):x=perm([(x[j]+limbs[i+j])%P for j in range(8)]+x[8:])
 return b''.join(v.to_bytes(8,'big') for v in x[:4])
def compress(x):return [(v+x[i]+2*x[i+4]+4*x[i+8])%P for i,v in enumerate(perm(x)[:4])]
if __name__=='__main__':
 import json
 print(json.dumps({'zero':perm([0]*12),'seq':perm(list(range(12))),'empty':hash32(b'').hex(),'compress_seq':compress(list(range(12)))},indent=2))
