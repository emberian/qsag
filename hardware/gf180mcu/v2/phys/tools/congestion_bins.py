import re,collections,sys
b=collections.Counter(); n=0; ov=None
for l in open(sys.argv[1]):
    m=re.search(r"overflow:(\d+)",l)
    if m: ov=int(m.group(1))
    m=re.search(r"bbox = \(([\d.]+), ([\d.]+)\)",l)
    if m:
        x,y=float(m.group(1)),float(m.group(2)); b[(int(x//100)*100,int(y//100)*100)]+=ov or 1; n+=1
print("violating gcells",n,"total overflow",sum(b.values()))
xs=sorted({k[0] for k in b}); ys=sorted({k[1] for k in b})
print("y\\x  "+" ".join("%5d"%x for x in xs))
for y in reversed(ys): print("%5d"%y+" "+" ".join("%5d"%b.get((x,y),0) for x in xs))
