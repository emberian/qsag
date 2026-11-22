import gdstk,sys
lib=gdstk.read_gds(sys.argv[1])
for c in lib.cells:
    print("CELL",c.name,c.bounding_box(), "polys",len(c.polygons),"refs",len(c.references))
    for p in c.polygons:
        bb=p.bounding_box()
        print("  L%d/%d n=%d bbox=(%.3f,%.3f)-(%.3f,%.3f) w=%.3f h=%.3f area=%.4f"%(p.layer,p.datatype,len(p.points),bb[0][0],bb[0][1],bb[1][0],bb[1][1],bb[1][0]-bb[0][0],bb[1][1]-bb[0][1],p.area()))
        if len(p.points)>4: print("     pts",[(round(float(x),3),round(float(y),3)) for x,y in p.points])
    for l in c.labels: print("  LABEL",l.text,l.layer,l.texttype,l.origin)
    for r in c.references[:10]: print("  REF",r.cell.name if hasattr(r.cell,"name") else r.cell,r.origin,r.rotation,r.repetition)
