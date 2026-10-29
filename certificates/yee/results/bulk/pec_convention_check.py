"""Exact small-box incidence verification of the relative-PEC convention.
This finite test supplements the size-independent combinatorial proof.
"""
from itertools import product
from collections import defaultdict
import json

def check_box(n):
    edges=[]
    for a in range(3):
        axes=[range(n[j]) if j==a else range(1,n[j]) for j in range(3)]
        edges.extend((a,*p) for p in product(*axes))
    lookup={e:i for i,e in enumerate(edges)}
    rows=[];col_counts=[0]*len(edges)
    for a in range(3):
        b=(a+1)%3;c=(a+2)%3
        ranges=[range(n[j]+1) if j==a else range(n[j]) for j in range(3)]
        for p in product(*ranges):
            # Curl_a = D_b E_c - D_c E_b.
            terms=[]
            for cmp,der,sign in [(c,b,1),(b,c,-1)]:
                q=list(p);q[der]+=1;terms.extend([((cmp,*q),sign),((cmp,*p),-sign)])
            row={lookup[e]:s for e,s in terms if e in lookup}
            assert len(row)<=4
            for e in row:col_counts[e]+=1
            rows.append(row)
    assert all(k==4 for k in col_counts)
    gram=defaultdict(int)
    for row in rows:
        for i,x in row.items():
            for j,y in row.items():gram[i,j]+=x*y
    for i,e in enumerate(edges):
        assert gram[i,i]==4
        assert sum(abs(v) for (a,b),v in gram.items() if a==i)<=16
        axis,*point=e
        perps=[j for j in range(3) if j!=axis]
        for offs in product((0,-1),repeat=2):
            cell=list(point)
            for j,off in zip(perps,offs):cell[j]+=off
            assert all(0<=cell[j]<n[j] for j in range(3))
    return {"box":n,"active_E":len(edges),"retained_face_rows":len(rows)}
if __name__=="__main__":
    records=[check_box(n) for n in product(range(2,5),repeat=3)]
    print(json.dumps({"checks":records,"status":"EXACT_FINITE_INCIDENCE_CHECK_PASS"},indent=2))
