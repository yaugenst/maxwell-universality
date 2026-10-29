# /// script
# requires-python = ">=3.11"
# dependencies = []
# ///
"""Propose exact scalar-expression certificates for the frozen 2056 boxes.

Saved constants are inputs only. Every arithmetic interval is rebuilt from
Fractions and integer square roots, then checked by Lean's kernel.
"""
from __future__ import annotations
from dataclasses import dataclass
from fractions import Fraction as Q
from pathlib import Path
import argparse, hashlib, json, math

ROOT = Path(__file__).resolve().parent
SOURCE = ROOT.parent / 'certificates/yee'
BASE = SOURCE / 'work/bulk/global_certificate'
RECEIPTS = SOURCE / 'recorded-run/artifacts/global_atomic/all_verified_boxes.jsonl'
OUT = ROOT / 'Maxwell/Certificate/GlobalScalar'
BITS = 100
SCALE = 1 << BITS
PI_UPPER = Q(314159265358979323847, 10**20)
SQRT3_UPPER = Q(173205080756887729353, 10**20)


def floor_grid(q):
    return Q((q.numerator*SCALE)//q.denominator, SCALE)


def ceil_grid(q):
    return Q(-((-q.numerator*SCALE)//q.denominator), SCALE)


def sqrt_floor(q):
    assert q >= 0
    return Q(math.isqrt((q.numerator*SCALE*SCALE)//q.denominator), SCALE)


def sqrt_ceil(q):
    a = sqrt_floor(q)
    return a if a*a == q else a+Q(1, SCALE)


def qlean(q):
    q=Q(q)
    return str(q.numerator) if q.denominator == 1 else f'({q.numerator}/{q.denominator})'


@dataclass(frozen=True)
class Node:
    op: str
    args: tuple
    lo: Q
    hi: Q


class Builder:
    def __init__(self):
        self.nodes=[]
        self.cache={}
    def emit(self, op, args, lo, hi):
        n=Node(op,args,lo,hi)
        if n not in self.cache:
            self.cache[n]=len(self.nodes)
            self.nodes.append(n)
        return self.cache[n]
    def rat(self,q):
        q=Q(q)
        return self.emit('rat',(q,),q,q)
    def binary(self,op,a,b):
        x,y=self.nodes[a],self.nodes[b]
        if op=='add': lo,hi=x.lo+y.lo,x.hi+y.hi
        elif op=='sub':lo,hi=x.lo-y.hi,x.hi-y.lo
        elif op=='mul':
            v=[x.lo*y.lo,x.lo*y.hi,x.hi*y.lo,x.hi*y.hi]
            lo,hi=min(v),max(v)
        else:raise ValueError(op)
        return self.emit(op,(a,b),floor_grid(lo),ceil_grid(hi))
    def inv(self,a):
        x=self.nodes[a]
        assert x.lo>0, (a,x)
        return self.emit('inv',(a,),floor_grid(1/x.hi),ceil_grid(1/x.lo))
    def sqrt(self,a):
        x=self.nodes[a]
        assert x.lo>=0,(a,x)
        return self.emit('sqrt',(a,),sqrt_floor(x.lo),sqrt_ceil(x.hi))
    def add(self,a,b):return self.binary('add',a,b)
    def sub(self,a,b):return self.binary('sub',a,b)
    def mul(self,a,b):return self.binary('mul',a,b)
    def div(self,a,b):return self.mul(a,self.inv(b))
    def sq(self,a):return self.mul(a,a)


def proposal(record):
    c=record['verified_constants']
    h=Q(record['halfwidth'])
    return dict(center=[Q(x) for x in record['center']], witness=record['witness'],
        lowCount=c['nl'],half=h,s=ceil_grid(PI_UPPER/10*(SQRT3_UPPER*h)),
        r=Q(c['rmin']),rh=Q(c['rhmin']),R=sqrt_ceil(Q(c['cutoff'])),cutoff=Q(c['cutoff']),
        fn=[Q(x) for x in c['fn'][:2]],en=[Q(x) for x in c['en'][:2]],
        kn=[[Q(x) for x in row] for row in c['kn'][:2]],crossder=[Q(x) for x in c['crossder']],
        rhow=[[Q(x) for x in row] for row in c['rhow'][1:3]],wn=Q(c['wn']),wp2=Q(c['wp2']),
        qfn=Q(c['qfn'][1]),qw=Q(c['qweighted'][1]),rzero=Q(c['rzero'][1]))


def expressions(p, *, sigma=Q(1, 2**24), rho=Q(13)):
    b=Builder(); r=b.rat;add=b.add;sub=b.sub;mul=b.mul;div=b.div;sq=b.sq;sqrt=b.sqrt
    def dot(v):return add(add(mul(r(p['half']),r(v[0])),mul(r(p['half']),r(v[1]))),mul(r(p['half']),r(v[2])))
    s=r(p['s']);rh=r(p['rh']);rl=r(p['r']);R=r(p['R']);t=r(Q(1,64));sigma=r(sigma)
    fn=[r(x) for x in p['fn']];en=[r(x) for x in p['en']]
    lossn=add(add(add(dot(p['kn'][0]),mul(sq(s),add(mul(fn[0],en[0]),sq(fn[0])))),
        div(mul(mul(mul(r(2),t),sq(s)),r(p['wn'])),sq(sub(r(1),div(s,rl))))),mul(sigma,sq(fn[0])))
    lossp=add(add(dot(p['kn'][1]),mul(sq(s),add(mul(fn[1],en[1]),sq(fn[1])))),mul(sigma,sq(fn[1])))
    lossg=add(div(mul(r(2),sq(s)),sq(rl)),mul(r(64),sigma))
    cp=add(div(add(r(3),div(s,rl)),sq(sub(r(1),div(s,rl)))),div(mul(r(Q(1,2)),R),sub(r(1),div(s,rl))))
    cross=add(dot(p['crossder']),mul(sq(s),add(mul(r(8),add(div(en[1],r(2)),fn[1])),mul(mul(mul(r(16),t),cp),r(p['wp2'])))))
    base=sub(div(sq(rh),r(rho)),t)
    shift=sub(sub(div(sq(sub(rh,s)),r(rho)),t),sigma)
    wmax=b.inv(sqrt(base));curlmax=div(rh,sqrt(base));chi=sqrt(div(base,shift))
    projcoef=div(add(add(div(rh,r(2)),r(3)),div(s,rh)),sq(sub(rh,s)))
    rp=mul(chi,add(add(add(mul(wmax,r(p['rzero'])),dot(p['rhow'][0])),
        mul(sq(s),add(add(div(mul(wmax,en[1]),r(2)),mul(add(div(curlmax,r(2)),wmax),fn[1])),
            mul(mul(mul(mul(r(2),t),wmax),projcoef),r(p['qfn']))))),mul(sigma,r(p['qw']))))
    rg=mul(chi,add(dot(p['rhow'][1]),mul(sq(s),mul(add(div(curlmax,r(2)),wmax),r(8)))))
    etap=add(sq(rp),div(mul(mul(add(t,sigma),sq(s)),sq(r(p['qfn']))),sq(sub(rh,s))))
    etag=sq(rg)
    negative=sub(r(Q(1023,1024)),lossn)
    positive=sub(sub(r(Q(1023,1024)),lossp),etap)
    gradient=sub(sub(r(1),lossg),etag)
    determinant=sub(mul(positive,gradient),sq(add(cross,sqrt(mul(etap,etag)))))
    roots=dict(negative=negative,positive=positive,gradient=gradient,determinant=determinant,
        smallLow=sub(rl,s),smallHigh=sub(rh,s),base=base,shift=shift)
    for key,n in roots.items(): assert b.nodes[n].lo>0,(p['witness'],key,b.nodes[n])
    return b,roots


def vector(vals):return '!['+', '.join(qlean(x) for x in vals)+']'

def lean_proposal(p):
    lines=[]
    for k,v in p.items():
        if k in ('center','witness','lowCount'):
            continue
        if k in ('center','fn','en','crossder'):value=vector(v)
        elif k in ('kn','rhow'):value='!['+', '.join(vector(row) for row in v)+']'
        elif k=='witness':value=json.dumps(v)
        elif k=='lowCount':value=str(v)
        else:value=qlean(v)
        lines.append(f'  {k} := {value}')
    return '{\n'+'\n'.join(lines)+'\n}'


def record_text(index,p,b,roots, *, checked_record=True):
    prefix=f'n{index:04d}_'
    lines=[f'def proposal{index:04d} : Proposal := '+lean_proposal(p),'']
    for j,n in enumerate(b.nodes):
        if n.op=='rat':rhs=f'.rat {qlean(n.args[0])}'
        else:
            args=' '.join(prefix+str(k) for k in n.args)
            rhs=f'.{n.op} {args} (enclosure {qlean(n.lo)} {qlean(n.hi)})'
        lines.append(f'private def {prefix}{j} : ScalarExpression.Certificate := {rhs}')
    lines.extend(['',f'def evidence{index:04d} : Evidence where'])
    lines.extend(f'  {key} := {prefix}{j}' for key,j in roots.items())
    lines.extend(['',f'theorem checked{index:04d} : accepts proposal{index:04d} evidence{index:04d} = true := by decide +kernel',''])
    if checked_record:
        lines.extend([f'def record{index:04d} : VerifiedProposal := ⟨proposal{index:04d}, evidence{index:04d}, checked{index:04d}⟩',''])
    return '\n'.join(lines)


def main():
    ap=argparse.ArgumentParser();ap.add_argument('--start',type=int,default=0);ap.add_argument('--count',type=int,default=2056);ap.add_argument('--batch-size',type=int,default=8)
    args=ap.parse_args();OUT.mkdir(exist_ok=True)
    canonical=json.loads((BASE/'cover_proposals.json').read_text())['accepted']
    receipts={r['witness']:r for r in map(json.loads,RECEIPTS.read_text().splitlines())}
    assert len(canonical)==len(receipts)==2056
    manifest=[];batches={};margins={k:None for k in ['negative','positive','gradient','determinant']}
    for index in range(args.start,min(args.start+args.count,2056)):
        original=canonical[index];record=receipts[original['witness']]
        assert original['center']==record['center'] and original['halfwidth']==record['halfwidth']
        p=proposal(record);b,roots=expressions(p);source=record_text(index,p,b,roots)
        batches.setdefault(index//args.batch_size,[]).append(source)
        for k in margins:
            lo=b.nodes[roots[k]].lo
            margins[k]=lo if margins[k] is None else min(margins[k],lo)
        manifest.append(dict(index=index,witness=p['witness'],nodes=len(b.nodes),
            record_sha256=hashlib.sha256(source.encode()).hexdigest(),
            s=str(p['s']),R=str(p['R']),rzero=str(p['rzero'])))
    output_hashes={}
    for batch,records in batches.items():
        path=OUT/f'Batch{batch:03d}.lean'
        text='import Maxwell.Certificate.GlobalScalarCore\n\nnamespace Maxwell.Certificate.GlobalScalar.Frozen\n\nopen ScalarExpression\nset_option maxRecDepth 100000\nset_option maxHeartbeats 0\n\n'+'\n'.join(records)+'\nend Maxwell.Certificate.GlobalScalar.Frozen\n'
        path.write_text(text)
        output_hashes[str(path.relative_to(ROOT))]=hashlib.sha256(text.encode()).hexdigest()
    m=dict(outputs=output_hashes,precision=BITS,records=manifest,minimum_lower_margins={k:str(v) for k,v in margins.items()},
        inputs={str(p):hashlib.sha256(p.read_bytes()).hexdigest() for p in [BASE/'cover_proposals.json',RECEIPTS]},
        status='untrusted scalar proposals; Lean acceptance required')
    target=ROOT/'evidence'/f'global_scalar_proposals_{args.start:04d}_{len(manifest):04d}.json'
    target.write_text(json.dumps(m,indent=2)+'\n')
    print(json.dumps(dict(records=len(manifest),nodes=sum(x['nodes'] for x in manifest),minimum_lower_margins=m['minimum_lower_margins'])))

if __name__=='__main__':main()
