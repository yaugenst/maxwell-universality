"""Exact rational-endpoint interval verifier for one Bloch box.
The file uses float data ONLY as proposed witnesses and proposed bounds.
All accept/reject tests use fixed-point interval arithmetic.
"""
from __future__ import annotations
import json,time,sys
from pathlib import Path
import numpy as np
from fractions import Fraction as F
import interval_tools as v
from interval_tools import I,PI,S,cb
from exact_geometry import diamond_cells_exact
BASE=Path(__file__).parent
_CELLS=diamond_cells_exact(20,12,1).astype(np.int32)
_DEN=[]
for _axis in range(3):
    _a,_b=[_i for _i in range(3) if _i!=_axis]
    _DEN.append(_CELLS+np.roll(_CELLS,1,_a)+np.roll(_CELLS,1,_b)+np.roll(np.roll(_CELLS,1,_a),1,_b))
DEN=np.ascontiguousarray(np.stack(_DEN,axis=-1)[:,:10,:10].reshape(2000,3))
assert set(DEN.ravel().tolist()) <= {4,15,26,37,48}
T=I(F(1,64));SIG=I(F(1,2**24));P0=I(1)-I(F(1,2**10))

def sl(a,cols):return np.ascontiguousarray(a[:,:,cols,:])
def ms(a,cols):return np.ascontiguousarray(a[cols][:,cols])
def highonly(a,low):a=a.copy();a[low]=0;return a

def lap_tests(lap,low,c):
    mask=np.ones(2000,bool);mask[low]=False
    r=I(c['rmin'])**2;rh=I(c['rhmin'])**2;cut=I(c['cutoff'])
    for j in range(2000):
        lo=int(lap[j,0])-int(lap[j,2]);hi=int(lap[j,0])+int(lap[j,2])
        assert lo*v.T>=r.hi*S,('lap_min',j)
        if mask[j]:assert lo*v.T>=rh.hi*S,('high_lap_min',j)
        else:assert hi*v.T<=cut.lo*S,('low_lap_max',j)
    return mask

def verify_scalar(c,half):
    h=[I(half)]*3;s=(2*PI/20)*(sum(x*x for x in h)).sqrt();s2=s*s
    fn=list(map(I,c['fn']));en=list(map(I,c['en']));qfn=list(map(I,c['qfn']));qw=list(map(I,c['qweighted']))
    r=I(c['rmin']);rh=I(c['rhmin'])
    dot=lambda a:sum(h[j]*I(a[j]) for j in range(3))
    assert (r-s).lo>0 and (rh-s).lo>0
    base=rh*rh/14-T;shift=(rh-s)**2/14-T-SIG
    assert base.lo>0 and shift.lo>0 and (T-SIG).lo>0
    lossn=dot(c['kn'][0])+s2*(fn[0]*en[0]+fn[0]**2)+2*T*s2*I(c['wn'])/(1-s/r)**2+SIG*fn[0]**2
    lossp=dot(c['kn'][1])+s2*(fn[1]*en[1]+fn[1]**2)+SIG*fn[1]**2
    lossg=2*s2/(r*r)+64*SIG
    ratio=1-s/r
    cp=(3+s/r)/ratio**2+I(F(1,2))*I(c['cutoff']).sqrt()/ratio
    cross=dot(c['crossder'])+s2*(8*(I(F(1,2))*en[1]+fn[1])+16*T*cp*I(c['wp2']))
    chi=(base/shift).sqrt();wmax=1/base.sqrt();curlmax=rh*wmax
    projcoef=(I(F(1,2))*rh+3+s/rh)/(rh-s)**2
    et=[]
    for j in [1,2]:
        rem=I(F(1,2))*wmax*en[j]+(I(F(1,2))*curlmax+wmax)*fn[j]
        if j==1:rem+=2*T*wmax*projcoef*qfn[j]
        rw=chi*(wmax*I(c['rzero'][j])+dot(c['rhow'][j])+s2*rem+SIG*qw[j])
        et.append(rw*rw+(T+SIG)*s2*qfn[j]**2/(rh-s)**2)
    p=P0-lossp-et[0];g=1-lossg-et[1];e=cross+(et[0]*et[1]).sqrt()
    determinant=p*g-e*e
    assert (P0-lossn).lo>0,('negative_block',lossn.decimals())
    assert p.lo>0 and g.lo>0 and determinant.lo>0,('positive_block',p.decimals(),g.decimals(),determinant.decimals())
    return {'negative_margin':(P0-lossn).bounds(),'positive_diagonal_margin':p.bounds(),
            'gradient_margin':g.bounds(),'positive_determinant_margin':determinant.bounds()}

def verify_record(rec,verbose=False):
    start=time.monotonic();c=json.loads(json.dumps(rec['constants']));lowfile=np.load(BASE/'witnesses'/rec['witness'])
    center=rec['center'];half=rec['halfwidth'];low=np.ascontiguousarray(lowfile['low'],dtype=np.int32)
    assert list(lowfile['center'])==center and float(lowfile['halfwidth'])==half
    raw=np.concatenate([lowfile['F'],lowfile['Fpos']],axis=2).astype(np.complex128)
    d=v.make_d(center);lap=v.laplacian(d);mask=lap_tests(lap,low,c)
    field=v.project(v.witness(raw),d);m=field.shape[2];assert m==2*len(low)
    nneg=int(rec["negative_count"]);assert 1<=nneg<m
    neg=slice(0,nneg);pos=slice(nneg,m)
    # Low-coordinate change of basis is complete: full rank on the transverse subspace.
    assert v.psd(v.gram(np.ascontiguousarray(field[low]),power=20)),'low_basis_rank'
    g=v.gradient(d,low)
    ef=v.curl(d,field,True)
    weighted_ef=v.fft(v.material(v.fft(ef,True),DEN))
    bf=v.curl(d,weighted_ef);af=v.add(bf,v.rat(field,1,64),True)
    lc=v.gram(field,af)
    assert v.psd(v.shifted_identity(ms(lc,neg),-P0,-1)),'central_negative'
    assert v.psd(v.shifted_identity(ms(lc,pos),-P0,1)),'central_positive'
    for j,sel in enumerate([neg,pos]):
        assert v.normcheck(sl(field,sel),c['fn'][j]),('F_norm',j)
        assert v.normcheck(sl(ef,sel),c['en'][j]),('curl_F_norm',j)
        
        while not v.normcheck(sl(highonly(af,low),sel),c['rzero'][j]):
            c['rzero'][j]*=2
            assert c['rzero'][j]<=F(1,128),('central_residual',j,c['rzero'][j])
        if verbose:print('VERIFIED_CENTRAL_RESIDUAL_BOUND',j,c['rzero'][j],flush=True)
        assert v.normcheck(sl(highonly(field,low),sel),c['qfn'][j]),('high_F_norm',j)
    assert I(c['fn'][2]).lo>=8*v.T
    assert I(c['en'][2]).lo>=0
    w=v.invweights(lap,0)
    assert v.normcheck(v.weight(sl(field,neg),w),c['wn'],squared=True),'weighted_negative'
    wl=v.invweights(lap,1,(~mask).astype(np.int32))
    assert v.normcheck(v.weight(sl(field,pos),wl),c['wp2']),'low_weighted_positive'
    wh=v.invweights(lap,2,mask.astype(np.int32))
    for j,sel in enumerate([neg,pos]):
        assert v.normcheck(v.weight(sl(field,sel),wh),c['qweighted'][j]),('high_weighted_F',j)
    theta=cb(0,2*PI/20)
    for axis in range(3):
        dp=np.zeros_like(d);plus=np.ascontiguousarray(d[:,axis,:].copy());plus[:,0]+=S
        dp[:,axis,:]=v.mul(plus,np.broadcast_to(theta,plus.shape));dp=np.ascontiguousarray(dp)
        ep=v.curl(dp,field,True)
        ewp=v.fft(v.material(v.fft(ep,True),DEN))
        db=v.add(v.curl(dp,weighted_ef),v.curl(d,ewp))
        da=v.add(db,v.rat(v.pprime(d,dp,field),1,32))
        kd=v.gram(field,db)
        for j,sel in enumerate([neg,pos]):
            assert v.hnormcheck(ms(kd,sel),c['kn'][j][axis]),('compression_derivative',j,axis)
            ah=v.weight(sl(highonly(da,low),sel),wh)
            assert v.normcheck(ah,c['rhow'][j][axis]),('weighted_residual_derivative',j,axis)
        egp=v.curl(dp,g,True)
        bgp=v.curl(d,v.fft(v.material(v.fft(egp,True),DEN)))
        assert v.normcheck(v.weight(highonly(bgp,low),wh),c['rhow'][2][axis]),('gradient_residual_derivative',axis)
        gp=v.gprime_raw(d,dp,low)
        kg=v.gram(sl(field,pos),v.add(bgp,v.rat(gp,1,32)))
        assert v.normcheck(kg,c['crossder'][axis]),('cross_derivative',axis)
        if verbose:print('VERIFIED_AXIS',axis,flush=True)
    scalar=verify_scalar(c,half)
    return {'center':center,'halfwidth':half,'witness':rec['witness'],'status':'INTERVAL_PASS',
            'seconds':time.monotonic()-start,'verified_constants':c,'margins':scalar,'frequency_halfwidth':str(F(SIG.lo,v.T)),'negative_count':nneg}

if __name__=='__main__':
    records=[json.loads(l) for l in open(BASE/'cover_screen.jsonl')]
    rec=next(x for x in records if x['result']['pass'])
    if len(sys.argv)>1:rec=[x for x in records if x['result']['pass']][int(sys.argv[1])]
    print('VERIFY_START',rec['center'],rec['halfwidth'],flush=True)
    print(json.dumps(verify_record(rec,True),indent=2),flush=True)
