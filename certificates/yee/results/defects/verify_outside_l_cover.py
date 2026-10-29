"""Independent exact geometry audit for the shifted outside-L Bloch cover.

This program uses rational polytope vertices, not the pilot's greedy
feasibility implementation. Pending/uncovered leaves always prevent PASS.
Matrix receipts are checked for consistency and current hashes, but do not
constitute a fresh matrix replay. Use --replay-matrices for that final gate.
"""
from pathlib import Path
from fractions import Fraction as F
from itertools import product,combinations
from functools import lru_cache
from collections import Counter
import json,hashlib,argparse,sys,subprocess,os,time,uuid

if not __debug__:
    raise RuntimeError('Exact acceptance requires assertions; do not run with -O or PYTHONOPTIMIZE.')

ROOT=Path(__file__).resolve().parents[2]
SHIFT=F(157,16384);SIGMA=F(1,1<<24);RHO=F(1023,1<<26)
WEDGE_ROWS=[(1,0,0),(-1,0,0),(0,1,0),(0,-1,0),(0,0,1),(0,0,-1),(-1,1,0),(0,-1,1),(1,1,1)]
MATRIX_CORE_SOURCES={'interval_kernel.cpp','interval_tools.py','verify_point.py','exact_geometry.py'}
MATRIX_SOURCE_SETS=(MATRIX_CORE_SOURCES|{'verify_pilot_batch.py'},MATRIX_CORE_SOURCES|{'verify_global.py','verify_cover.py'})
MATRIX_MARGINS={'negative_margin','positive_diagonal_margin','gradient_margin','positive_determinant_margin'}
NORM_PARAMETERS=('fn','en','kn','rhow','crossder','wn','wp2','qfn','qweighted','rmin','rhmin','rzero','cutoff')

def det(a):
    return a[0][0]*(a[1][1]*a[2][2]-a[1][2]*a[2][1])-a[0][1]*(a[1][0]*a[2][2]-a[1][2]*a[2][0])+a[0][2]*(a[1][0]*a[2][1]-a[1][1]*a[2][0])

VERTICES=[]
for chosen in combinations(range(9),3):
    a=[WEDGE_ROWS[i] for i in chosen];d=det(a)
    if not d:continue
    # Explicit 2x2 cofactors are simpler and independently check the inverse.
    cofactor=[]
    for i in range(3):
        row=[]
        for j in range(3):
            rr=[r for r in range(3) if r!=i];cc=[c for c in range(3) if c!=j]
            row.append((-1)**(i+j)*(a[rr[0]][cc[0]]*a[rr[1]][cc[1]]-a[rr[0]][cc[1]]*a[rr[1]][cc[0]]))
        cofactor.append(row)
    adj=[[cofactor[j][i] for j in range(3)] for i in range(3)]
    assert all(sum(a[i][k]*adj[k][j] for k in range(3))==d*(i==j) for i in range(3) for j in range(3))
    if d<0:d=-d;adj=[[-x for x in row] for row in adj]
    VERTICES.append((chosen,d,adj))

def key_from_box(center,halfwidth,depth):
    assert isinstance(depth,int) and 0<=depth<=30
    h=F(halfwidth);assert h==F(1,1<<(depth+1))
    index=[]
    for c in center:
        z=(F(c)-h)*(1<<depth)
        assert z.denominator==1 and 0<=z<1<<depth
        index.append(int(z))
    assert len(index)==3
    return depth,tuple(index)

def endpoints(key):
    d,idx=key;s=1<<d
    return tuple(F(i,s) for i in idx),tuple(F(i+1,s) for i in idx)

@lru_cache(None)
def feasible(key):
    depth,idx=key
    # Scale coordinates by 2^(depth+1), making all nine RHS values integers.
    lo=tuple(2*i for i in idx);hi=tuple(x+2 for x in lo)
    bounds=[hi[0],-lo[0],hi[1],-lo[1],hi[2],-lo[2],0,0,3*(1<<depth)]
    for chosen,d,adj in VERTICES:
        rhs=[bounds[i] for i in chosen]
        numerator=[sum(a*b for a,b in zip(row,rhs)) for row in adj]
        if all(sum(a*x for a,x in zip(row,numerator))<=bound*d for row,bound in zip(WEDGE_ROWS,bounds)):
            return True
    return False

def in_gamma(key):return max(endpoints(key)[1])<=F(1,8)
def in_l_ball(key):
    lo,hi=endpoints(key)
    return sum(max((a-F(1,2))**2,(b-F(1,2))**2) for a,b in zip(lo,hi))<=F(1,400)

def analytic_gamma():
    signed_l=set(product([-1,1],repeat=3));classes=[]
    while signed_l:
        center=min(signed_l)
        equivalent={p for p in signed_l if len({((p[j]-center[j])//2)%2 for j in range(3)})==1}
        assert equivalent=={center,tuple(-x for x in center)}
        classes.append(sorted(equivalent));signed_l-=equivalent
    assert len(classes)==4
    primitive_columns=[[20,10,10],[0,10,0],[0,0,10]]
    assert det(primitive_columns)==2000 and 20**3//det(primitive_columns)==4
    labeled_L=[('L+++',(1,1,1),(1,1,1)),('L++-',(1,1,-1),(1,1,0)),
               ('L+-+',(1,-1,1),(1,0,1)),('L-++',(-1,1,1),(1,0,0))]
    class_ids=[]
    for label,p,expected_character in labeled_L:
        character=(p[0]%2,((p[0]+p[1])//2)%2,((p[0]+p[2])//2)%2)
        assert character==expected_character
        class_id=next(i for i,c in enumerate(classes) if p in c)
        class_ids.append(class_id)
    assert len(set(class_ids))==4
    def atan(q):
        s=sum(F((-1)**j,(2*j+1)*q**(2*j+1)) for j in range(8))
        tail=F(1,17*q**17)
        return s,s+tail
    a,b=atan(5);c,d=atan(239)
    pi_lo=16*a-4*d;pi_hi=16*b-4*c
    assert F(3)<pi_lo<pi_hi<F(22,7)
    x0=pi_hi/160;x1=7*pi_lo/160;x2=15*pi_lo/160
    assert 0<x0<x1<x2<F(1,2)
    # sin(x)<=x; sin(x)>=x-x^3/6 on this interval. The latter polynomial
    # is increasing here, so evaluating it at a lower angle is safe.
    low=12*x0*x0
    high_odd=12*(x1-x1**3/6)**2
    high_even=4*(x2-x2**3/6)**2
    t=F(1,64)
    margins={'low':t-SIGMA-low,'high_odd':high_odd-13*(t+SIGMA),'high_even':high_even-13*(t+SIGMA)}
    assert all(v>0 for v in margins.values())
    assert F(12)+64*SHIFT<13 and RHO<F(1,4096)
    threshold=SHIFT+SIGMA-RHO
    assert threshold==F(642053,1<<26)
    # The separate fresh exact point checker proves this named rational bound;
    # no saved acceptance JSON is read as evidence here.
    upper=F(23913,2500000)
    assert threshold-upper>F(1,500000)
    return {'gamma_margins_exact':{k:str(v) for k,v in margins.items()},
            'four_inequivalent_L_classes_in_doubled_coordinates':classes,
            'L_labels_and_primitive_characters':[{'label':l,'doubled_cartesian':p,'primitive_k_twice_mod2':k} for l,p,k in labeled_L],
            'primitive_cell_count':2000,'conventional_folding_index':4,
            'symmetry_dependency':'fresh original-material integer geometry check certifies all48 signed-coordinate-permutation actions; the uniform comparator shift preserves them',
            'perturbed_positive_band_threshold':str(threshold),
            'threshold_above_lowest_L_upper_interval_by_more_than':'1/500000',
            'point_interval_dependency':'fresh exact point residual/inertia verification certifies E_L++- <23913/2500000; required separately'}

def sha(path):return hashlib.sha256(path.read_bytes()).hexdigest()

def record_sha(record):
    return hashlib.sha256(json.dumps(record,sort_keys=True,separators=(',',':'),allow_nan=False).encode()).hexdigest()

def atomic_json(path,value):
    path.parent.mkdir(parents=True,exist_ok=True)
    payload=(json.dumps(value,indent=2,sort_keys=True)+'\n').encode()
    temporary=path.with_name(path.name+'.tmp-'+uuid.uuid4().hex)
    with temporary.open('xb') as stream:
        stream.write(payload);stream.flush();os.fsync(stream.fileno())
    os.replace(temporary,path)
    assert path.read_bytes()==payload,'Atomic output readback failed'

def safe_witness(name):
    assert isinstance(name,str) and name not in ('','.','..')
    assert Path(name).name==name and '/' not in name and '\\' not in name
    assert name.endswith('.npz')
    return name

def witness_metadata(record,matrix_dir):
    # The fresh matrix driver also checks every F/Fpos value. Here the
    # independent link audit reads only the small exact box and index arrays.
    import numpy as np
    name=safe_witness(record['witness']);path=matrix_dir/'witnesses'/name
    with np.load(path,allow_pickle=False) as w:
        low=w['low'];center=w['center'];half=w['halfwidth']
        assert low.ndim==1 and len(low)>=1 and np.issubdtype(low.dtype,np.integer)
        assert len(set(low.tolist()))==len(low) and np.all(low>=0) and np.all(low<2000)
        assert center.shape==(3,) and np.isfinite(center).all()
        assert half.shape==() and np.isfinite(half)
        assert tuple(F(float(x)) for x in center)==tuple(map(F,record['center']))
        assert F(float(half))==F(record['halfwidth'])
    return path

def norm_parameter_signs(constants):
    # Norm acceptance routines may square their proposed bounds. Their
    # mathematical interpretation therefore requires nonnegative inputs.
    def flatten(value):
        if isinstance(value,list):
            for entry in value:yield from flatten(entry)
        else:yield F(value)
    count=0
    for field in NORM_PARAMETERS:
        values=list(flatten(constants[field]));assert values
        assert all(value>=0 for value in values),('negative norm parameter',field)
        if field in ('fn','rmin','rhmin'):
            assert all(value>0 for value in values),('nonpositive norm/radius parameter',field)
        count+=len(values)
    return count

def verified_constants_are_allowed(proposal,checked):
    # verify_record is allowed only to double its proposed two central
    # residual bounds until the exact interval test passes. It recomputes
    # all resulting scalar margins using those enlarged bounds.
    old=proposal['rzero'];new=checked['rzero']
    assert isinstance(old,list) and isinstance(new,list) and len(old)==len(new)==3
    expected=json.loads(json.dumps(proposal));expected['rzero']=new
    assert expected==checked,'Unexpected changed matrix constants'
    assert F(new[2])==F(old[2])
    for a,b in zip(old[:2],new[:2]):
        a=F(a);b=F(b)
        assert 0<=a<=b
        if a==b:continue
        assert a>0 and b<=F(1,128)
        ratio=b/a
        assert ratio.denominator==1 and ratio.numerator>0
        n=ratio.numerator;assert n&(n-1)==0,'Residual enlargement is not a power of two'

def matrix_receipt(record,matrix_dir,receipts_dir,proposal_hash,source_snapshot):
    name=safe_witness(record['witness']);path=receipts_dir/(name+'.json')
    if not path.exists():return False,'missing',None
    receipt_before=sha(path);r=json.loads(path.read_text())
    if r.get('status')!='INTERVAL_PASS':return False,'not accepted',None
    assert key_from_box(r['center'],r['halfwidth'],r['depth'])==key_from_box(record['center'],record['halfwidth'],record['depth'])
    verified_constants_are_allowed(record['constants'],r['verified_constants'])
    assert F(r['electric_uniform_shift'])==SHIFT and F(r['cell_shift'])==64*SHIFT
    assert F(r['frequency_halfwidth'])==SIGMA and r['negative_count']==2 and r['kernel_fractional_bits']==48
    assert set(r['source_sha256']) in MATRIX_SOURCE_SETS and set(r['margins'])==MATRIX_MARGINS
    assert r['witness']==name
    canonical='verify_global.py' in r['source_sha256']
    if canonical:
        assert r['fresh_matrix_check'] is True
        assert r['proposal_sha256']==proposal_hash
        assert r['record_sha256']==record_sha(record)
    witness_path=matrix_dir/'witnesses'/name;witness_before=sha(witness_path)
    assert witness_metadata(record,matrix_dir)==witness_path
    if witness_before!=r['witness_sha256']:return False,'stale witness',None
    if canonical:
        assert r['witness_before_sha256']==witness_before and r['witness_after_sha256']==witness_before
    for source,digest in r['source_sha256'].items():
        if source not in source_snapshot:
            source_snapshot[source]=sha(matrix_dir/source)
        if source_snapshot[source]!=digest:return False,'stale source',None
    assert all(len(bounds)==2 and F(bounds[1])>=F(bounds[0])>0 for bounds in r['margins'].values())
    assert sha(path)==receipt_before,'Receipt changed during audit'
    assert sha(witness_path)==witness_before,'Witness changed during audit'
    return True,'current',{'receipt_sha256':receipt_before,'witness_sha256':witness_before,
                           'record_sha256':record_sha(record),'canonical_receipt':canonical}

def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--proposal',type=Path,default=ROOT/'work/bulk/global_certificate/cover_proposals.json')
    parser.add_argument('--matrix-dir',type=Path,default=ROOT/'work/bulk/global_certificate')
    parser.add_argument('--output',type=Path,default=ROOT/'results/defects/outside_l_cover_audit.json')
    parser.add_argument('--replay-matrices',action='store_true')
    parser.add_argument('--receipts-dir',type=Path)
    parser.add_argument('--require-current-receipts',action='store_true')
    parser.add_argument('--workers',type=int,default=6)
    args=parser.parse_args()
    assert args.workers>=1
    started=time.monotonic()
    args.receipts_dir=args.receipts_dir or (args.matrix_dir/'verification_final'/'accepted_points' if (args.matrix_dir/'verify_global.py').is_file() else args.matrix_dir/'accepted_points')
    atomic_json(args.output,{'status':'RUNNING','matrix_replayed_this_run':False})
    proposal_bytes=args.proposal.read_bytes()
    proposal_hash=hashlib.sha256(proposal_bytes).hexdigest()
    data=json.loads(proposal_bytes)
    assert F(data['uniform_shift'])==SHIFT and F(data['frequency_halfwidth'])==SIGMA
    assert F(data['L_ball_radius'])==F(1,20) and F(data['gamma_cube_radius'])==F(1,8)
    leaves={};records={};witness_names=set();sign_checks=0
    for r in data['accepted']:
        name=safe_witness(r['witness']);assert name not in witness_names;witness_names.add(name)
        sign_checks+=norm_parameter_signs(r['constants'])
        k=key_from_box(r['center'],r['halfwidth'],r['depth'])
        assert k not in leaves
        leaves[k]='proposal';records[k]=r
    for field,kind in [('analytic_gamma_boxes','gamma'),('excluded_L_boxes','ball'),('pending','pending')]:
        for c,h,d in data[field]:
            k=key_from_box(c,h,d);assert k not in leaves
            if kind=='gamma':assert in_gamma(k)
            if kind=='ball':assert in_l_ball(k)
            leaves[k]=kind
    ancestors=set()
    for d,idx in leaves:
        for a in range(d):
            k=(a,tuple(i>>(d-a) for i in idx))
            assert k not in leaves,('overlapping leaves',k,(d,idx))
            ancestors.add(k)
    counts=Counter();uncovered=[];used=set()
    def visit(key):
        if not feasible(key):counts['empty_polytope_leaves']+=1;return
        if key in leaves:
            kind=leaves[key];counts[kind]+=1;used.add(key);return
        if in_gamma(key):counts['implicit_gamma']+=1;return
        if in_l_ball(key):counts['implicit_ball']+=1;return
        if key not in ancestors:
            uncovered.append([key[0],list(key[1])]);counts['uncovered']+=1;return
        counts['internal_nodes']+=1
        d,idx=key
        for bits in product([0,1],repeat=3):visit((d+1,tuple(2*idx[j]+bits[j] for j in range(3))))
    visit((0,(0,0,0)))
    receipt_counts=Counter();missing=[];point_bindings={};source_snapshot={}
    for key,r in records.items():
        okay,why,binding=matrix_receipt(r,args.matrix_dir,args.receipts_dir,proposal_hash,source_snapshot)
        receipt_counts[why]+=1
        if not okay:missing.append(r['witness'])
        else:point_bindings[r['witness']]=binding
    geometric_complete=not data['pending'] and not uncovered
    receipts_complete=not missing
    out={'geometry_complete':geometric_complete,'matrix_receipts_complete':receipts_complete,
         'matrix_replayed_this_run':False,'global_spectral_edge_certified':False,
         'status':'OPEN','counts':dict(counts),'proposed_matrix_boxes':len(records),
         'nonnegative_norm_and_radius_parameters_checked':sign_checks,
         'pending_input_boxes':len(data['pending']),'uncovered_feasible_leaves':uncovered,
         'current_receipt_counts':dict(receipt_counts),'missing_matrix_receipts':missing,
         'analytic_comparator':analytic_gamma(),'proposal_sha256_before':proposal_hash,
         'proposal_sha256':proposal_hash,'source_sha256_before':source_snapshot,
         'point_bindings':point_bindings,'receipt_directory':str(args.receipts_dir),
         'scope':'geometry/comparator audit; receipt matching alone is not a fresh exact matrix replay'}
    if geometric_complete and args.replay_matrices:
        # The canonical driver provides the parallel atomic fresh replay.
        # A distinct new output directory prevents stale per-point reuse.
        driver=args.matrix_dir/'verify_global.py'
        assert driver.is_file(),'Use the canonical global_certificate directory for a fresh replay'
        replay_dir=args.output.with_name(args.output.stem+'_fresh_matrices')
        assert not replay_dir.exists(),'Fresh replay output already exists'
        subprocess.run([sys.executable,str(driver),'--workers',str(args.workers),'--output',str(replay_dir)],check=True)
        args.receipts_dir=replay_dir/'accepted_points'
        point_bindings={};source_snapshot={}
        for r in records.values():
            okay,why,binding=matrix_receipt(r,args.matrix_dir,args.receipts_dir,proposal_hash,source_snapshot)
            assert okay,(r['witness'],why)
            point_bindings[r['witness']]=binding
        receipts_complete=True
        out.update(matrix_receipts_complete=True,matrix_replayed_this_run=True,
                   point_bindings=point_bindings,source_sha256_before=source_snapshot,
                   receipt_directory=str(args.receipts_dir),current_receipt_counts={'current':len(records)},
                   missing_matrix_receipts=[],status='PASS_OUTSIDE_L_COMPARATOR',
                   scope='complete outside-L comparator; unique global edge additionally uses fresh local/inertia certificates')
    elif geometric_complete and receipts_complete and args.require_current_receipts:
        assert all(b['canonical_receipt'] for b in point_bindings.values()),'Canonical record/proposal bindings required'
        out['status']='PASS_GEOMETRY_AND_CURRENT_RECEIPTS_EXTERNAL_REPLAY'
        out['scope']='complete exact geometry and fully bound current receipts; fresh matrix execution must be established by the separate replay driver'
    elif geometric_complete:
        out['status']='GEOMETRY_PASS_MATRIX_REPLAY_REQUIRED'
    out['proposal_sha256_after']=sha(args.proposal)
    out['source_sha256_after']={source:sha(args.matrix_dir/source) for source in source_snapshot}
    assert out['proposal_sha256_after']==proposal_hash,'Proposal changed during audit'
    assert out['source_sha256_after']==source_snapshot,'Matrix sources changed during audit'
    out['elapsed_seconds']=time.monotonic()-started
    atomic_json(args.output,out)
    print(json.dumps({k:out[k] for k in ['status','geometry_complete','matrix_receipts_complete','counts','proposed_matrix_boxes','pending_input_boxes','current_receipt_counts']},indent=2))
    if not geometric_complete:sys.exit(2)
    if not out['matrix_replayed_this_run'] and not (receipts_complete and args.require_current_receipts):sys.exit(3)

if __name__=='__main__':main()
