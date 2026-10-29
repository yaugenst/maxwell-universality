"""Full fresh verification of all 604 period-20 Yee gap boxes.
Default mode checks every matrix certificate, then geometry and coverage.
--shard I checks one bounded batch; --finalize only assembles such completed
checks and is NOT a replacement for running all shards. Missing/invalid evidence
raises; no witness generation or stored-PASS shortcut occurs in this verifier.
"""
from __future__ import annotations
import os
os.environ["OPENBLAS_NUM_THREADS"]="1";os.environ["OMP_NUM_THREADS"]="1"
os.environ["UBSAN_OPTIONS"]="halt_on_error=1:print_stacktrace=1"
from pathlib import Path
from fractions import Fraction
from concurrent.futures import ProcessPoolExecutor,as_completed
import argparse,json,hashlib,subprocess,time,sys,platform
BASE=Path(__file__).resolve().parent
SOURCES=["reproduce.py","interval_kernel.cpp","interval_tools.py","verify_point.py","verify_geometry_cover.py","exact_geometry.py","cover_screen_complete.json","audit/independent_checks.py","evidence_manifest.json"]
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def source_hashes():return {p:sha(BASE/p) for p in SOURCES}
def proposals():
    frozen=json.loads((BASE/"evidence_manifest.json").read_text())["files"]
    for name,digest in frozen.items():
        if not (BASE/name).is_file():raise FileNotFoundError("Missing frozen evidence: "+name)
        assert sha(BASE/name)==digest,"Frozen evidence changed: "+name
    records=json.loads((BASE/"cover_screen_complete.json").read_text())["accepted"]
    assert len(records)==604
    assert len({(tuple(r["center"]),r["halfwidth"]) for r in records})==604
    assert len({r["witness"] for r in records})==604
    for r in records:
        assert Fraction(r["halfwidth"])==Fraction(1,32) and r["depth"]==4
        assert all(Fraction(x)*32==int(Fraction(x)*32) for x in r["center"])
        name=r["witness"];assert Path(name).name==name and name.endswith(".npz")
        if not (BASE/"witnesses"/name).is_file():raise FileNotFoundError("Missing required witness: "+name)
    return sorted(records,key=lambda r:tuple(r["center"]))
def validate_witness(r):
    import numpy as np
    path=BASE/"witnesses"/r["witness"];before=sha(path)
    with np.load(path,allow_pickle=False) as w:
        low=w["low"]
        assert low.ndim==1 and np.issubdtype(low.dtype,np.integer)
        assert 1<=len(low)<=15 and len(set(low.tolist()))==len(low)
        assert np.all(low>=0) and np.all(low<2000)
        assert w["F"].shape==(2000,3,2) and w["Fpos"].shape==(2000,3,2*len(low)-2)
        assert np.all(np.isfinite(w["F"])) and np.all(np.isfinite(w["Fpos"]))
        assert np.max(abs(w["F"]))<100 and np.max(abs(w["Fpos"]))<100
        assert list(w["center"])==r["center"] and float(w["halfwidth"])==r["halfwidth"]
    return before
def verify_one(r):
    before=validate_witness(r)
    from verify_point import verify_record
    accepted=verify_record(r)
    after=sha(BASE/"witnesses"/r["witness"])
    assert before==after,"Witness bytes changed during verification"
    assert accepted["status"]=="INTERVAL_PASS" and accepted["frequency_halfwidth"]=="1/4096"
    accepted["witness_sha256"]=after;accepted["depth"]=4
    return accepted
def compile_kernel(out):
    args=["g++","-O2","-g","-std=c++17","-shared","-fPIC","-fsanitize=undefined","-fno-sanitize-recover=all",str(BASE/"interval_kernel.cpp"),"-o",str(BASE/"interval_kernel.so")]
    subprocess.run(args,check=True)
    import numpy as np
    env={"python":sys.version,"platform":platform.platform(),"numpy":np.__version__,"compiler":subprocess.run(["g++","--version"],check=True,text=True,capture_output=True).stdout,"compile_argv":args,"assertions_enabled":__debug__,"sanitizer":"undefined, halt on first error"}
    (out/"runtime.json").write_text(json.dumps(env,indent=2)+"\n")
def split(records,i,n):return records[len(records)*i//n:len(records)*(i+1)//n]
def run_shard(records,i,n,workers,out):
    subset=split(records,i,n);sources=source_hashes();started=time.monotonic();result=[]
    name=out/f"shard_{i:02d}.jsonl";meta=out/f"shard_{i:02d}.metadata.json"
    print("SHARD_START",i,"of",n,"points",len(subset),flush=True)
    with name.open("w") as f,ProcessPoolExecutor(max_workers=workers) as pool:
        for future in as_completed([pool.submit(verify_one,r) for r in subset]):
            r=future.result();result.append(r);f.write(json.dumps(r)+"\n");f.flush()
            print("FRESH_MATRIX_ACCEPT",i,len(result),"/",len(subset),r["center"],r["witness_sha256"],flush=True)
    assert len(result)==len(subset) and source_hashes()==sources
    meta.write_text(json.dumps({"index":i,"shards":n,"count":len(result),"source_sha256":sources,"records_sha256":sha(name),"elapsed_seconds":time.monotonic()-started,"status":"FRESH_FULL_MATRIX_CHECKS_COMPLETED"},indent=2)+"\n")
    print("SHARD_COMPLETE",i,len(result),time.monotonic()-started,flush=True)
def finalize(records,n,out):
    from verify_point import verify_scalar
    all_records=[];sources=source_hashes()
    for i in range(n):
        name=out/f"shard_{i:02d}.jsonl";meta=json.loads((out/f"shard_{i:02d}.metadata.json").read_text())
        assert meta["index"]==i and meta["shards"]==n and meta["source_sha256"]==sources
        assert meta["records_sha256"]==sha(name) and meta["status"]=="FRESH_FULL_MATRIX_CHECKS_COMPLETED"
        actual=[json.loads(x) for x in name.read_text().splitlines()];expected=split(records,i,n)
        assert len(actual)==meta["count"]==len(expected)
        assert {tuple(r["center"]) for r in actual}=={tuple(r["center"]) for r in expected}
        for r in actual:
            assert r["status"]=="INTERVAL_PASS" and r["frequency_halfwidth"]=="1/4096"
            assert r["witness_sha256"]==sha(BASE/"witnesses"/r["witness"])
            assert verify_scalar(r["verified_constants"],r["halfwidth"])==r["margins"]
        all_records.extend(actual)
    assert len(all_records)==604 and len({tuple(r["center"]) for r in all_records})==604
    all_records.sort(key=lambda r:tuple(r["center"]))
    (BASE/"verified_boxes_strengthened.jsonl").write_text("".join(json.dumps(r)+"\n" for r in all_records))
    covered=subprocess.run([sys.executable,str(BASE/"verify_geometry_cover.py")],cwd=BASE,check=True,capture_output=True,text=True)
    (out/"geometry_cover.log").write_text(covered.stdout);print(covered.stdout,end="",flush=True)
    independent=subprocess.run([sys.executable,str(BASE/"audit/independent_checks.py"),"--source",str(BASE),"--output",str(out/"independent_checks.json")],check=True,capture_output=True,text=True)
    (out/"independent_checks.log").write_text(independent.stdout);print(independent.stdout,end="",flush=True)
    limits={"negative_margin":Fraction(1,128),"positive_diagonal_margin":Fraction(1,4),"gradient_margin":Fraction(3,4),"positive_determinant_margin":Fraction(1,10)}
    minima={k:min(Fraction(r["margins"][k][0]) for r in all_records) for k in limits}
    for k,v in limits.items():assert minima[k]>v;print("EXACT_MARGIN",k,str(minima[k]),">",str(v),flush=True)
    summary={"status":"ALL_604_FULL_MATRIX_CERTIFICATES_REPRODUCED","scope":"H1 infinite period-20 Yee bulk gap only; not H2/H3/R5 or the full reduction","gap_lower_bound":"1/4096","frequency_squared":"1/64","frequency_halfwidth":"1/4096","matrix_checks":604,"shards":n,"all_before_after_witness_hashes_equal":True,"all_current_witness_hashes_equal":True,"undefined_behavior_sanitizer":"all 604 matrix checks","source_sha256":sources,"minimum_margins":{k:str(v) for k,v in minima.items()},"compiler_runtime_file":"runtime.json","formal_verification":False}
    (out/"reproduction_summary.json").write_text(json.dumps(summary,indent=2)+"\n")
    print("COMPLETE_FRESH_BULK_GAP_REPRODUCTION_PASS",flush=True)
def main():
    if not __debug__:raise RuntimeError("Do not use Python -O")
    ap=argparse.ArgumentParser();ap.add_argument("--workers",type=int,default=4);ap.add_argument("--shards",type=int,default=11);ap.add_argument("--shard",type=int);ap.add_argument("--finalize",action="store_true");ap.add_argument("--output",type=Path,default=BASE/"verification_run");a=ap.parse_args()
    assert a.workers>=1 and a.shards>=1
    if a.shard is not None:assert 0<=a.shard<a.shards and not a.finalize
    out=a.output.resolve();out.mkdir(parents=True,exist_ok=True);records=proposals();compile_kernel(out)
    if a.finalize:finalize(records,a.shards,out);return
    if a.shard is not None:run_shard(records,a.shard,a.shards,a.workers,out);return
    for i in range(a.shards):run_shard(records,i,a.shards,a.workers,out)
    finalize(records,a.shards,out)
if __name__=="__main__":main()
