"""Independent Fraction endpoint checks of supplied interval primitives.
These are adversarial arithmetic tests, not formal verification.
The mathematical derivation in audit.md proves the general enclosure formulas.
"""
from pathlib import Path
from fractions import Fraction as F
import argparse,ctypes,random,itertools,subprocess,json,math
class B(ctypes.Structure):_fields_=[("x",ctypes.c_int64),("y",ctypes.c_int64),("r",ctypes.c_int64)]
S=1<<52
def contains(b,x,y):return F(b.x-b.r,S)<=x<=F(b.x+b.r,S) and F(b.y-b.r,S)<=y<=F(b.y+b.r,S)
def corners(b):return itertools.product((F(b.x-b.r,S),F(b.x+b.r,S)),(F(b.y-b.r,S),F(b.y+b.r,S)))
def main():
    ap=argparse.ArgumentParser();ap.add_argument("--source",type=Path,required=True);args=ap.parse_args();out=Path(__file__).resolve().parent
    source=out/"kernel_test_wrapper.cpp"
    source.write_text('#include "'+str(args.source/"interval_kernel.cpp")+'"\nextern "C" B audit_mul(B a,B b){return mul(a,b);}\nextern "C" B audit_rat(B a,int64_t n,int64_t d){return rat(a,n,d);}\nextern "C" B audit_div(B a,B b){return divr(a,b);}\nextern "C" B audit_sqrt(B a){return sqrtreal(a);}\n')
    libpath=out/"kernel_test_wrapper.so"
    subprocess.run(["g++","-O1","-g","-std=c++17","-shared","-fPIC","-fsanitize=undefined","-fno-sanitize-recover=all",str(source),"-o",str(libpath)],check=True)
    lib=ctypes.CDLL(str(libpath))
    for n in ["mul","div"]:getattr(lib,"audit_"+n).argtypes=[B,B];getattr(lib,"audit_"+n).restype=B
    lib.audit_rat.argtypes=[B,ctypes.c_int64,ctypes.c_int64];lib.audit_rat.restype=B
    lib.audit_sqrt.argtypes=[B];lib.audit_sqrt.restype=B
    rng=random.Random(0xC0FFEE);count=0
    for j in range(2000):
        # Broad signs, small and large radii, large represented centers.
        e=rng.randrange(0,58);f=rng.randrange(0,min(58,112-e))
        a=B(rng.randrange(-(1<<e),1<<e),rng.randrange(-(1<<e),1<<e),rng.randrange(0,1<<e))
        b=B(rng.randrange(-(1<<f),1<<f),rng.randrange(-(1<<f),1<<f),rng.randrange(0,1<<f))
        c=lib.audit_mul(a,b)
        for x,y in corners(a):
            for u,v in corners(b):assert contains(c,x*u-y*v,x*v+y*u)
        n=rng.randrange(-100,101);d=rng.randrange(1,101);c=lib.audit_rat(a,n,d)
        for x,y in corners(a):assert contains(c,x*F(n,d),y*F(n,d))
        b=B(rng.randrange(S//2,2*S),0,rng.randrange(0,S//8));c=lib.audit_div(a,b)
        for x,y in corners(a):
            for den in (F(b.x-b.r,S),F(b.x+b.r,S)):assert contains(c,x/den,y/den)
        b=B(rng.randrange(1,1<<61),0,0);b.r=rng.randrange(0,b.x+1);c=lib.audit_sqrt(b)
        lo=F(c.x-c.r,S);hi=F(c.x+c.r,S);assert lo>=0 and lo*lo<=F(b.x-b.r,S) and hi*hi>=F(b.x+b.r,S)
        count+=1
    print(json.dumps({"case_groups":count,"primitive_calls":4*count,"endpoint_comparisons":"exact fractions","undefined_behavior_sanitizer":True,"status":"ARITHMETIC_ENDPOINT_CHECK_PASS"},indent=2))
if __name__=="__main__":main()
