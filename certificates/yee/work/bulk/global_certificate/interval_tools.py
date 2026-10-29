"""Exact fixed-point interval arithmetic and wrappers for the C++ kernel."""
from __future__ import annotations
import ctypes,math
from fractions import Fraction as F
from pathlib import Path
import numpy as np

Q=100;T=1<<Q;B=48;S=1<<B
class I:
    __slots__=('lo','hi')
    def __init__(self,x,hi=None,raw=False):
        if raw:self.lo=int(x);self.hi=int(hi)
        else:
            a=F(x);b=F(x if hi is None else hi)
            self.lo=a.numerator*T//a.denominator
            self.hi=-((-b.numerator*T)//b.denominator)
        assert self.lo<=self.hi
    @staticmethod
    def cast(x):return x if isinstance(x,I) else I(x)
    def __add__(self,b):b=self.cast(b);return I(self.lo+b.lo,self.hi+b.hi,True)
    __radd__=__add__
    def __neg__(self):return I(-self.hi,-self.lo,True)
    def __sub__(self,b):return self+-self.cast(b)
    def __rsub__(self,b):return self.cast(b)+-self
    def __mul__(self,b):
        b=self.cast(b);v=[self.lo*b.lo,self.lo*b.hi,self.hi*b.lo,self.hi*b.hi]
        return I(min(v)//T,-((-max(v))//T),True)
    __rmul__=__mul__
    def __truediv__(self,b):
        b=self.cast(b);assert not b.lo<=0<=b.hi
        v=[F(a*T,c) for a in (self.lo,self.hi) for c in (b.lo,b.hi)]
        l=min(v);h=max(v)
        return I(l.numerator//l.denominator,-((-h.numerator)//h.denominator),True)
    def __rtruediv__(self,b):return self.cast(b)/self
    def sqrt(self):
        assert self.lo>=0
        l=math.isqrt(self.lo*T);h=math.isqrt(self.hi*T)
        if h*h<self.hi*T:h+=1
        return I(l,h,True)
    def __pow__(self,n):
        if n<0:return I(1)/(self**(-n))
        x=I(1);b=self
        while n:
            if n&1:x=x*b
            b=b*b;n//=2
        return x
    def bounds(self):return [str(F(self.lo,T)),str(F(self.hi,T))]
    def decimals(self):return [self.lo/T,self.hi/T] # DISPLAY ONLY


def atan_interval(den):
    z=I(0)
    for k in range(120):z+=I(F((-1)**k,den**(2*k+1)*(2*k+1)))
    err=F(1,den**241*241)
    return z+I(-err,err)
PI=16*atan_interval(5)-4*atan_interval(239)

def cis(phase):
    f=F(phase);f=f-(f+F(1,2)).numerator//(f+F(1,2)).denominator
    x=2*PI*f;x2=x*x
    tc=I(1);ts=x;c=tc;s=ts
    for k in range(1,65):
        tc=tc*(-x2)/((2*k-1)*(2*k));c+=tc
        ts=ts*(-x2)/((2*k)*(2*k+1));s+=ts
    err=F(4**130,math.factorial(130))
    return cb(c+I(-err,err),s+I(-err,err))

def cb(real=0,imag=0):
    real=I.cast(real);imag=I.cast(imag);shift=Q-B
    lr=real.lo//(1<<shift);ur=-((-real.hi)//(1<<shift))
    li=imag.lo//(1<<shift);ui=-((-imag.hi)//(1<<shift))
    mr=(lr+ur)//2;mi=(li+ui)//2;r=max(mr-lr,ur-mr,mi-li,ui-mi)
    return np.array([mr,mi,r],dtype=np.int64)

def witness(z):
    z=np.asarray(z);out=np.zeros(z.shape+(3,),np.int64)
    # These quantized dyadics DEFINE the witness; no approximation is trusted.
    out[...,0]=np.rint(z.real*S).astype(np.int64)
    out[...,1]=np.rint(z.imag*S).astype(np.int64)
    return np.ascontiguousarray(out)

def mids(z):return (z[...,0]+1j*z[...,1])/S

def ptr(z):assert z.flags.c_contiguous;return ctypes.c_void_p(z.ctypes.data)
LIB=ctypes.CDLL(str(Path(__file__).with_name('interval_kernel.so')))
for name in ['b_add','b_rat','b_mul','b_gram','b_project','b_gradient','b_laplacian','b_curl','b_material','b_weight','b_invweights','b_pprime_physical','b_gprime_raw','b_fft']:
    getattr(LIB,name).restype=None
LIB.b_psd.restype=ctypes.c_int

def add(a,b,subtract=False):
    assert a.shape==b.shape;o=np.empty_like(a);LIB.b_add(ptr(a),ptr(b),ptr(o),ctypes.c_int(a.size//3),ctypes.c_int(subtract));return o

def rat(a,n,d=1):
    o=np.empty_like(a);LIB.b_rat(ptr(a),ptr(o),ctypes.c_int(a.size//3),ctypes.c_int64(n),ctypes.c_int64(d));return o

def mul(a,b):
    aa,bb=np.broadcast_arrays(a,b);aa=np.ascontiguousarray(aa);bb=np.ascontiguousarray(bb)
    o=np.empty_like(aa);LIB.b_mul(ptr(aa),ptr(bb),ptr(o),ctypes.c_int(o.size//3));return o

def gram(a,b=None,power=0):
    if b is None:b=a
    a=np.ascontiguousarray(a.reshape(-1,a.shape[-2],3));b=np.ascontiguousarray(b.reshape(-1,b.shape[-2],3))
    assert a.shape[0]==b.shape[0]
    o=np.empty((a.shape[1],b.shape[1],3),np.int64)
    LIB.b_gram(ptr(a),ptr(b),ptr(o),ctypes.c_int(a.shape[0]),ctypes.c_int(a.shape[1]),ctypes.c_int(b.shape[1]),ctypes.c_int(power));return o

def psd(a):
    a=np.ascontiguousarray(a)
    assert np.all(a[...,2]>=0), "negative interval radius"
    assert np.all(a[...,0]!=np.iinfo(np.int64).min) and np.all(a[...,1]!=np.iinfo(np.int64).min), "INT64_MIN absolute-value input"
    biggest=max(int(np.abs(a[...,0]).max(initial=0)),int(np.abs(a[...,1]).max(initial=0)))+int(a[...,2].max(initial=0))
    if biggest==0:return False
    exponent=B-(biggest.bit_length()-1)
    if exponent>0:a=rat(a,1<<exponent)
    elif exponent<0:a=rat(a,1,1<<(-exponent))
    return bool(LIB.b_psd(ptr(a),ctypes.c_int(a.shape[0])))

def shifted_identity(a,constant,sign=-1):
    o=rat(a,sign);d=cb(constant)
    for j in range(a.shape[0]):o[j,j]=add(o[j,j],d)
    return o

def normcheck(a,bound,squared=False):
    value=I(bound) if squared else I(bound)**2
    power=max(0,value.hi.bit_length()-Q)
    return psd(shifted_identity(gram(a,power=power),value/(1<<power)))

def hnormcheck(a,bound):
    return psd(shifted_identity(a,I(bound),-1)) and psd(shifted_identity(a,I(bound),1))

ROOTS=np.array([cis(F(j,20)) for j in range(20)])
NORMS=np.array([cb(1/I(v).sqrt()) for v in [20,10,10]])

def fft(a,inverse=False):
    assert a.shape[0:2]==(2000,3);ncol=a.shape[2];o=np.empty_like(a)
    LIB.b_fft(ptr(a),ptr(o),ctypes.c_int(3*ncol),ctypes.c_int(inverse),ptr(ROOTS),ptr(NORMS));return o

def make_d(center):
    n1,n2,n3=np.meshgrid(np.arange(20),np.arange(10),np.arange(10),indexing='ij')
    q=np.stack([n1,2*n2-n1,2*n3-n1],axis=-1).reshape(2000,3)%20
    phases=np.array([cis(F(x)/20) for x in center])
    dd=mul(ROOTS[q],np.broadcast_to(phases,(2000,3,3)))
    one=np.zeros_like(dd);one[...,0]=S
    return add(dd,one,True)

def laplacian(d):
    o=np.empty((2000,3),np.int64);LIB.b_laplacian(ptr(d),ptr(o),ctypes.c_int(2000));return o

def project(raw,d):
    o=np.empty_like(raw);LIB.b_project(ptr(raw),ptr(d),ptr(o),ctypes.c_int(2000),ctypes.c_int(raw.shape[2]));return o

def gradient(d,low):
    low=np.ascontiguousarray(low,dtype=np.int32);o=np.zeros((2000,3,len(low),3),np.int64)
    LIB.b_gradient(ptr(d),ptr(low),ptr(o),ctypes.c_int(2000),ctypes.c_int(len(low)));return o

def curl(d,a,adjoint=False):
    o=np.empty_like(a);LIB.b_curl(ptr(d),ptr(a),ptr(o),ctypes.c_int(2000),ctypes.c_int(a.shape[2]),ctypes.c_int(adjoint));return o

def material(a,den):
    den=np.ascontiguousarray(den,dtype=np.int32);o=np.empty_like(a)
    LIB.b_material(ptr(a),ptr(den),ptr(o),ctypes.c_int(2000),ctypes.c_int(a.shape[2]));return o

def invweights(lap,kind,mask=None):
    if mask is not None:mask=np.ascontiguousarray(mask,dtype=np.int32)
    o=np.empty_like(lap);LIB.b_invweights(ptr(lap),ptr(mask) if mask is not None else None,ptr(o),ctypes.c_int(2000),ctypes.c_int(kind));return o

def weight(a,w):
    o=np.empty_like(a);LIB.b_weight(ptr(a),ptr(w),ptr(o),ctypes.c_int(2000),ctypes.c_int(a.shape[2]));return o

def pprime(d,dp,a):
    o=np.empty_like(a);LIB.b_pprime_physical(ptr(d),ptr(dp),ptr(a),ptr(o),ctypes.c_int(2000),ctypes.c_int(a.shape[2]));return o

def gprime_raw(d,dp,low):
    low=np.ascontiguousarray(low,dtype=np.int32);o=np.zeros((2000,3,len(low),3),np.int64)
    LIB.b_gprime_raw(ptr(d),ptr(dp),ptr(low),ptr(o),ctypes.c_int(2000),ctypes.c_int(len(low)));return o

if __name__=='__main__':
    import time
    rng=np.random.default_rng(1);a=witness(rng.normal(size=(2000,3,4))+1j*rng.normal(size=(2000,3,4)))
    st=time.monotonic();z=fft(fft(a),True)
    exact_included=np.all(abs(z[...,0]-a[...,0])<=z[...,2]) and np.all(abs(z[...,1]-a[...,1])<=z[...,2])
    assert exact_included
    print('Interval Fourier roundtrip contains exact input:',exact_included,'seconds',time.monotonic()-st)
    print('Maximum displayed roundtrip radius',float(z[...,2].max()/S))
    assert normcheck(a,200)
    print('Exact interval Gram/LDL norm test: PASS')
