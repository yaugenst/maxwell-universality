"""Integer arithmetic for finite FCC Yee fibers at time-reversal points.

NumPy is used only to read numeric witness archives, never for acceptance.
Cells, incidence matrices, symmetries, residual norms and interval comparisons
are reconstructed with Python integers/Fractions.
"""
from fractions import Fraction as F
from itertools import product

if not __debug__:
    raise RuntimeError('Exact acceptance requires assertions; do not run with -O or PYTHONOPTIMIZE.')

N=2000
COORDS=list(product(range(20),range(10),range(10)))
MASS_BITS=29

def reduce_coord(r):
    n2=r[1]//10;n3=r[2]//10
    x=r[0]-10*(n2+n3);n1=x//20
    return ((x%20)*10+r[1]%10)*10+r[2]%10,(n1,n2,n3)

def dot(u,v):
    return sum(a*b for a,b in zip(u,v))

def nearest(n,d):
    assert d>0
    return (2*n+d)//(2*d)

def quantize(values,bits=100):
    result=[]
    for x in values:
        a,b=float(x).as_integer_ratio()
        result.append(nearest(a*(1<<bits),b))
    return result

def apply_rows(rows,u):
    return [sum(a*u[j] for j,a in row.items()) for row in rows]

def transpose_rows(rows):
    result=[{} for _ in rows]
    for i,row in enumerate(rows):
        for j,a in row.items():result[j][i]=a
    return result

def gram_rows(left,right):
    result=[{} for _ in left]
    for lrow,rrow in zip(left,right):
        for i,a in lrow.items():
            for j,b in rrow.items():result[i][j]=result[i].get(j,0)+a*b
    return [{j:a for j,a in row.items() if a} for row in result]

def combine_rows(*terms):
    result=[{} for _ in terms[0][1]]
    for coefficient,rows in terms:
        for i,row in enumerate(rows):
            for j,a in row.items():result[i][j]=result[i].get(j,0)+coefficient*a
    return [{j:a for j,a in row.items() if a} for row in result]

def base_cell(r):
    # Doubled cell-center coordinates. Sphere centers are FCC shifts +/-5.
    point=tuple(2*(a%20)+1 for a in r)
    for fcc in [(0,0,0),(0,20,20),(20,0,20),(20,20,0)]:
        for offset in [-5,5]:
            delta=[(point[j]-fcc[j]-offset+20)%40-20 for j in range(3)]
            if sum(a*a for a in delta)<=100:return 12
    return 1

class ExactFiber:
    def __init__(self,k_twice,perturb):
        self.k=tuple(k_twice)
        self.perturb=perturb
        assert all(isinstance(x,int) for plane in perturb for row in plane for x in row)
        assert len(perturb)==20 and all(len(p)==20 and all(len(r)==20 for r in p) for p in perturb)
        for r in product(range(20),repeat=3):
            p=perturb[r[0]][r[1]][r[2]]
            assert 0<=p<=2046
            inv=tuple((-a-1)%20 for a in r)
            assert p==perturb[inv[0]][inv[1]][inv[2]]
            for tr in [(0,10,10),(10,0,10),(10,10,0)]:
                s=tuple((r[j]+tr[j])%20 for j in range(3))
                assert p==perturb[s[0]][s[1]][s[2]]
        self.shift=[]
        for axis in range(3):
            row=[]
            for r in COORDS:
                s=list(r);s[axis]+=1
                idx,tr=reduce_coord(s)
                sign=1 if sum(a*b for a,b in zip(self.k,tr))%2==0 else -1
                row.append((idx,sign))
            self.shift.append(row)
        self.C=self.curl_rows(kind='zero')
        self.K=[self.curl_rows(kind='first',axis=j) for j in range(3)]
        self.L=[self.curl_rows(kind='second',axis=j) for j in range(3)]
        self.lap=gram_rows(self.C,self.C)
        self.B=[combine_rows((1,gram_rows(self.C,k)),(-1,gram_rows(k,self.C))) for k in self.K]
        self.D=[[None]*3 for _ in range(3)]
        for i in range(3):
            for j in range(3):
                terms=[(1,gram_rows(self.K[i],self.K[j])),(1,gram_rows(self.K[j],self.K[i]))]
                if i==j:terms += [(-1,gram_rows(self.L[i],self.C)),(-1,gram_rows(self.C,self.L[i]))]
                self.D[i][j]=combine_rows(*terms)
        self.mass=[];self.inversion=[]
        for axis in range(3):
            transverse=[j for j in range(3) if j!=axis]
            for r in COORDS:
                total=0
                for b in product([-1,0],repeat=2):
                    s=list(r)
                    for j,a in zip(transverse,b):s[j]=(s[j]+a)%20
                    total+=(base_cell(s)<<21)+perturb[s[0]][s[1]][s[2]]
                self.mass.append(total)
                target=[-a for a in r];target[axis]-=1
                idx,tr=reduce_coord(target)
                sign=-1 if sum(a*b for a,b in zip(self.k,tr))%2==0 else 1
                self.inversion.append((axis*N+idx,sign))
        for i,(j,s) in enumerate(self.inversion):
            assert self.inversion[j]==(i,s)
            assert self.mass[i]==self.mass[j]
        self.check_parity(self.lap,1)
        for b in self.B:self.check_parity(b,-1)
        for row in self.D:
            for d in row:self.check_parity(d,1)

    def curl_rows(self,kind,axis=None):
        rows=[{} for _ in range(3*N)]
        # Curl output/input/differentiation direction/orientation.
        for out,inp,direction,orientation in [(0,1,2,-1),(0,2,1,1),(1,0,2,1),(1,2,0,-1),(2,0,1,-1),(2,1,0,1)]:
            if kind!='zero' and direction!=axis:continue
            for anchor,(idx,phase) in enumerate(self.shift[direction]):
                row=rows[out*N+anchor]
                for col,coefficient in [(inp*N+idx,orientation*phase),(inp*N+anchor,orientation*(1 if kind=='first' else -1))]:
                    row[col]=row.get(col,0)+coefficient
        return [{j:a for j,a in row.items() if a} for row in rows]

    def check_parity(self,rows,parity):
        for i,row in enumerate(rows):
            ii,si=self.inversion[i]
            transformed={self.inversion[j][0]:si*a*self.inversion[j][1] for j,a in row.items()}
            assert transformed=={j:parity*a for j,a in rows[ii].items()}

    def invert(self,u):
        return [s*u[j] for j,s in self.inversion]

    def project(self,u,parity):
        # Output denominator is twice the input denominator.
        return [a+parity*b for a,b in zip(u,self.invert(u))]

    def apply_mass_scaled(self,u):
        return [(a<<MASS_BITS)-m*b for a,m,b in zip(apply_rows(self.lap,u),self.mass,u)]

    def eigen_residual(self,u,lambda_bits=80):
        au=self.apply_mass_scaled(u);norm=dot(u,u)
        lam_num=nearest(dot(u,au)<<(lambda_bits-MASS_BITS),norm)
        residual=[(a<<(lambda_bits-MASS_BITS))-lam_num*b for a,b in zip(au,u)]
        residual_sq=dot(residual,residual)
        best=0
        for b in range(1,lambda_bits):
            if residual_sq <= norm << (2*lambda_bits-2*b):best=b
            else:break
        assert best>40
        center=F(lam_num,1<<lambda_bits);radius=F(1,1<<best)
        return {'center':center,'radius':radius,'lower':center-radius,'upper':center+radius,
                'lambda_numerator':lam_num,'lambda_bits':lambda_bits,'residual_squared_numerator':residual_sq,
                'vector_norm_squared_numerator':norm,'residual_dyadic_exponent':best}

def fstr(x):return str(x.numerator)+'/'+str(x.denominator)

def ldl_positive(a):
    n=len(a);l=[[F(i==j) for j in range(n)] for i in range(n)];d=[]
    for j in range(n):
        dj=a[j][j]-sum(l[j][k]**2*d[k] for k in range(j))
        assert dj>0,(j,dj)
        d.append(dj)
        for i in range(j+1,n):
            l[i][j]=(a[i][j]-sum(l[i][k]*l[j][k]*d[k] for k in range(j)))/dj
    return d
