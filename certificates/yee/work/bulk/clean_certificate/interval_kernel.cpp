// Fixed dyadic rectangular complex intervals. No floating arithmetic is used
// by verification operations. Floating eigensolvers supply witnesses only.
#include <cstdint>
#include <vector>
#include <algorithm>
#include <cassert>
#include <limits>
#include <stdexcept>
using i64=int64_t; using i128=__int128_t; using u128=__uint128_t;
static const i64 S=(i64(1)<<52);
struct B {i64 x,y,r;};
static i64 ab(i64 a){assert(a!=INT64_MIN);return a<0?-a:a;}
static i64 cv(i128 a){if(a<INT64_MIN || a>INT64_MAX)throw std::overflow_error("interval range");return (i64)a;}
static i64 ceilpos(i128 a,i128 b){assert(a>=0 && b>0);return cv(a/b+(a%b!=0));}
static B add(B a,B b){return {cv(i128(a.x)+b.x),cv(i128(a.y)+b.y),cv(i128(a.r)+b.r)};}
static B neg(B a){return {cv(-i128(a.x)),cv(-i128(a.y)),a.r};}
static B sub(B a,B b){return add(a,neg(b));}
static B cj(B a){return {a.x,cv(-i128(a.y)),a.r};}
static B mul(B a,B b){
 if(i128(ab(a.x))+a.r>=(i128(1)<<62) || i128(ab(a.y))+a.r>=(i128(1)<<62))throw std::overflow_error("multiply range");
 if(i128(ab(b.x))+b.r>=(i128(1)<<62) || i128(ab(b.y))+b.r>=(i128(1)<<62))throw std::overflow_error("multiply range");
 i128 x=i128(a.x)*b.x-i128(a.y)*b.y;
 i128 y=i128(a.x)*b.y+i128(a.y)*b.x;
 i128 r=i128(ab(a.x)+ab(a.y))*b.r+i128(ab(b.x)+ab(b.y))*a.r+2*i128(a.r)*b.r;
 return {cv(x/S),cv(y/S),cv(i128(ceilpos(r,S))+1)};
}
static B rat(B a,i64 num,i64 den){
 assert(den>0);return {cv(i128(a.x)*num/den),cv(i128(a.y)*num/den),cv(i128(ceilpos(i128(a.r)*ab(num),den))+1)};
}
static i128 flr(i128 a,i128 b){assert(b>0);i128 q=a/b;return q-(a<0 && a%b!=0);}
static i128 cei(i128 a,i128 b){return -flr(-a,b);}
static B divr(B a,B b){
 assert(b.y==0 && b.x>b.r);i128 dl=i128(b.x)-b.r,dh=i128(b.x)+b.r;
 i128 xr=i128(a.x)*S/b.x,yi=i128(a.y)*S/b.x; i128 radius=0;
 for(int t=0;t<2;t++){
   i64 m=t?a.y:a.x;i128 mid=t?yi:xr;
   i128 lo=std::min(flr((i128(m)-a.r)*S,dl),flr((i128(m)-a.r)*S,dh));
   i128 hi=std::max(cei((i128(m)+a.r)*S,dl),cei((i128(m)+a.r)*S,dh));
   radius=std::max(radius,std::max(mid-lo,hi-mid));
 }
 return {cv(xr),cv(yi),cv(radius)};
}
static uint64_t isqrt128(u128 n){
 const u128 original=n;
 u128 res=0,bit=u128(1)<<126;while(bit>n)bit>>=2;
 while(bit){if(n>=res+bit){n-=res+bit;res=(res>>1)+bit;}else res>>=1;bit>>=2;}
 assert(res<=UINT64_MAX);
 assert(res*res<=original);
 if(res!=UINT64_MAX)assert((res+1)*(res+1)>original);
 return (uint64_t)res;
}
static B sqrtreal(B a){
 assert(a.y==0 && a.x>=a.r);
 u128 l=u128(i128(a.x)-a.r)*S,u=u128(i128(a.x)+a.r)*S;
 i64 lo=(i64)isqrt128(l),hi=(i64)isqrt128(u);if(u128(hi)*hi<u)hi++;
 i64 mid=cv((i128(lo)+hi)/2);return {mid,0,std::max(mid-lo,hi-mid)};
}
static B realpart(B a){return {a.x,0,a.r};}
static B normsq(B a){return realpart(mul(cj(a),a));}
static B cprod(const B* a,const B* b,int rows,int sa,int sb,bool conjugate,int power=0){
 assert(rows<=8192);i128 x=0,y=0,r=0;
 for(int i=0;i<rows;i++){
  B aa=a[i*sa],bb=b[i*sb];if(conjugate)aa=cj(aa);
  assert(i128(ab(aa.x))+aa.r<(i128(1)<<62) && i128(ab(aa.y))+aa.r<(i128(1)<<62));
  assert(i128(ab(bb.x))+bb.r<(i128(1)<<62) && i128(ab(bb.y))+bb.r<(i128(1)<<62));
  i128 dx=i128(aa.x)*bb.x-i128(aa.y)*bb.y,dy=i128(aa.x)*bb.y+i128(aa.y)*bb.x;
  i128 dr=(i128(ab(aa.x))+ab(aa.y))*bb.r+(i128(ab(bb.x))+ab(bb.y))*aa.r+2*i128(aa.r)*bb.r;
  assert(!__builtin_add_overflow(x,dx,&x));assert(!__builtin_add_overflow(y,dy,&y));assert(!__builtin_add_overflow(r,dr,&r));
 }
 assert(power>=0 && power<=70);i128 den=i128(S)<<power;return {cv(x/den),cv(y/den),cv(i128(ceilpos(r,den))+1)};
}
extern "C" {
void b_add(const B* a,const B* b,B* c,int n,int subtract){for(int i=0;i<n;i++)c[i]=subtract?sub(a[i],b[i]):add(a[i],b[i]);}
void b_rat(const B* a,B* c,int n,i64 num,i64 den){for(int i=0;i<n;i++)c[i]=rat(a[i],num,den);}
void b_mul(const B* a,const B* b,B* c,int n){for(int i=0;i<n;i++)c[i]=mul(a[i],b[i]);}
void b_gram(const B* a,const B* b,B* c,int n,int ma,int mb,int power){
 for(int i=0;i<ma;i++)for(int j=0;j<mb;j++)c[i*mb+j]=cprod(a+i,b+j,n,ma,mb,true,power);
}
int b_psd(const B* input,int n){
 try {
 std::vector<B> a(input,input+n*n);
 // The exact target is Hermitian; the lower triangle determines it.
 for(int j=0;j<n;j++){
  B piv=realpart(a[j*n+j]);if(piv.x<=piv.r)return 0;
  for(int i=j+1;i<n;i++)for(int k=j+1;k<=i;k++){
   B v=divr(mul(a[i*n+j],cj(a[k*n+j])),piv);
   a[i*n+k]=sub(a[i*n+k],v);
  }
 }
 return 1;
 }catch(const std::overflow_error&){return 0;}
}
void b_project(const B* raw,const B* d,B* out,int n,int m){
 for(int q=0;q<n;q++){
  B lap{0,0,0};for(int a=0;a<3;a++)lap=add(lap,normsq(d[3*q+a]));lap=realpart(lap);
  for(int j=0;j<m;j++){
   B dot{0,0,0};for(int a=0;a<3;a++)dot=add(dot,mul(d[3*q+a],raw[(3*q+a)*m+j]));
   B z=divr(dot,lap);
   for(int a=0;a<3;a++)out[(3*q+a)*m+j]=sub(raw[(3*q+a)*m+j],mul(cj(d[3*q+a]),z));
  }
 }
}
void b_gradient(const B* d,const int* low,B* out,int n,int m){
 std::fill(out,out+3*n*m,B{0,0,0});
 for(int j=0;j<m;j++){
  int q=low[j];B lap{0,0,0};for(int a=0;a<3;a++)lap=add(lap,normsq(d[3*q+a]));
  B root=sqrtreal(realpart(lap));
  for(int a=0;a<3;a++)out[(3*q+a)*m+j]=rat(divr(cj(d[3*q+a]),root),8,1);
 }
}
void b_laplacian(const B* d,B* out,int n){for(int q=0;q<n;q++){B v{0,0,0};for(int a=0;a<3;a++)v=add(v,normsq(d[3*q+a]));out[q]=realpart(v);}}
void b_curl(const B* d,const B* v,B* out,int n,int m,int adjoint){
 for(int q=0;q<n;q++)for(int a=0;a<3;a++){
  int b=(a+1)%3,c=(a+2)%3;B db=d[3*q+b],dc=d[3*q+c];
  if(adjoint){db=cj(db);dc=cj(dc);}
  for(int j=0;j<m;j++){
   B z=sub(mul(db,v[(3*q+c)*m+j]),mul(dc,v[(3*q+b)*m+j]));
   out[(3*q+a)*m+j]=adjoint?neg(z):z;
  }
 }
}
void b_material(const B* v,const int* den,B* out,int n,int m){
 for(int a=0;a<3*n;a++)for(int j=0;j<m;j++)out[a*m+j]=rat(v[a*m+j],4,den[a]);
}
void b_weight(const B* v,const B* weights,B* out,int n,int m){
 for(int q=0;q<n;q++)for(int a=0;a<3;a++)for(int j=0;j<m;j++)out[(3*q+a)*m+j]=mul(v[(3*q+a)*m+j],weights[q]);
}
void b_invweights(const B* lap,const int* mask,B* out,int n,int kind){
 for(int q=0;q<n;q++){
  if(mask && !mask[q]){out[q]={0,0,0};continue;}
  B v=lap[q];if(kind==2)v=sub(rat(v,1,12),B{S/64,0,0});
  if(kind!=1)v=sqrtreal(v);
  out[q]=divr(B{S,0,0},v);
 }
}
void b_pprime_physical(const B* d,const B* dp,const B* v,B* out,int n,int m){
 for(int q=0;q<n;q++){
  B lap{0,0,0};for(int a=0;a<3;a++)lap=add(lap,normsq(d[3*q+a]));lap=realpart(lap);
  for(int j=0;j<m;j++){
   B dot{0,0,0};for(int a=0;a<3;a++)dot=add(dot,mul(dp[3*q+a],v[(3*q+a)*m+j]));
   dot=divr(dot,lap);
   for(int a=0;a<3;a++)out[(3*q+a)*m+j]=mul(cj(d[3*q+a]),dot);
  }
 }
}
void b_gprime_raw(const B* d,const B* dp,const int* low,B* out,int n,int m){
 std::fill(out,out+3*n*m,B{0,0,0});
 for(int j=0;j<m;j++){
  int q=low[j];B lap{0,0,0};for(int a=0;a<3;a++)lap=add(lap,normsq(d[3*q+a]));
  B root=sqrtreal(realpart(lap));
  for(int a=0;a<3;a++)out[(3*q+a)*m+j]=rat(divr(cj(dp[3*q+a]),root),8,1);
 }
}
}
// Unnormalized length 20,10,5 mixed-radix FFT; roots[] contains 20th roots.
static void fftrec(const B* in,int stride,B* out,int len,const B* roots,int inverse){
 if(len==1){out[0]=in[0];return;}
 if(len%2==0){
  B ev[20],od[20];fftrec(in,2*stride,ev,len/2,roots,inverse);fftrec(in+stride,2*stride,od,len/2,roots,inverse);
  for(int j=0;j<len/2;j++){
   B w=roots[(20/len)*j];if(!inverse)w=cj(w);B z=mul(w,od[j]);out[j]=add(ev[j],z);out[j+len/2]=sub(ev[j],z);
  }
 }else{
  assert(len==5);
  for(int j=0;j<5;j++){
   B aa[5],bb[5];for(int l=0;l<5;l++){aa[l]=in[l*stride];bb[l]=roots[(4*j*l)%20];if(!inverse)bb[l]=cj(bb[l]);}
   out[j]=cprod(aa,bb,5,1,1,false);
  }
 }
}
static void axisfft(const B* in,B* out,int cols,int axis,const B* roots,const B* norms,int inverse){
 int shape[3]={20,10,10};int strides[3]={100,10,1};int len=shape[axis],step=strides[axis];
 for(int i=0;i<20;i++)for(int j=0;j<10;j++)for(int k=0;k<10;k++){
  int coord[3]={i,j,k};if(coord[axis]!=0)continue;int base=100*i+10*j+k;
  for(int c=0;c<cols;c++){
   B vv[20];fftrec(in+base*cols+c,step*cols,vv,len,roots,inverse);
   for(int a=0;a<len;a++)out[(base+a*step)*cols+c]=mul(vv[a],norms[axis]);
  }
 }
}
extern "C" void b_fft(const B* in,B* out,int cols,int inverse,const B* roots,const B* norms){
 const int n=2000;std::vector<B> a(n*cols),b(n*cols);
 if(!inverse){
  axisfft(in,a.data(),cols,0,roots,norms,0);
  for(int i=0;i<20;i++)for(int j=0;j<10;j++)for(int k=0;k<10;k++){
   int q=100*i+10*j+k;B w=roots[(i*(j+k))%20];for(int c=0;c<cols;c++)a[q*cols+c]=mul(a[q*cols+c],w);
  }
  axisfft(a.data(),b.data(),cols,1,roots,norms,0);axisfft(b.data(),out,cols,2,roots,norms,0);
 }else{
  axisfft(in,a.data(),cols,2,roots,norms,1);axisfft(a.data(),b.data(),cols,1,roots,norms,1);
  for(int i=0;i<20;i++)for(int j=0;j<10;j++)for(int k=0;k<10;k++){
   int q=100*i+10*j+k;B w=cj(roots[(i*(j+k))%20]);for(int c=0;c<cols;c++)b[q*cols+c]=mul(b[q*cols+c],w);
  }
  axisfft(b.data(),out,cols,0,roots,norms,1);
 }
}
