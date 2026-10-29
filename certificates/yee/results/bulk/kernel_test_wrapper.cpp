#include "/workspace/scratch/afe058a3cc75/maxwell_research/work/bulk/maxwell_round6/interval_kernel.cpp"
extern "C" B audit_mul(B a,B b){return mul(a,b);}
extern "C" B audit_rat(B a,int64_t n,int64_t d){return rat(a,n,d);}
extern "C" B audit_div(B a,B b){return divr(a,b);}
extern "C" B audit_sqrt(B a){return sqrtreal(a);}
