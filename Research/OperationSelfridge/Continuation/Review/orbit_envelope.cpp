#include <iostream>
#include <vector>
#include <algorithm>
#include <cmath>
#include <map>
#include <numeric>
#include <array>
#include <set>
#include <iomanip>
#include <chrono>
using namespace std;
const int pref=60000,endp=10000000,H=18000,dmax=10;
vector<int> ps,small,ix;
vector<vector<int>> to;
double late_coef=0;
double g3=2.,g5=4./3;
vector<double> src;
double baseone,base3;
double moment(int p,double g){double r=p-1.;return 1+g*(7.*p*p-2*p+1)/(r*r*r);}
map<int,int> sch={{11,3},{13,3},{17,4},{19,4},{23,6},{29,8},{31,8},{37,10},{41,12},{43,12}};
vector<int> early;
vector<double> pmf(int p,double g){vector<double> v(11,0);double t=g/p;v[1]=1-t;for(int j=2;j<=9;++j){v[j]=t*(1.-1./p);t/=p;}v[10]=t;return v;}
void advance(vector<double>& prob,vector<double>& out, const vector<double>& c){
 fill(out.begin(),out.end(),0.);
 for(int j=1;j<=10;++j) {
     auto &ids=to[j]; for(int i=0;i<(int)ids.size();++i)out[ids[i]]+=prob[i]*c[j];
 }
 prob.swap(out);
}
double head_mean=0,head_cube=0,headcost=0;
vector<double> bk, slopes,ints;
double corr(double y){
 int j=upper_bound(bk.begin(),bk.end(),y)-bk.begin()-1;
 return slopes[j]*y+ints[j];
}
void make_kernel(int r){
 vector<int> Hs; for(int x=0;x<45;++x)if(x%3&&x%5&&x%9!=r&&x%15!=1)Hs.push_back(x);
 int n=Hs.size();
 vector<vector<int>> groups;
 int mods[]={1,3,9,5,15,45};
 for(int q:mods){
  vector<int> masks(q);for(int i=0;i<n;++i)masks[Hs[i]%q]|=1<<i;groups.push_back(masks);
 }
 vector<set<array<int,6>>> strata(n+1);
 for(int mask=0;mask<1<<n;++mask){
   array<int,6> ar{};
   for(int i=0;i<6;++i)for(int gm:groups[i])ar[i]=max(ar[i],__builtin_popcount((unsigned)(mask&gm)));
   strata[__builtin_popcount((unsigned)mask)].insert(ar);
 }
 auto total=*strata[n].begin();
 // Sum the six shape maxima over all exponent choices, excluding prescribed labels.
 double cnt[]={1.,1.,1.5,1.25,1.25,1.875};  // 3,5 upper digits uniform
 for(int i=0;i<6;++i)head_mean+=total[i]*cnt[i]/n;
 headcost=head_mean;
 for(int i:{0,1,2,3,4})headcost-=total[i]/(double)n;
 auto ap=pmf(3,1),bp=pmf(5,1);
 map<double,double> deltas;
 for(int a=1;a<=10;++a)for(int b=1;b<=10;++b){
  array<int,6> nu={1,1,a,b,b,a*b}; vector<int> cur;
  for(auto& vs:strata){int hi=0;for(auto ar:vs)hi=max(hi,inner_product(ar.begin(),ar.end(),nu.begin(),0)); cur.push_back(hi);}
  // Slopes j/n in ascending order; line intercept (cur[n-j]-cur[n])/n.
  vector<int> lines; vector<double> starts;
  for(int j=0;j<=n;++j){
   double start=-1e10;
   while(!lines.empty()){
    int k=lines.back();
    start=double(cur[n-k]-cur[n-j])/(j-k);
    if(start>starts.back())break;
    lines.pop_back(); starts.pop_back();
   }
   lines.push_back(j);starts.push_back(start);
  }
  int prev=0;
  for(int i=0;i<(int)lines.size();++i){int j=lines[i];if(j>prev)deltas[max(0.,starts[i])]+=ap[a]*bp[b]*(j-prev)/n;prev=j;}
 }
 bk={0};slopes={0};ints={0};
 for(auto [x,d]:deltas){double val=slopes.back()*x+ints.back();bk.push_back(x);slopes.push_back(slopes.back()+d);ints.push_back(val-slopes.back()*x);}
 // Third moment of comonotone single-head masks, computed exactly in a subsequent certificate if promising.
 auto moms=[](double p){
   double r=p-1;return array<double,4>{1.,1+1/r,1+2/r+(p+1)/(r*r),moment((int)p,1.)};
 };
 auto ma=moms(3),mb=moms(5);
 for(int k=1;k<=n;++k) {
  vector<pair<int,int>> v;int aexp[]={0,0,1,0,0,1},bexp[]={0,0,0,1,1,1};
  for(int i=0;i<6;++i)if(k<=total[i])v.emplace_back(aexp[i],bexp[i]);
  for(auto [a,b]:v)for(auto [c,d]:v)for(auto [e,f]:v)head_cube+=ma[a+c+e]*mb[b+d+f]/n;
 }
}
double cost(){
 vector<double> v=src,u(v.size());double mean=1,cube=1,tot=0;
 for(int p:ps){
  double r=p-1.;double d=sch.count(p)?sch[p]/r:.3, g=1/(1-d), t=d*r;
  double z=head_mean*mean-t;
  for(int i=0;i<(int)small.size()&&small[i]<t;++i)z+=small[i]*corr(t/small[i])*v[i];
  tot+=g*z/r;
  advance(v,u,pmf(p,g));mean*=1+g/r;cube*=moment(p,g);
 }
 return headcost+tot+late_coef*cube*head_cube;
}
int main(int argc,char**argv){
 int head_r=argc>1?stoi(argv[1]):1;
 int lower=11;
 vector<char> prime(endp+1,1);
 for(int i=2;i*i<=endp;++i)if(prime[i])for(int j=i*i;j<=endp;j+=i)prime[j]=0;
 double M=1;
 for(int p=lower;p<=endp;++p)if(prime[p]){if(p<=pref)ps.push_back(p);else{
 double r=p-1.;late_coef+=4000./1701*M/(r*r*r); M*=moment(p,10./7);}}
 late_coef+=4000./1701*M/(664578.*664578*169*14);
 for(int n=1;n<=H;++n){int m=n;for(int p:{2,3,5,7})while(m%p==0)m/=p;if(m==1)small.push_back(n);}
 to.resize(11);ix.resize(H+1,-1);for(int i=0;i<(int)small.size();++i)ix[small[i]]=i;
 for(int j=1;j<=10;++j)for(int n:small){if(j*n>H)break;to[j].push_back(ix[j*n]);}
 src.resize(small.size());vector<double> tmp(src.size());src[ix[1]]=1;
 make_kernel(head_r);cout<<"head "<<headcost<<" mean "<<head_mean<<" cube "<<head_cube<<endl;
 for(int p:ps){if(p>73)break;early.push_back(p);}
 double found=cost();cout<<"initial "<<found<<endl;
 if(argc<3)return 0;for(int round=0;round<3;++round){
  for(int p:early){
   int t0=sch.count(p)?sch[p]:roundf(.3*(p-1));int best=t0;double score=found;bool has=sch.count(p);
   for(int t=max(1,t0-3);t<=min((p-1)/2,t0+3);++t){sch[p]=t;double v=cost();if(v<score){score=v;best=t;}}
   if(score<found||has)sch[p]=best;else sch.erase(p);
   found=score;
  }
  cout<<found<<" ";for(auto [p,t]:sch)cout<<p<<'='<<t<<' ';cout<<endl;
 }
}
