#include <algorithm>
#include <cmath>
#include <cstdint>
#include <iostream>
#include <vector>
using I=std::int64_t;
I bound, prefixes=0, trials=0, hits=0;
std::vector<int> primes, factors;
std::vector<bool> prime;
bool fits(I v, I p, int e){
  for(int j=0;j<e;++j){if(v>bound/p)return false;v*=p;}
  return true;
}
int inv(int n,int p){
  int a=n,b=p,c=1,d=0;
  while(b){int q=a/b;int t=a-q*b;a=b;b=t;t=c-q*d;c=d;d=t;}
  return (c%p+p)%p;
}
bool good(I n,int p){
  I q=n/p;
  bool split=(n-1)%(p-1)==0, nonsplit=(n-1)%(p+1)==0;
  if(split==nonsplit)return false;
  return split?q%p==1:q%p==p-1;
}
void search(int i,int left,I product){
  if(left>1){
    for(int j=i;j<(int)primes.size() && fits(product,primes[j],left);++j){
      factors.push_back(primes[j]);search(j+1,left-1,product*primes[j]);factors.pop_back();
    }
    return;
  }
  ++prefixes;
  int lo=factors.back()+1;
  int hi=std::min({bound/product, (I)std::sqrt((long double)product+1)+2,(I)prime.size()-1});
  if(hi<lo)return;
  // Modulo each previously selected a, the remaining p must satisfy
  // (product/a)*p = +1 or -1 (mod a). Jump through four CRT classes.
  int a=factors[factors.size()-1], b=factors[factors.size()-2];
  int u=inv((product/a)%a,a), v=inv((product/b)%b,b), ai=inv(a%b,b), ab=a*b;
  for(int av:{u,a-u})for(int bv:{v,b-v}){
    int c=av+a*((((bv-av)%b+b)%b*ai)%b);
    int start=c<lo?c+((lo-c+ab-1)/ab)*ab:c;
    for(int p=start;p<=hi;p+=ab){
      ++trials;
      if(!prime[p])continue;
      I n=product*p;
      if(!good(n,p))continue;
      bool accept=true;
      for(int f:factors)if(!good(n,f)){accept=false;break;}
      if(accept){++hits;std::cout<<"composite "<<n<<"\n";}
    }
  }
}
int main(int argc,char**argv){
  bound=std::stoll(argv[1]);
  int maxp=(int)std::cbrt((long double)bound)+4;
  prime.assign(maxp+1,true);prime[0]=prime[1]=false;
  for(int p=2;p<=maxp;++p)if(prime[p]){
    if(p!=2)primes.push_back(p);
    if(p<=maxp/p)for(int j=p*p;j<=maxp;j+=p)prime[j]=false;
  }
  I smallest=1;
  for(int t=1;smallest<=bound/primes[t-1];++t){
    smallest*=primes[t-1];
    if(t>=4)search(0,t,1);
  }
  std::cout<<"bound "<<bound<<" prefixes "<<prefixes<<" trials "<<trials<<" hits "<<hits<<"\n";
}
