#include <algorithm>
#include <bit>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <numeric>
#include <string>
#include <vector>
using namespace std;
using U = uint32_t;
struct Graph { string name; int n, k; vector<pair<int,int>> edges; };
struct DSU {
 vector<int> p, sz, mn;
 explicit DSU(int n): p(n,-1), sz(n,1), mn(n,1000000) {}
 int find(int v) { int r=v; while(p[r]!=r)r=p[r]; while(v!=r){int t=p[v];p[v]=r;v=t;} return r; }
 void join(int u,int v) {u=find(u);v=find(v);if(u==v)return;if(sz[u]<sz[v])swap(u,v);p[v]=u;sz[u]+=sz[v];mn[u]=min(mn[u],mn[v]);}
};
Graph pairs(int t,int k) {
 Graph g{"connected_outside_"+to_string(t)+"_pairs_k"+to_string(k),1+2*t,k,{}};
 for(int b=0;b<t;b++) {
  int u=1+2*b,v=u+1;
  for(int i=0;i<k+1;i++)g.edges.emplace_back(u,v);
  for(int i=0;i<k;i++){g.edges.emplace_back(0,u);g.edges.emplace_back(0,v);}
 }
 for(int b=0;b<t-1;b++)g.edges.emplace_back(2+2*b,3+2*b);
 return g;
}
int main() {
 vector<Graph> gs{pairs(2,2),pairs(3,2),pairs(2,3)};
 Graph star{"three_5_port_stars",4,2,{}};
 for(int v=1;v<=3;v++)for(int j=0;j<5;j++)star.edges.emplace_back(0,v);
 gs.push_back(star);
 ofstream out("review_root_caps.json");out<<"{\"status\":\"PASS\",\"encoding\":\"bit1 means stored u to v; edge list positions are physical identities\",\"graphs\":[";
 bool comma=false;
 for(auto &g:gs) {
  int n=g.n,k=g.k,m=(int)g.edges.size(),full=(1<<n)-1;
  U limit=U(1)<<m;
  vector<U> pos(n),neg(n);vector<int>deg(n);vector<pair<U,U>>cuts;
  for(int i=0;i<m;i++){auto[u,v]=g.edges[i];pos[u]|=U(1)<<i;neg[v]|=U(1)<<i;deg[u]++;deg[v]++;}
  int lambda=m,dense=0;
  for(int s=1;s<full;s++) {
   U cp=0,cn=0;int es=0,ec=0;
   for(int i=0;i<m;i++){auto[u,v]=g.edges[i];bool a=(s>>u)&1,b=(s>>v)&1;if(a&&b)es++;else if(!a&&!b)ec++;else if(a)cp|=U(1)<<i;else cn|=U(1)<<i;}
   lambda=min(lambda,popcount(cp|cn));
   if(s&1){cuts.emplace_back(cp,cn);if(es>k*(popcount((U)s)-1)&&ec>k*(n-popcount((U)s)-1))dense++;}
  }
  auto degree=[&](U s,int v){return popcount(s&pos[v])+popcount((~s)&neg[v]);};
  vector<U>good;vector<int> index(limit,-1);size_t host=0;int eta=m,rmax=0;
  for(U s=0;s<limit;s++) {
   bool ok=true;
   for(int v=0;v<n;v++){int d=degree(s,v);if(d<k||d>deg[v]-k){ok=false;break;}}
   if(!ok)continue;
   host++;
   for(auto[cp,cn]:cuts){int d=popcount(s&cp)+popcount((~s)&cn);if(d<k||d>popcount(cp|cn)-k){ok=false;break;}}
   if(ok){index[s]=(int)good.size();good.push_back(s);int r=degree(s,0);eta=min(eta,r);rmax=max(rmax,r);}
  }
  if(lambda<2*k+1||good.empty()||eta<=k||rmax!=deg[0]-eta)return 2;
  vector<vector<int>>layers(deg[0]+1);
  for(size_t i=0;i<good.size();i++)layers[degree(good[i],0)].push_back((int)i);
  DSU ds((int)good.size());size_t queries=0,nontrivial=0,fail=0;
  vector<U>failure_states;
  U prep_source=0;bool prep_found=false;vector<int>prep_word;
  for(int r=eta;r<=rmax;r++) {
   for(int v:layers[r]){ds.p[v]=v;ds.mn[v]=r;}
   for(int v:layers[r])for(int i=0;i<m;i++){int z=index[good[v]^(U(1)<<i)];if(z>=0&&ds.p[z]>=0)ds.join(v,z);}
   if(r==eta)continue;
   for(int v:layers[r]) {
    queries++;if(r<rmax)nontrivial++;
    if(ds.mn[ds.find(v)]>eta){fail++;if(failure_states.size()<8)failure_states.push_back(good[v]);}
    if(!prep_found&&r<rmax) {
     U s=good[v];bool direct=false;
     for(int i=0;i<m;i++){auto[u,w]=g.edges[i];if(u!=0&&w!=0)continue;U z=s^(U(1)<<i);if(index[z]>=0&&degree(z,0)==r-1){direct=true;break;}}
     if(!direct&&ds.mn[ds.find(v)]==eta){prep_found=true;prep_source=s;}
    }
   }
  }
  int components=0;for(size_t v=0;v<good.size();v++)if(ds.find((int)v)==(int)v)components++;
  if(prep_found) {
   int cap=degree(prep_source,0);vector<int>parent(good.size(),-1),move(good.size(),-1),queue;
   int start=index[prep_source],target=-1;parent[start]=start;queue.push_back(start);
   for(size_t h=0;h<queue.size()&&target<0;h++) {
    int v=queue[h];if(degree(good[v],0)==eta){target=v;break;}
    for(int i=0;i<m;i++){int z=index[good[v]^(U(1)<<i)];if(z>=0&&parent[z]<0&&degree(good[z],0)<=cap){parent[z]=v;move[z]=i;queue.push_back(z);}}
   }
   if(target<0)return 3;
   for(int v=target;v!=start;v=parent[v])prep_word.push_back(move[v]);
   reverse(prep_word.begin(),prep_word.end());
  }
  if(comma)out<<",";
  comma=true;
  out<<"{\"name\":\""<<g.name<<"\",\"n\":"<<n<<",\"k\":"<<k<<",\"m\":"<<m<<",\"lambda\":"<<lambda<<",\"root\":0,\"eta\":"<<eta<<",\"root_max\":"<<rmax<<",\"root_degree\":"<<deg[0]<<",\"osp\":"<<(dense==0?"true":"false")<<",\"orientations_examined\":"<<limit<<",\"vertex_legal\":"<<host<<",\"fully_legal\":"<<good.size()<<",\"good_components\":"<<components<<",\"queries\":"<<queries<<",\"nontrivial_queries\":"<<nontrivial<<",\"failures\":"<<fail<<",\"failure_states\":[";
  for(size_t i=0;i<failure_states.size();i++){if(i)out<<",";out<<failure_states[i];}out<<"],\"edges\":[";
  for(int i=0;i<m;i++){if(i)out<<",";out<<"["<<g.edges[i].first<<","<<g.edges[i].second<<"]";}out<<"],\"preparation_witness\":";
  if(!prep_found)out<<"null";
  else{out<<"{\"start\":"<<prep_source<<",\"cap\":"<<degree(prep_source,0)<<",\"word\":[";for(size_t i=0;i<prep_word.size();i++){if(i)out<<",";out<<prep_word[i];}out<<"]}";}
  out<<"}";out.flush();cerr<<g.name<<": eta="<<eta<<" good="<<good.size()<<" nontrivial="<<nontrivial<<" failures="<<fail<<"\n";
  if(fail)return 4;
 }
 out<<"]}\n";
}
