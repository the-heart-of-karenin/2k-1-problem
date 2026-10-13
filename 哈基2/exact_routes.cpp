#include <algorithm>
#include <bit>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <numeric>
#include <string>
#include <tuple>
#include <vector>
using namespace std;
using U = uint32_t;
struct Graph { string name; int n,k; vector<pair<int,int>> edges; };
struct DSU {
 vector<int> p,sz,mn;
 explicit DSU(int n):p(n,-1),sz(n,1),mn(n,1000000){}
 int find(int x){int r=x;while(p[r]!=r)r=p[r];while(x!=r){int t=p[x];p[x]=r;x=t;}return r;}
 void join(int a,int b){a=find(a);b=find(b);if(a==b)return;if(sz[a]<sz[b])swap(a,b);p[b]=a;sz[a]+=sz[b];mn[a]=min(mn[a],mn[b]);}
};
int main(int argc,char**argv){
 string output=argc>1?argv[1]:"exact_results.json";
 vector<Graph> graphs;
 Graph a{"K6",6,2,{}};for(int i=0;i<6;i++)for(int j=i+1;j<6;j++)a.edges.emplace_back(i,j);graphs.push_back(a);
 a.name="K6_plus_three_root_edges";a.edges.insert(a.edges.end(),{{0,1},{0,2},{0,3}});graphs.push_back(a);
 Graph b{"three_dense_pairs_odd",6,2,{}};for(int i=0;i<6;i+=2)for(int j=0;j<3;j++)b.edges.emplace_back(i,i+1);
 b.edges.insert(b.edges.end(),{{0,2},{1,3},{2,4},{3,5},{2,5},{4,0},{5,1},{4,1}});graphs.push_back(b);
 Graph b3{"three_dense_pairs_k3",6,3,{}};for(int i=0;i<6;i+=2)for(int j=0;j<4;j++)b3.edges.emplace_back(i,i+1);for(int i=0;i<6;i++)for(int j=i+1;j<6;j++)if(i/2!=j/2&&!(i==0&&j==2))b3.edges.emplace_back(i,j);graphs.push_back(b3);
 Graph shadow{"root_shadow_control_k2",4,2,{}};for(auto[u,v,copies]:vector<tuple<int,int,int>>{{0,1,3},{0,2,3},{0,3,2},{1,3,2},{2,3,2}})for(int j=0;j<copies;j++)shadow.edges.emplace_back(u,v);graphs.push_back(shadow);
 Graph c{"K5_plus_cycle",5,2,{}};for(int i=0;i<5;i++)for(int j=i+1;j<5;j++)c.edges.emplace_back(i,j);for(int i=0;i<5;i++)c.edges.emplace_back(i,(i+1)%5);graphs.push_back(c);
 Graph d{"C8_square_plus_opposites",8,2,{}};for(int i=0;i<8;i++){d.edges.emplace_back(i,(i+1)%8);d.edges.emplace_back(i,(i+2)%8);}for(int i=0;i<4;i++)d.edges.emplace_back(i,i+4);graphs.push_back(d);
 Graph e{"K8_minus_cycle",8,2,{}};for(int i=0;i<8;i++)for(int j=i+1;j<8;j++)if(j-i!=1&&!(i==0&&j==7))e.edges.emplace_back(i,j);graphs.push_back(e);
 Graph e2{"two_dense_K4_odd",8,2,{}};for(int base:{0,4}){for(int i=0;i<4;i++)for(int j=i+1;j<4;j++)e2.edges.emplace_back(base+i,base+j);e2.edges.emplace_back(base,base+1);e2.edges.emplace_back(base+2,base+3);}for(int i=0;i<4;i++)for(int j=0;j<(i==0?1:2);j++)e2.edges.emplace_back(i,i+4);graphs.push_back(e2);
 Graph f{"two_K5_with_matching",10,2,{}};for(int base:{0,5})for(int i=0;i<5;i++)for(int j=i+1;j<5;j++)f.edges.emplace_back(base+i,base+j);for(int i=0;i<5;i++)f.edges.emplace_back(i,i+5);graphs.push_back(f);
 ofstream out(output);out<<"{\"encoding\":\"bit1 is stored u to v; parallel positions are distinct\",\"graphs\":[";
 bool comma=false;
 for(auto &g:graphs){
  int n=g.n,k=g.k,m=(int)g.edges.size();U limit=U(1)<<m;int all=(1<<n)-1;
  vector<U>pos(n),neg(n);vector<int>deg(n),internal(1<<n);vector<pair<U,U>>cuts;
  for(int i=0;i<m;i++){auto[u,v]=g.edges[i];pos[u]|=U(1)<<i;neg[v]|=U(1)<<i;deg[u]++;deg[v]++;}
  int lambda=m,dense_constraints=0;
  for(int x=1;x<all;x++){
   U cp=0,cn=0;int ex=0,ey=0;
   for(int i=0;i<m;i++){auto[u,v]=g.edges[i];bool iu=(x>>u)&1,iv=(x>>v)&1;if(iu&&iv)ex++;else if(!iu&&!iv)ey++;else if(iu)cp|=U(1)<<i;else cn|=U(1)<<i;}
   internal[x]=ex;lambda=min(lambda,popcount(cp|cn));
   if(!(x&1))continue;
   if(ex>k*(popcount((U)x)-1)&&ey>k*(n-popcount((U)x)-1)){cuts.emplace_back(cp,cn);dense_constraints++;}
  }
  auto degree=[&](U s,int v){return popcount(s&pos[v])+popcount((~s)&neg[v]);};
  vector<unsigned char>flag(limit,0);vector<U>good,host;
  for(U s=0;s<limit;s++){
   bool ok=true;for(int v=0;v<n;v++){int q=degree(s,v);if(q<k||q>deg[v]-k){ok=false;break;}}
   if(!ok)continue;
   host.push_back(s);ok=true;
   for(auto[cp,cn]:cuts){int q=popcount(s&cp)+popcount((~s)&cn);int dc=popcount(cp|cn);if(q<k||q>dc-k){ok=false;break;}}
   flag[s]=ok?1:2;if(ok)good.push_back(s);
  }
  vector<int>label(limit,-1);vector<U>queue;int good_components=0;vector<size_t>good_sizes;
  for(U s:good)if(label[s]==-1){queue.clear();queue.push_back(s);label[s]=good_components;for(size_t h=0;h<queue.size();h++){U u=queue[h];for(int i=0;i<m;i++){U v=u^(U(1)<<i);if(flag[v]==1&&label[v]==-1){label[v]=good_components;queue.push_back(v);}}}good_sizes.push_back(queue.size());good_components++;}
  size_t bad_components=0,max_bad=0,bad_without_legal_neighbor=0;vector<size_t>bad_sizes;size_t boundary_conflicts=0;U bad_no_neighbor_witness=0;
  for(U s:host)if(flag[s]==2){int neighbors=0;for(int i=0;i<m;i++)if(flag[s^(U(1)<<i)]==1)neighbors++;if(!neighbors){bad_without_legal_neighbor++;bad_no_neighbor_witness=s;}}
  for(U s:host)if(flag[s]==2&&label[s]==-1){queue.clear();queue.push_back(s);label[s]=-2;vector<int>boundary;for(size_t h=0;h<queue.size();h++){U u=queue[h];for(int i=0;i<m;i++){U v=u^(U(1)<<i);if(flag[v]==2&&label[v]==-1){label[v]=-2;queue.push_back(v);}else if(flag[v]==1)boundary.push_back(label[v]);}}sort(boundary.begin(),boundary.end());boundary.erase(unique(boundary.begin(),boundary.end()),boundary.end());if(boundary.size()>1)boundary_conflicts++;bad_components++;max_bad=max(max_bad,queue.size());bad_sizes.push_back(queue.size());}
  // Root-height cap audit: only graphs with some degree > 2k+1 are informative.
  fill(label.begin(),label.end(),-1);for(size_t j=0;j<good.size();j++)label[good[j]]=(int)j;
  size_t root_queries=0,root_failures=0,root_nontrivial_queries=0;vector<tuple<int,int,U,int,int>>root_witnesses;vector<int>eta(n);
  for(int v=0;v<n;v++){eta[v]=m;for(U s:good)eta[v]=min(eta[v],degree(s,v));if(deg[v]<=2*k+1)continue;
   vector<vector<int>>layers(deg[v]+1);for(size_t j=0;j<good.size();j++)layers[degree(good[j],v)].push_back((int)j);
   DSU ds((int)good.size());
   for(int r=eta[v];r<=deg[v]-k;r++){
    for(int j:layers[r]){ds.p[j]=j;ds.mn[j]=r;}
    for(int j:layers[r])for(int i=0;i<m;i++){int z=label[good[j]^(U(1)<<i)];if(z>=0&&ds.p[z]>=0)ds.join(j,z);}
    if(r<=eta[v])continue;
    for(int j:layers[r]){root_queries++;if(r<deg[v]-eta[v])root_nontrivial_queries++;int best=ds.mn[ds.find(j)];if(best>eta[v]){root_failures++;if(root_witnesses.size()<8)root_witnesses.emplace_back(v,r,good[j],best,eta[v]);}}
   }
  }
  // A genuine Hamming trap, followed by an unrestricted shortest physical word.
  U trap_start=0,trap_target=0;bool found_trap=false;vector<int>trap_word;
  if(g.name=="K6"){
   for(U s:good){U blocked=0;for(int i=0;i<m;i++)if(flag[s^(U(1)<<i)]!=1)blocked|=U(1)<<i;
    for(U t=blocked;t;t=(t-1)&blocked){if(popcount(t)>=2&&flag[s^t]==1){trap_start=s;trap_target=s^t;found_trap=true;break;}}
    if(found_trap)break;
   }
   if(found_trap){vector<int>parent(limit,-1),move(limit,-1);queue.clear();queue.push_back(trap_start);parent[trap_start]=trap_start;for(size_t h=0;h<queue.size()&&parent[trap_target]<0;h++){U u=queue[h];for(int i=0;i<m;i++){U z=u^(U(1)<<i);if(flag[z]==1&&parent[z]<0){parent[z]=u;move[z]=i;queue.push_back(z);}}}for(U z=trap_target;z!=trap_start;z=parent[z])trap_word.push_back(move[z]);reverse(trap_word.begin(),trap_word.end());}
  }
  if(comma)out<<",";
  comma=true;
  out<<"{\"name\":\""<<g.name<<"\",\"n\":"<<n<<",\"k\":"<<k<<",\"m\":"<<m<<",\"lambda\":"<<lambda<<",\"edges\":[";
  for(int i=0;i<m;i++){if(i)out<<",";out<<"["<<g.edges[i].first<<","<<g.edges[i].second<<"]";}out<<"],\"dense_cut_constraints\":"<<dense_constraints<<",\"orientations_examined\":"<<limit<<",\"vertex_legal\":"<<host.size()<<",\"fully_legal\":"<<good.size()<<",\"good_components\":"<<good_components<<",\"good_component_sizes\":[";
  for(size_t i=0;i<good_sizes.size();i++){if(i)out<<",";out<<good_sizes[i];}out<<"],\"bad_components\":"<<bad_components<<",\"largest_bad_component\":"<<max_bad<<",\"bad_vertices_without_legal_neighbor\":"<<bad_without_legal_neighbor<<",\"bad_no_neighbor_witness\":"<<bad_no_neighbor_witness<<",\"bad_boundary_component_conflicts\":"<<boundary_conflicts<<",\"root_cap_queries\":"<<root_queries<<",\"root_cap_failures\":"<<root_failures<<",\"eta_by_root\":[";
  for(int i=0;i<n;i++){if(i)out<<",";out<<eta[i];}out<<"],\"root_cap_nontrivial_queries\":"<<root_nontrivial_queries<<",\"root_cap_witnesses\":[";
  for(size_t i=0;i<root_witnesses.size();i++){if(i)out<<",";auto[v,r,s,best,emin]=root_witnesses[i];out<<"{\"root\":"<<v<<",\"cap\":"<<r<<",\"state\":"<<s<<",\"min_reachable\":"<<best<<",\"global_min\":"<<emin<<"}";}out<<"]";
  if(found_trap){out<<",\"hamming_trap\":{\"start\":"<<trap_start<<",\"target\":"<<trap_target<<",\"hamming\":"<<popcount(trap_start^trap_target)<<",\"shortest_word\":[";for(size_t i=0;i<trap_word.size();i++){if(i)out<<",";out<<trap_word[i];}out<<"]}";}
  out<<"}";out.flush();cerr<<g.name<<": host="<<host.size()<<" good="<<good.size()<<" good_components="<<good_components<<" bad_components="<<bad_components<<" root_failures="<<root_failures<<"\n";
 }
 out<<"]}\n";
}
