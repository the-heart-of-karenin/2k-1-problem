#include <algorithm>
#include <bit>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <vector>
using namespace std;
using U=uint32_t;
int main() {
 const int n=8,k=2;
 vector<pair<int,int>>edges;
 for(int base:{0,4}) {
  for(int u=0;u<4;u++)for(int v=u+1;v<4;v++)edges.emplace_back(base+u,base+v);
  edges.emplace_back(base,base+1);edges.emplace_back(base+2,base+3);
 }
 for(int i=0;i<4;i++)for(int j=0;j<(i==0?1:2);j++)edges.emplace_back(i,i+4);
 const int m=(int)edges.size(),full=(1<<n)-1;
 const U limit=U(1)<<m;
 vector<U>pos(n),neg(n);vector<int>deg(n);
 for(int i=0;i<m;i++){auto[u,v]=edges[i];pos[u]|=U(1)<<i;neg[v]|=U(1)<<i;deg[u]++;deg[v]++;}
 vector<pair<U,U>>cuts;
 int lambda=m;
 for(int s=1;s<full;s++) {
  U cp=0,cn=0;
  for(int i=0;i<m;i++){auto[u,v]=edges[i];bool a=(s>>u)&1,b=(s>>v)&1;if(a&&!b)cp|=U(1)<<i;else if(b&&!a)cn|=U(1)<<i;}
  lambda=min(lambda,popcount(cp|cn));
  if(s&1)cuts.emplace_back(cp,cn);
 }
 vector<unsigned char>flag(limit,0);
 size_t host=0,good=0;
 for(U s=0;s<limit;s++) {
  bool ok=true;
  for(int v=0;v<n;v++){int d=popcount(s&pos[v])+popcount((~s)&neg[v]);if(d<k||d>deg[v]-k){ok=false;break;}}
  if(!ok)continue;
  host++;
  for(auto[cp,cn]:cuts){int d=popcount(s&cp)+popcount((~s)&cn);if(d<k||d>popcount(cp|cn)-k){ok=false;break;}}
  flag[s]=ok?1:2;if(ok)good++;
 }
 vector<int>badLabel(limit,-1),member(limit,-1),seen(limit,-1);
 vector<U>queue,boundary,firstBoundary;
 struct Row{size_t bad,boundary;int induced;};vector<Row>rows;
 U witnessA=0,witnessB=0,witnessBad=0;bool found=false;
 size_t disconnected=0;
 for(U s=0;s<limit;s++)if(flag[s]==2&&badLabel[s]<0) {
  int id=(int)rows.size();queue.clear();boundary.clear();queue.push_back(s);badLabel[s]=id;
  for(size_t h=0;h<queue.size();h++)for(int i=0;i<m;i++) {
   U t=queue[h]^(U(1)<<i);
   if(flag[t]==2&&badLabel[t]<0){badLabel[t]=id;queue.push_back(t);}
   else if(flag[t]==1)boundary.push_back(t);
  }
  size_t badSize=queue.size();
  sort(boundary.begin(),boundary.end());boundary.erase(unique(boundary.begin(),boundary.end()),boundary.end());
  for(U v:boundary)member[v]=id;
  int components=0;U a=0,b=0;
  for(U v:boundary)if(seen[v]!=id) {
   if(components==0)a=v;else if(components==1)b=v;
   components++;queue.clear();queue.push_back(v);seen[v]=id;
   for(size_t h=0;h<queue.size();h++)for(int i=0;i<m;i++) {
    U t=queue[h]^(U(1)<<i);
    if(member[t]==id&&seen[t]!=id){seen[t]=id;queue.push_back(t);}
   }
  }
  if(components>1){disconnected++;if(!found){found=true;witnessA=a;witnessB=b;witnessBad=s;firstBoundary=boundary;}}
  rows.push_back({badSize,boundary.size(),components});
 }
 if(lambda!=5||host!=905572||good!=872436||rows.size()!=122||!found)return 2;
 // An actual legal word across two different components of the immediate boundary.
 vector<int>parent(limit,-1);vector<unsigned char>move(limit,0);
 queue.clear();queue.push_back(witnessA);parent[witnessA]=witnessA;
 for(size_t h=0;h<queue.size()&&parent[witnessB]<0;h++)for(int i=0;i<m;i++) {
  U t=queue[h]^(U(1)<<i);
  if(flag[t]==1&&parent[t]<0){parent[t]=queue[h];move[t]=(unsigned char)i;queue.push_back(t);}
 }
 if(parent[witnessB]<0)return 3;
 vector<int>word;for(U v=witnessB;v!=witnessA;v=parent[v])word.push_back(move[v]);reverse(word.begin(),word.end());
 vector<U>states{witnessA};vector<int>onBoundary{1};U v=witnessA;bool left=false;
 for(int i:word){v^=U(1)<<i;states.push_back(v);bool in=binary_search(firstBoundary.begin(),firstBoundary.end(),v);onBoundary.push_back(in);if(!in)left=true;}
 if(!left||v!=witnessB)return 4;
 ofstream out("review_bad_boundary.json");
 out<<"{\"status\":\"PASS\",\"graph\":\"two_dense_K4_odd\",\"encoding\":\"bit1 stored u to v\",\"n\":8,\"m\":23,\"k\":2,\"lambda\":5,\"host\":"<<host<<",\"fully_legal\":"<<good<<",\"bad_components\":"<<rows.size()<<",\"bad_components_with_disconnected_immediate_legal_boundary\":"<<disconnected<<",\"rows\":[";
 for(size_t i=0;i<rows.size();i++){if(i)out<<",";out<<"{\"id\":"<<i<<",\"bad_size\":"<<rows[i].bad<<",\"boundary_size\":"<<rows[i].boundary<<",\"boundary_induced_components\":"<<rows[i].induced<<"}";}
 out<<"],\"witness\":{\"bad_representative\":"<<witnessBad<<",\"start\":"<<witnessA<<",\"target\":"<<witnessB<<",\"word\":[";
 for(size_t i=0;i<word.size();i++){if(i)out<<",";out<<word[i];}out<<"],\"states\":[";
 for(size_t i=0;i<states.size();i++){if(i)out<<",";out<<states[i];}out<<"],\"on_immediate_boundary\":[";
 for(size_t i=0;i<onBoundary.size();i++){if(i)out<<",";out<<(onBoundary[i]?"true":"false");}out<<"]},\"edges\":[";
 for(int i=0;i<m;i++){if(i)out<<",";out<<"["<<edges[i].first<<","<<edges[i].second<<"]";}out<<"]}\n";
 cerr<<"bad components="<<rows.size()<<"; disconnected boundaries="<<disconnected<<"; legal detour length="<<word.size()<<"\n";
}
