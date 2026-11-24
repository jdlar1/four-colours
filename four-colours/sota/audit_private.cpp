// Independent degree-labelled induced graph embeddings of configuration interiors.
// High non-hub degrees are realized at 12. Their new fan vertices also have
// degree 12 and cannot be the image of any stock interior vertex.
#include <algorithm>
#include <array>
#include <bit>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <sstream>
#include <string>
#include <vector>
using namespace std;
using Mask=uint64_t;
struct Pattern {vector<int> degree;vector<Mask> adj;vector<vector<int>> rotations;};
struct Wheel {
    int face[62][62]{}; int d;array<int,62> degree{};array<Mask,62> adj{};array<Mask,13> bydegree{};
    void edge(int a,int b){adj[a]|=1ULL<<b;adj[b]|=1ULL<<a;}
    void triangle(int a,int b,int c){edge(a,b);edge(b,c);edge(c,a);face[a][b]=1+c;face[b][c]=1+a;face[c][a]=1+b;}
    void build(){
        for(int i=1;i<=d;i++){
            int next=i%d+1,prev=(i+d-2)%d+1;
            triangle(0,i,next);triangle(next,i,d+i);
            if(degree[i]>8) continue;
            int last=d+prev;
            for(int f=0;f<degree[i]-5;f++){
                int v=(2+f)*d+i;triangle(i,last,v);last=v;
            }
            triangle(i,last,d+i);
        }
        for(int i=0;i<=5*d;i++)if(degree[i]<12 && adj[i])bydegree[degree[i]]|=1ULL<<i;
    }
    bool embed(const Pattern& p,vector<Mask> allowed, Mask assigned,Mask used,array<int,27> mapping)const{
        int best=-1,minimum=100;
        for(int i=0;i<int(allowed.size());i++)if(!(assigned>>i&1)){
            int count=popcount(allowed[i]);
            if(!count)return false;
            if(count<minimum){minimum=count;best=i;}
        }
        if(best<0){
            for(int i=1;i<=d;i++)if(!(used>>i&1) && (used>>(d+i)&1) && (used>>(d+(i+d-2)%d+1)&1))return false;
            for(int orientation=0;orientation<2;orientation++){
                bool ok=true;
                for(int v=0;v<int(mapping.size()) && v<int(p.degree.size());v++){
                    const auto& rot=p.rotations[v];
                    for(int j=0;j<int(rot.size());j++){
                        int u=rot[j],w=rot[(j+1)%rot.size()];
                        if(u<0||w<0)continue;
                        int a=mapping[v],b=mapping[u],c=mapping[w];
                        if(orientation)swap(b,c);
                        if(face[a][b]!=c+1)ok=false;
                    }
                }
                if(ok)return true;
            }
            return false;
        }
        for(Mask m=allowed[best];m;m&=m-1){
            int a=countr_zero(m);
            auto next=allowed;
            for(int j=0;j<int(next.size());j++){
                next[j]&=~(1ULL<<a);
                next[j]&=(p.adj[best]>>j&1)?adj[a]:~adj[a];
            }
            mapping[best]=a;
            if(embed(p,move(next),assigned|1ULL<<best,used|1ULL<<a,mapping))return true;
        }
        return false;
    }
};
int main(int argc,char** argv){
    if(argc!=3 && argc!=4)return 2;
    bool enumerate=argc==4 && string(argv[3])=="--all";
    ifstream conf(argv[1]);string line;
    vector<Pattern> pats;
    while(getline(conf,line)){
        if(line.empty())continue;
        getline(conf,line);istringstream header(line);int n,r;header>>n>>r;
        getline(conf,line);Pattern p;p.degree.resize(n-r);p.adj.resize(n-r);p.rotations.resize(n-r);
        for(int j=1;j<=n;j++){
            getline(conf,line);if(j<=r)continue;
            istringstream in(line);int id,g,v;in>>id>>g;p.degree[j-r-1]=g;
            while(in>>v){p.rotations[j-r-1].push_back(v-r-1);if(v>r)p.adj[j-r-1]|=1ULL<<(v-r-1);}
        }
        int coords=0;
        while(coords<n && getline(conf,line)){istringstream in(line);long point;while(in>>point)coords++;}
        pats.push_back(move(p));
    }
    ifstream witnesses(argv[2]);getline(witnesses,line);
    int total=0,mismatch=0;
    while(getline(witnesses,line)){
        istringstream rec(line);Wheel w;
        int id,q;rec>>id>>w.d>>q;
        for(int j=0;j<=5*w.d;j++){int lo,hi;rec>>lo>>hi;w.degree[j]=hi;}
        if(!rec)return 5;
        w.build();vector<int> hits;
        for(int i=0;i<int(pats.size());i++){
            if(any_of(pats[i].degree.begin(),pats[i].degree.end(),[&](int g){return !w.bydegree[g];})) continue;
            vector<Mask> allowed;
            for(int g:pats[i].degree)allowed.push_back(w.bydegree[g]);
            if(w.embed(pats[i],move(allowed),0,0,{}))hits.push_back(i+1);
        }
        if(enumerate){cout<<id<<" 0 "<<q;for(int i:hits)cout<<" "<<i;cout<<"\n";}
        else if(hits!=vector<int>{id}){
            mismatch++;cout<<"Witness "<<id<<" graph matches";for(int i:hits)cout<<" "<<i;cout<<"\n";
        }
        total++;
    }
    if(!enumerate)cout<<total<<" witnesses, "<<pats.size()<<" patterns, "<<mismatch<<" mismatches\n";
    return mismatch!=0;
}
