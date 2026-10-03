// Independent finite-domain search for 8+9 fan-free gluings.
// No SAT library or production solver code. Missing cross edges are unknown,
// and occur in neither colour of the partial graph.
#include <algorithm>
#include <array>
#include <bitset>
#include <chrono>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <map>
#include <string>
#include <vector>
#include "vendor/nlohmann/json.hpp"
using json = nlohmann::json;
using Mask = uint32_t;
using Graph = std::array<Mask,17>;
using Bits = std::bitset<512>;
int pc(Mask x) { int n=0; while(x){x&=x-1;++n;}return n; }
int low(Mask x) { int n=0;while(!(x&1)){x>>=1;++n;}return n; }
bool matching(const Graph& g, Mask m, int need) {
    if(!need)return true; if(pc(m)<2*need)return false;
    int best=-1,degree=100; Mask tmp=m;
    while(tmp){int v=low(tmp);tmp&=tmp-1;int d=pc(g[v]&m);if(d<degree){degree=d;best=v;if(!d)break;}}
    Mask rest=m^(1u<<best),choices=g[best]&rest;
    while(choices){Mask b=choices&-choices;choices^=b;if(matching(g,rest^b,need-1))return true;}
    return matching(g,rest,need);
}
bool valid(const Graph& r,const Graph& b) {
    for(int v=0;v<17;++v)if(matching(r,r[v],3)||matching(b,b[v],4))return false;
    return true;
}
bool matchingWitness(const Graph&g,Mask m,int need,std::vector<int>&edges){
    if(!need)return true;if(pc(m)<2*need)return false;int v=low(m);Mask rest=m^(1u<<v),choices=g[v]&rest;
    while(choices){Mask bit=choices&-choices;choices^=bit;edges.push_back(v);edges.push_back(low(bit));if(matchingWitness(g,rest^bit,need-1,edges))return true;edges.pop_back();edges.pop_back();}
    return matchingWitness(g,rest,need,edges);
}
json fanWitness(const Graph&r,const Graph&b){for(int c=0;c<2;++c)for(int v=0;v<17;++v){std::vector<int>edges;const Graph&g=c?b:r;if(matchingWitness(g,g[v],c?4:3,edges))return json::array({c,v,edges});}throw std::runtime_error("Requested absent fan witness");}
struct State { std::array<Bits,8> row;std::array<Bits,9> col; };
struct Search {
    Graph baseR{},baseB{};std::array<int,8> da{};std::array<int,9> db{};
    std::array<Mask,8> a{};std::array<Mask,9>b{};
    std::vector<Bits> pair;std::vector<Bits> rc,cr;
    std::array<std::array<bool,8>,8> twins{};
    std::chrono::steady_clock::time_point began;double limit=60;
    uint64_t nodes=0,failures=0,pairChecks=0;bool timeout=false;std::array<int,8>witness{};
    bool certify=false;json certificate;std::map<uint32_t,json>pairProofs;
    bool expired(){if(std::chrono::duration<double>(std::chrono::steady_clock::now()-began).count()>limit){timeout=true;return true;}return false;}
    Bits& pairs(int i,int m,int k){return pair[(i*512+m)*8+k];}
    Bits& rowcols(int i,int m,int j){return rc[(i*512+m)*9+j];}
    Bits& colrows(int j,int m,int i){return cr[(j*256+m)*8+i];}
    void addRow(Graph&r,Graph&bl,int i,int m){for(int j=0;j<9;++j){auto&g=(m>>j&1)?r:bl;g[i]|=1u<<(8+j);g[8+j]|=1u<<i;}}
    void addCol(Graph&r,Graph&bl,int j,int m){for(int i=0;i<8;++i){auto&g=(m>>i&1)?r:bl;g[i]|=1u<<(8+j);g[8+j]|=1u<<i;}}
    void provePair(int i,int m,int k,int q){if(i>k){std::swap(i,k);std::swap(m,q);}uint32_t key=(((i*512u+m)*8u+k)*512u+q);if(pairProofs.count(key))return;Graph r=baseR,bl=baseB;addRow(r,bl,i,m);addRow(r,bl,k,q);pairProofs[key]=fanWitness(r,bl);}
    Search(const json& input,double secs,bool symmetry=true):limit(secs){
        a=input.at("left_red").get<std::array<Mask,8>>();b=input.at("right_red").get<std::array<Mask,9>>();
        for(int i=0;i<8;++i){baseR[i]=a[i];baseB[i]=255u^(1u<<i)^a[i];da[i]=pc(a[i]);}
        for(int j=0;j<9;++j){baseR[8+j]=b[j]<<8;baseB[8+j]=(511u^(1u<<j)^b[j])<<8;db[j]=pc(b[j]);}
        for(int i=0;i<8;++i)for(int k=i+1;k<8;++k)twins[i][k]=symmetry&&((a[i]&~(1u<<k))==(a[k]&~(1u<<i)));
        pair.resize(8*512*8);rc.resize(8*512*9);cr.resize(9*256*8);
        began=std::chrono::steady_clock::now();
    }
    bool prepare(State&s){
        if(certify){certificate["initial_rejections"]=json::array();certificate["initial_rows"]=json::array();certificate["initial_columns"]=json::array();}
        for(int i=0;i<8;++i)for(int m=0;m<512;++m)if(7<=da[i]+pc(m)&&da[i]+pc(m)<=10){Graph r=baseR,bl=baseB;addRow(r,bl,i,m);if(valid(r,bl))s.row[i].set(m);else if(certify)certificate["initial_rejections"].push_back(json::array({0,i,m,fanWitness(r,bl)}));}
        for(int j=0;j<9;++j)for(int m=0;m<256;++m)if(7<=db[j]+pc(m)&&db[j]+pc(m)<=10){Graph r=baseR,bl=baseB;addCol(r,bl,j,m);if(valid(r,bl))s.col[j].set(m);else if(certify)certificate["initial_rejections"].push_back(json::array({1,j,m,fanWitness(r,bl)}));}
        if(certify){for(int i=0;i<8;++i){json d=json::array();for(int m=0;m<512;++m)if(s.row[i][m])d.push_back(m);certificate["initial_rows"].push_back(d);}for(int j=0;j<9;++j){json d=json::array();for(int m=0;m<256;++m)if(s.col[j][m])d.push_back(m);certificate["initial_columns"].push_back(d);}}
        for(int i=0;i<8;++i)for(int m=0;m<512;++m)if(s.row[i][m])for(int j=0;j<9;++j)for(int q=0;q<256;++q)if(s.col[j][q]){
            int bit=m>>j&1;if(bit==(q>>i&1)&&pc(m)+pc(q)-2*bit>=da[i]+db[j]){rowcols(i,m,j).set(q);colrows(j,q,i).set(m);}}
        for(int i=0;i<8;++i)for(int k=i+1;k<8;++k)for(int m=0;m<512;++m)if(s.row[i][m]){
            if(expired())return false;
            for(int q=0;q<512;++q)if(s.row[k][q]&&(!twins[i][k]||m<=q)){
                Graph r=baseR,bl=baseB;addRow(r,bl,i,m);addRow(r,bl,k,q);++pairChecks;
                if(valid(r,bl)){pairs(i,m,k).set(q);pairs(k,q,i).set(m);}
            }
        }return true;
    }
    bool propagate(State&s,json*trace=nullptr){bool change=true;while(change){change=false;
        for(int i=0;i<8;++i){if(s.row[i].none())return false;for(int m=0;m<512;++m)if(s.row[i][m]){
            bool good=true;int reason=-1,target=-1;for(int k=0;k<8&&good;++k)if(k!=i){good=(pairs(i,m,k)&s.row[k]).any();if(!good){reason=0;target=k;if(trace)for(int q=0;q<512;++q)if(s.row[k][q])provePair(i,m,k,q);}}
            for(int j=0;j<9&&good;++j){good=(rowcols(i,m,j)&s.col[j]).any();if(!good){reason=1;target=j;}}
            if(!good&&trace)(*trace)["deletions"].push_back(json::array({0,i,m,reason,target}));
            if(!good){s.row[i].reset(m);change=true;}
        }if(s.row[i].none())return false;}
        for(int j=0;j<9;++j){if(s.col[j].none())return false;for(int m=0;m<256;++m)if(s.col[j][m]){
            bool good=true;int target=-1;for(int i=0;i<8&&good;++i){good=(colrows(j,m,i)&s.row[i]).any();if(!good)target=i;}
            if(!good&&trace)(*trace)["deletions"].push_back(json::array({1,j,m,1,target}));
            if(!good){s.col[j].reset(m);change=true;}
        }if(s.col[j].none())return false;}
    }return true;}
    bool dfs(State s,json*trace=nullptr){++nodes;if(trace)(*trace)["deletions"]=json::array();if((nodes&255)==1&&expired())return false;
        if(!propagate(s,trace)){++failures;if(trace)(*trace)["kind"]="empty";return false;}
        Graph r=baseR,bl=baseB;int chosen=-1,best=513;
        for(int i=0;i<8;++i){int size=int(s.row[i].count());if(size==1){for(int m=0;m<512;++m)if(s.row[i][m]){addRow(r,bl,i,m);witness[i]=m;break;}}else if(size<best){best=size;chosen=i;}}
        // Fans with three or more known rows are tested here, independently of
        // the binary compatibility tables. Unassigned cross edges remain absent.
        if(!valid(r,bl)){++failures;if(trace){(*trace)["kind"]="fan";(*trace)["fan"]=fanWitness(r,bl);}return false;}
        if(chosen<0)return true;
        if(trace){(*trace)["kind"]="branch";(*trace)["row"]=chosen;(*trace)["children"]=json::array();}
        for(int m=0;m<512;++m)if(s.row[chosen][m]){State child=s;child.row[chosen].reset();child.row[chosen].set(m);json childTrace;bool found=dfs(child,trace?&childTrace:nullptr);if(trace)(*trace)["children"].push_back(json::array({m,childTrace}));if(found)return true;if(timeout)return false;}
        return false;
    }
    json run(){State s;bool ready=prepare(s);json out;out["pair_checks"]=pairChecks;out["row_domain_sizes"]=json::array();out["column_domain_sizes"]=json::array();for(auto&d:s.row)out["row_domain_sizes"].push_back(d.count());for(auto&d:s.col)out["column_domain_sizes"].push_back(d.count());
        json tree;bool sat=ready&&dfs(s,certify?&tree:nullptr);out["status"]=sat?"SAT":timeout?"UNKNOWN":"UNSAT";out["nodes"]=nodes;out["failures"]=failures;out["wall_seconds"]=std::chrono::duration<double>(std::chrono::steady_clock::now()-began).count();if(sat)out["cross_rows"]=witness;
        if(certify&&!sat&&!timeout){certificate["tree"]=tree;certificate["pair_rejections"]=json::array();for(const auto&p:pairProofs)certificate["pair_rejections"].push_back(json::array({p.first,p.second}));certificate["schema"]="fan17-csp-certificate-1";out["certificate_pairs"]=pairProofs.size();}return out;}
};
int main(int argc,char**argv){if(argc<3){std::cerr<<"Usage: csp_rows CASES_JSON REPORT_JSON [SECONDS=60] [CASE_ID=-1] [SYMMETRY=on]\n";return 2;}try{
    std::ifstream in(argv[1]);json cases;in>>cases;double seconds=argc>3?std::stod(argv[3]):60;long long wanted=argc>4?std::stoll(argv[4]):-1;json results=json::array();
    bool symmetry=argc<6||std::string(argv[5])!="off";
    bool certify=argc>6;if(certify&&symmetry)throw std::runtime_error("Certificates require symmetry off");
    for(const auto&item:cases){long long id=item.at("case_id");if(wanted>=0&&id!=wanted)continue;Search search(item,seconds,symmetry);search.certify=certify;json r=search.run();r["case_id"]=id;r["method"]="Independent finite-domain CSP with partial-graph fan scans, row/column degree domains and balanced-cut swaps";r["twin_row_symmetry"]=symmetry;r["proof_verified"]=false;if(certify&&r["status"]=="UNSAT"){search.certificate["case_id"]=id;search.certificate["left_red"]=item["left_red"];search.certificate["right_red"]=item["right_red"];std::string path=std::string(argv[6])+"_"+std::to_string(id)+".json";std::ofstream cert(path);cert<<search.certificate.dump()<<"\n";r["certificate_path"]=path;}results.push_back(r);std::cout<<r.dump()<<std::endl;std::ofstream out(argv[2]);out<<results.dump(2)<<"\n";}
}catch(const std::exception&e){std::cerr<<e.what()<<"\n";return 1;}return 0;}
