#pragma once
#include "fan_solver.hpp"
#include "catalog_identity.hpp"
#include "vendor/nlohmann/json.hpp"
#include <algorithm>
#include <array>
#include <filesystem>
#include <fstream>
#include <iomanip>
#include <map>
#include <memory>
#include <mutex>
#include <sstream>
#include <stdexcept>
#include <string>
#include <vector>

namespace fan_cli {
using json=nlohmann::json;
namespace fs=std::filesystem;
inline constexpr const char* ENGINE="fan17-cpp-1";
inline std::string bytes(const fs::path& path) {
    std::ifstream f(path,std::ios::binary);
    if(!f)throw std::runtime_error("Cannot read "+path.u8string());
    std::ostringstream s;s<<f.rdbuf();
    if(!f.good()&&!f.eof())throw std::runtime_error("Read failed: "+path.u8string());
    return s.str();
}
inline std::uint64_t fnv(const std::string& s,std::uint64_t h=14695981039346656037ULL) {
    for(unsigned char c:s){h^=c;h*=1099511628211ULL;}return h;
}
inline std::string hexhash(std::uint64_t x) {
    std::ostringstream s;s<<std::hex<<std::setfill('0')<<std::setw(16)<<x;return s.str();
}
struct Profile {
    // Delta, e, lower/upper cross sums, support, allowed, max-root nu, zero flags.
    std::array<std::int64_t,8> p{};
    std::uint64_t pairs=0;
    std::vector<int> ids;
};
inline bool compatible(const Profile& a,const Profile& b) {
    const auto& x=a.p;const auto& y=b.p;
    if(x[0]+y[0]>10)return false;
    if(std::max({x[2],y[2],std::int64_t(0)})>std::min({std::int64_t(72),x[3],y[3]}))return false;
    if((std::uint64_t(x[4])&~std::uint64_t(y[5])) || (std::uint64_t(y[4])&~std::uint64_t(x[5])))return false;
    if(x[0]+y[0]==10 && (!(y[7]&(1LL<<(2-x[6]))) || !(x[7]&(1LL<<(2-y[6])))))return false;
    return true;
}
struct RowBlocks {std::vector<int> js;std::vector<std::uint64_t> prefix{0};};
struct Pair {std::uint64_t id;int left,right;};

class Catalog {
    mutable std::mutex row_mutex_,seed_mutex_;
    mutable std::map<int,std::shared_ptr<const RowBlocks>> row_cache_;
    mutable std::vector<std::shared_ptr<const fan::SeedInfo>> left_cache_,right_cache_;
    static std::vector<fan::Graph9> read_seeds(const std::string& raw,int order,std::size_t expected) {
        std::vector<fan::Graph9> graphs;std::istringstream input(raw);std::string line;
        while(std::getline(input,line)) {
            if(!line.empty()&&line.back()=='\r')line.pop_back();
            if(line.size()!=std::size_t(1+(order*(order-1)/2+5)/6)||line[0]!=char(63+order))
                throw std::runtime_error("Invalid graph6 record for its catalog side");
            graphs.push_back(fan::read_graph6(line));
        }
        if(graphs.size()!=expected)throw std::runtime_error("Incomplete seed library");
        return graphs;
    }
    static std::vector<Profile> read_profiles(const json& items,const std::vector<fan::Graph9>& graphs,
                                             int order,bool left_side,std::vector<std::uint64_t>* prefix) {
        std::vector<Profile> out;std::vector<bool> seen(graphs.size(),false);
        for(const auto& item:items) {
            Profile p;p.p=item.at("p").get<std::array<std::int64_t,8>>();
            if(left_side)p.pairs=item.at("pairs").get<std::uint64_t>();
            p.ids=item.at("ids").get<std::vector<int>>();
            if(p.p[0]<0||p.p[0]>=order||p.p[1]<0||p.p[1]>order*(order-1)/2||p.p[2]!=7*order-2*p.p[1]||
               p.p[3]<0||p.p[3]>72||p.p[4]<0||p.p[4]>=(1LL<<49)||p.p[5]<0||p.p[5]>=(1LL<<49)||
               p.p[6]<0||p.p[6]>2||p.p[7]<0||p.p[7]>7||p.ids.empty()||!std::is_sorted(p.ids.begin(),p.ids.end()))
                throw std::runtime_error("Invalid order-17 profile");
            for(int id:p.ids) {
                if(id<0||std::size_t(id)>=graphs.size()||seen[id])throw std::runtime_error("Duplicate or invalid seed index");
                seen[id]=true;int maxd=0,sumd=0,upper=0;
                for(int v=0;v<order;++v) {
                    const auto bits=graphs[id][v];if(bits>>order)throw std::runtime_error("Seed adjacency escapes its part");
                    int d=fan_symmetry::bit_count(bits);maxd=std::max(maxd,d);sumd+=d;upper+=std::min(17-order,10-d);
                }
                for(int v=order;v<9;++v)if(graphs[id][v])throw std::runtime_error("Nonzero padded seed vertex");
                if(maxd!=p.p[0]||sumd/2!=p.p[1]||upper!=p.p[3])throw std::runtime_error("Seed/profile mismatch");
            }
            if(prefix)prefix->push_back(prefix->back()+p.pairs);
            out.push_back(std::move(p));
        }
        if(std::find(seen.begin(),seen.end(),false)!=seen.end())throw std::runtime_error("Profiles omit a seed");
        return out;
    }
    std::shared_ptr<const fan::SeedInfo> seed_impl(int id,bool symmetry,bool left_side) const {
        const auto& graphs=left_side?graphs_left:graphs_right;auto& cache=left_side?left_cache_:right_cache_;
        if(id<0||std::size_t(id)>=graphs.size())throw std::runtime_error("Seed index outside its catalog side");
        {std::lock_guard<std::mutex> lock(seed_mutex_);if(cache[id]&&(!symmetry||cache[id]->automorphisms_ready))return cache[id];}
        auto s=std::make_shared<fan::SeedInfo>(graphs[id],symmetry,left_side?8:9);
        std::lock_guard<std::mutex> lock(seed_mutex_);
        if(!cache[id]||(symmetry&&!cache[id]->automorphisms_ready))cache[id]=s;
        return cache[id];
    }
public:
    std::vector<Profile> profiles_left,profiles_right;
    std::vector<std::uint64_t> prefix{0};
    std::vector<fan::Graph9> graphs_left,graphs_right;
    std::uint64_t total=0,chunk=0;
    std::string fingerprint,source_manifest;
    explicit Catalog(const fs::path& directory) {
        const auto cat=bytes(directory/"catalog.json"),left=bytes(directory/"fan8_target17.graph6"),right=bytes(directory/"fan9_target17.graph6");
        fingerprint=hexhash(fnv(right,fnv(left,fnv(cat,fnv(ENGINE)))));
        if(hexhash(fnv(cat))!=EXPECTED_CATALOG_FNV||hexhash(fnv(left))!=EXPECTED_LEFT_FNV||
           hexhash(fnv(right))!=EXPECTED_RIGHT_FNV||fingerprint!=EXPECTED_DATASET)
            throw std::runtime_error("Order-17 catalog/seed fingerprints differ from this executable's dataset");
        const auto data=json::parse(cat);
        if(data.at("format")!="fan17-catalog-1"||data.at("engine")!=ENGINE||data.at("total_order")!=17||
           data.at("orders")!=json::array({8,9})||data.at("seed_counts")!=json::array({8812,115174}))
            throw std::runtime_error("Not the pinned order-17 rectangular catalog");
        total=data.at("total_pairs").get<std::uint64_t>();chunk=data.at("chunk_size").get<std::uint64_t>();
        source_manifest=data.at("source_manifest_id").get<std::string>();
        if(total!=EXPECTED_PAIRS||chunk!=500||data.at("profile_counts")!=json::array({EXPECTED_LEFT_PROFILES,EXPECTED_RIGHT_PROFILES}))
            throw std::runtime_error("Unexpected order-17 catalog dimensions");
        graphs_left=read_seeds(left,8,8812);graphs_right=read_seeds(right,9,115174);
        profiles_left=read_profiles(data.at("profiles_left"),graphs_left,8,true,&prefix);
        profiles_right=read_profiles(data.at("profiles_right"),graphs_right,9,false,nullptr);
        if(profiles_left.size()!=EXPECTED_LEFT_PROFILES||profiles_right.size()!=EXPECTED_RIGHT_PROFILES||prefix.back()!=total)
            throw std::runtime_error("Incomplete order-17 profile index");
        left_cache_.resize(graphs_left.size());right_cache_.resize(graphs_right.size());
    }
    std::uint64_t tasks() const {return (total+chunk-1)/chunk;}
    std::pair<std::uint64_t,std::uint64_t> bounds(std::uint64_t task) const {
        if(task>=tasks())throw std::runtime_error("Task index outside catalog");return {task*chunk,std::min((task+1)*chunk,total)};
    }
    std::shared_ptr<const RowBlocks> row(int i) const {
        {std::lock_guard<std::mutex> lock(row_mutex_);auto it=row_cache_.find(i);if(it!=row_cache_.end())return it->second;}
        if(i<0||std::size_t(i)>=profiles_left.size())throw std::runtime_error("Left profile index outside catalog");
        auto r=std::make_shared<RowBlocks>();
        for(int j=0;j<int(profiles_right.size());++j)if(compatible(profiles_left[i],profiles_right[j])) {
            r->js.push_back(j);r->prefix.push_back(r->prefix.back()+std::uint64_t(profiles_left[i].ids.size())*profiles_right[j].ids.size());
        }
        if(r->prefix.back()!=profiles_left[i].pairs)throw std::runtime_error("Row count disagrees with rectangular compatibility rules");
        std::lock_guard<std::mutex> lock(row_mutex_);if(row_cache_.size()>=128)row_cache_.erase(row_cache_.begin());
        return row_cache_.emplace(i,r).first->second;
    }
    Pair pair(std::uint64_t position) const {
        if(position>=total)throw std::runtime_error("Case index outside order-17 catalog");
        const int i=int(std::upper_bound(prefix.begin(),prefix.end(),position)-prefix.begin())-1;
        auto blocks=row(i);const auto local=position-prefix[i];
        const int block=int(std::upper_bound(blocks->prefix.begin(),blocks->prefix.end(),local)-blocks->prefix.begin())-1;
        const int j=blocks->js.at(block);const auto offset=local-blocks->prefix[block];
        const auto& a=profiles_left[i].ids;const auto& b=profiles_right[j].ids;
        return {position,a.at(std::size_t(offset/b.size())),b.at(std::size_t(offset%b.size()))};
    }
    std::shared_ptr<const fan::SeedInfo> seed_left(int id,bool symmetry) const {return seed_impl(id,symmetry,true);}
    std::shared_ptr<const fan::SeedInfo> seed_right(int id,bool symmetry) const {return seed_impl(id,symmetry,false);}
};
} // namespace fan_cli
