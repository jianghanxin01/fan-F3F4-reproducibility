#include "catalog.hpp"
#include "checkpoint_io.hpp"
#include <atomic>
#include <chrono>
#include <cmath>
#include <csignal>
#include <cstdio>
#include <exception>
#include <functional>
#include <iostream>
#include <set>
#include <thread>

using namespace fan_cli;
using fan_io::atomic_json;
using fan_io::DirLock;
using Clock=std::chrono::steady_clock;
static volatile std::sig_atomic_t interrupted=0;
static void signal_handler(int) { interrupted=1; }
static double elapsed(Clock::time_point start) { return std::chrono::duration<double>(Clock::now()-start).count(); }
static std::mutex console_mutex;
static void say(const json& value) { std::lock_guard<std::mutex> lock(console_mutex); std::cout<<value.dump()<<std::endl; }

struct Args {
    std::string command;
    std::map<std::string,std::vector<std::string>> values;
    Args(int argc,char** argv) {
        if (argc<2) {command="help";return;} command=argv[1];
        const std::set<std::string> flags{"--retry-unknown"};
        for (int i=2;i<argc;++i) {
            std::string key=argv[i]; if (key.rfind("--",0)!=0 || values.count(key)) throw std::runtime_error("Invalid/duplicate option "+key);
            values[key]={};
            if (flags.count(key)) continue;
            if (key=="--inputs") { while (i+1<argc && std::string(argv[i+1]).rfind("--",0)!=0) values[key].push_back(argv[++i]); }
            else if (i+1<argc && std::string(argv[i+1]).rfind("--",0)!=0) values[key].push_back(argv[++i]);
            if (values[key].empty()) throw std::runtime_error("Missing value for "+key);
        }
    }
    void allowed(std::initializer_list<const char*> names) const {
        std::set<std::string> set; for (auto n:names) set.insert(n);
        for (const auto& kv:values) if (!set.count(kv.first)) throw std::runtime_error("Unknown option "+kv.first);
    }
    bool has(const std::string& key) const {return values.count(key)!=0;}
    std::string get(const std::string& key,const std::string& def="") const {auto it=values.find(key);return it==values.end()?def:it->second.at(0);}
    std::uint64_t number(const std::string& key,std::uint64_t def) const {
        if (!has(key)) return def; std::string v=get(key); std::size_t used=0;
        if (v.empty() || v[0]=='-') throw std::runtime_error("Expected nonnegative integer for "+key);
        auto n=std::stoull(v,&used); if (used!=v.size()) throw std::runtime_error("Invalid integer for "+key); return n;
    }
    double seconds() const { std::string v=get("--seconds","5"); std::size_t used=0; double x=std::stod(v,&used);
        if (used!=v.size() || !std::isfinite(x) || x<=0) throw std::runtime_error("--seconds must be finite and positive"); return x; }
    bool symmetry() const {auto s=get("--symmetry","on"); if(s!="on"&&s!="off")throw std::runtime_error("--symmetry must be on or off");return s=="on";}
    unsigned threads() const {auto n=number("--threads",1); if(n<1||n>1024)throw std::runtime_error("--threads must be 1..1024");return unsigned(n);}
};
static json result_json(const fan::SolveResult& r) {
    json j={{"status",r.status},{"setup_seconds",r.setup_seconds},{"total_seconds",r.total_seconds},
      {"iterations",r.iterations},{"clauses",r.clauses},{"variables",r.variables},
      {"symmetry_constraints",r.symmetry_constraints},{"left_group_order",r.left_group_order},
      {"right_group_order",r.right_group_order},{"transpose_constraint",r.transpose_constraint},{"proof_verified",false}};
    if (r.has_witness) j["red_adjacency"]=r.red;
    return j;
}
static fan::SolveResult solve(Catalog& c,const Pair& p,const fan::SolveOptions& options) {
    auto a=c.seed_left(p.left,options.symmetry), b=c.seed_right(p.right,options.symmetry);
    auto r=fan::solve_pair(*a,*b,options);
    if(r.status!="SAT"&&r.status!="UNSAT"&&r.status!="UNKNOWN")throw std::runtime_error("Invalid solver status");
    if(r.status=="SAT" && (!r.has_witness || !fan::valid_fan_coloring(fan::Graph(r.red.begin(),r.red.end()))))throw std::runtime_error("Invalid SAT witness");
    return r;
}
static fs::path task_path(const fs::path& root,std::uint64_t id) {
    std::ostringstream s;s<<"task_"<<std::setw(6)<<std::setfill('0')<<id<<".json";return root/s.str();
}
struct Checkpoint {
    std::uint64_t task=0,start=0,stop=0,attempts=0;
    double seconds=0,work_seconds=0;
    bool symmetry=true;
    std::string status;
    json witnesses=json::object();
};
static Checkpoint blank(Catalog& c,std::uint64_t task) {
    auto bounds=c.bounds(task); Checkpoint v;v.task=task;v.start=bounds.first;v.stop=bounds.second;v.status.assign(v.stop-v.start,'0');return v;
}
static std::array<std::uint64_t,4> counts(const std::string& s) {std::array<std::uint64_t,4> out{};for(char ch:s){if(ch<'0'||ch>'3')throw std::runtime_error("Invalid checkpoint status");++out[ch-'0'];}return out;}
static fan::Graph parse_graph(const json& raw) {
    if(!raw.is_array())throw std::runtime_error("Adjacency must be an array");
    fan::Graph graph;graph.reserve(raw.size());
    for(const auto& value:raw) {
        if(!value.is_number_unsigned()||value.get<std::uint64_t>()>0xffffffffULL)throw std::runtime_error("Adjacency masks must be unsigned 32-bit integers");
        graph.push_back(value.get<std::uint32_t>());
    }
    return graph;
}
static void witness_check(Catalog& c,std::uint64_t id,const json& raw) {
    auto g=parse_graph(raw); if(g.size()!=17)throw std::runtime_error("Wrong witness order");
    for(int u=0;u<17;++u) {
        if(g[u]&~((1U<<17)-1) || (g[u]&(1U<<u)))throw std::runtime_error("Invalid witness adjacency");
        for(int v=0;v<17;++v)if(((g[u]>>v)&1)!=((g[v]>>u)&1))throw std::runtime_error("Asymmetric witness");
    }
    auto p=c.pair(id);
    for(int u=0;u<8;++u)if((g[u]&255)!=c.graphs_left[p.left][u])throw std::runtime_error("Left witness seed mismatch");
    for(int u=0;u<9;++u)if((g[u+8]>>8)!=c.graphs_right[p.right][u])throw std::runtime_error("Right witness seed mismatch");
    if(!fan::valid_fan_coloring(g))throw std::runtime_error("Witness contains a forbidden fan");
}
static std::string status_hash(const Checkpoint& v) {return hexhash(fnv(v.witnesses.dump(),fnv(v.status)));}
static Checkpoint read_checkpoint(Catalog& c,const fs::path& path) {
    auto j=json::parse(bytes(path)); auto id=j.at("task").get<std::uint64_t>(); Checkpoint v=blank(c,id);
    if(j.at("format")!="fan17-cpp-checkpoint-1"||j.at("engine")!=ENGINE||j.at("dataset")!=c.fingerprint||j.at("start")!=v.start||j.at("stop")!=v.stop||j.at("proof_verified")!=false)
        throw std::runtime_error("Checkpoint belongs to another dataset/engine: "+path.string());
    v.status=j.at("status").get<std::string>();v.witnesses=j.at("witnesses");
    v.attempts=j.at("attempts").get<std::uint64_t>();v.work_seconds=j.at("work_seconds").get<double>();
    v.seconds=j.at("seconds").get<double>();v.symmetry=j.at("symmetry").get<bool>();
    if(v.status.size()!=v.stop-v.start||!v.witnesses.is_object()||j.at("status_hash")!=status_hash(v)||!std::isfinite(v.work_seconds)||v.work_seconds<0)
        throw std::runtime_error("Damaged checkpoint: "+path.string());
    auto cnt=counts(v.status);
    if(v.witnesses.size()!=cnt[3])throw std::runtime_error("Missing or surplus SAT witness");
    for(std::size_t i=0;i<v.status.size();++i)if(v.status[i]=='3') {
        auto key=std::to_string(v.start+i);if(!v.witnesses.contains(key))throw std::runtime_error("Missing SAT witness");witness_check(c,v.start+i,v.witnesses[key]);
    }
    if(v.attempts<v.status.size()-cnt[0])throw std::runtime_error("Invalid attempt count");
    return v;
}
static void save_checkpoint(Catalog& c,const fs::path& path,const Checkpoint& v) {
    auto cnt=counts(v.status);
    atomic_json(path,{{"format","fan17-cpp-checkpoint-1"},{"engine",ENGINE},{"dataset",c.fingerprint},
        {"source_manifest_id",c.source_manifest},{"task",v.task},{"start",v.start},{"stop",v.stop},
        {"status",v.status},{"status_hash",status_hash(v)},{"attempts",v.attempts},{"work_seconds",v.work_seconds},
        {"seconds",v.seconds},{"symmetry",v.symmetry},{"counts",{{"PENDING",cnt[0]},{"UNSAT",cnt[1]},{"UNKNOWN",cnt[2]},{"SAT",cnt[3]}}},
        {"witnesses",v.witnesses},{"proof_verified",false}});
}

static void run(const Args& args) {
    args.allowed({"--data","--machine","--machines","--threads","--seconds","--results","--retry-unknown","--task-ids","--task-file","--case-budget","--symmetry","--task-order"});
    Catalog c(args.get("--data","data")); const auto machine=args.number("--machine",1),machines=args.number("--machines",1);
    if(machines<1||machines>c.tasks()||machine<1||machine>machines)throw std::runtime_error("Machine number must be 1..--machines, with --machines between 1 and the task count");
    const fs::path root=args.get("--results","results/machine_01");fs::create_directories(root);DirLock run_lock(root/"RUN.lock");
    if(fs::exists(root/"SAT_FOUND.json")) {
        auto marker=json::parse(bytes(root/"SAT_FOUND.json"));
        if(marker.at("dataset")!=c.fingerprint||marker.at("engine")!=ENGINE)throw std::runtime_error("SAT marker belongs to another dataset/engine");
        witness_check(c,marker.at("case").get<std::uint64_t>(),marker.at("red_adjacency"));
        say({{"status","SAT_ALREADY_FOUND"},{"case",marker.at("case")},{"witness",(root/"SAT_FOUND.json").u8string()}});return;
    }
    fs::remove(root/"STOP"); // A new explicit run resumes a prior graceful stop.
    fan::SolveOptions options;options.seconds=args.seconds();options.symmetry=args.symmetry();
    const bool retry=args.has("--retry-unknown");const auto budget=args.number("--case-budget",~std::uint64_t(0));
    std::vector<std::uint64_t> tasks;
    if(args.has("--task-ids")&&args.has("--task-file"))throw std::runtime_error("Use either --task-ids or --task-file");
    if(args.has("--task-ids")) {
        std::istringstream s(args.get("--task-ids"));std::string part;std::set<std::uint64_t> unique;
        while(std::getline(s,part,',')){std::size_t used=0;if(part.empty()||part[0]=='-')throw std::runtime_error("Invalid task list");auto id=std::stoull(part,&used);if(used!=part.size()||id>=c.tasks()||!unique.insert(id).second)throw std::runtime_error("Invalid/duplicate task ID");tasks.push_back(id);}
        if(tasks.empty())throw std::runtime_error("Empty task list");
    } else if(args.has("--task-file")) {
        auto list=json::parse(bytes(args.get("--task-file")));if(!list.is_array())throw std::runtime_error("Task file must contain a JSON array");
        std::set<std::uint64_t> unique;
        for(const auto& value:list) {
            if(!value.is_number_unsigned())throw std::runtime_error("Task file IDs must be nonnegative integers");
            auto id=value.get<std::uint64_t>();if(id>=c.tasks()||!unique.insert(id).second)throw std::runtime_error("Invalid/duplicate task ID in task file");
            if(id%machines==machine-1)tasks.push_back(id);
        }
    } else for(std::uint64_t id=machine-1;id<c.tasks();id+=machines)tasks.push_back(id);
    const auto task_order=args.get("--task-order","spread");
    if(task_order!="spread"&&task_order!="sequential")throw std::runtime_error("--task-order must be spread or sequential");
    if(task_order=="spread") {
        // A deterministic permutation of existing tasks, never a sampling filter.
        // This visits distinct catalog regions early when seeking one witness.
        auto priority=[](std::uint64_t x) {
            x+=20261002ULL+0x9e3779b97f4a7c15ULL;
            x=(x^(x>>30))*0xbf58476d1ce4e5b9ULL;
            x=(x^(x>>27))*0x94d049bb133111ebULL;
            return x^(x>>31);
        };
        std::sort(tasks.begin(),tasks.end(),[&](auto x,auto y){auto a=priority(x),b=priority(y);return a==b?x<y:a<b;});
    }
    std::atomic<std::size_t> next{0};std::atomic<std::uint64_t> attempted{0};std::atomic<bool> stop{false},sat_found{false};
    std::exception_ptr error;std::mutex error_mutex;auto began=Clock::now();
    auto stopped=[&]{return stop.load()||interrupted||fs::exists(root/"STOP");};
    auto worker=[&]{try{
        while(!stopped()) {
            auto t=next.fetch_add(1);if(t>=tasks.size())break;auto id=tasks[t];auto path=task_path(root,id);auto lp=path;lp+=".lock";DirLock lock(lp);
            auto v=fs::exists(path)?read_checkpoint(c,path):blank(c,id);if(v.task!=id)throw std::runtime_error("Task file name mismatch");
            if(v.status.find('3')!=std::string::npos){stop=true;break;}
            v.seconds=options.seconds;v.symmetry=options.symmetry;auto saved=Clock::now();unsigned dirty=0;
            for(std::size_t i=0;i<v.status.size()&&!stopped();++i) {
                if(v.status[i]!='0' && !(retry&&v.status[i]=='2'))continue;
                auto ticket=attempted.fetch_add(1);if(ticket>=budget){attempted.fetch_sub(1);stop=true;break;}
                auto pair=c.pair(v.start+i);auto start=Clock::now();auto result=solve(c,pair,options);v.work_seconds+=elapsed(start);++v.attempts;++dirty;
                v.status[i]=result.status=="UNSAT"?'1':result.status=="UNKNOWN"?'2':'3';
                if(result.status=="SAT") {
                    v.witnesses[std::to_string(pair.id)]=result.red;stop=true;
                    auto marker=result_json(result);marker["case"]=pair.id;marker["seed_indices"]={pair.left,pair.right};marker["dataset"]=c.fingerprint;marker["engine"]=ENGINE;
                    atomic_json(root/("witness_"+std::to_string(pair.id)+".json"),marker);
                    bool expected=false;if(sat_found.compare_exchange_strong(expected,true))atomic_json(root/"SAT_FOUND.json",marker);
                }
                if(dirty>=100||elapsed(saved)>=3||result.status=="SAT") {save_checkpoint(c,path,v);dirty=0;saved=Clock::now();}
            }
            save_checkpoint(c,path,v);auto cnt=counts(v.status);
            say({{"task",id},{"PENDING",cnt[0]},{"UNSAT",cnt[1]},{"UNKNOWN",cnt[2]},{"SAT",cnt[3]},{"wall_seconds",elapsed(began)}});
        }
    }catch(...){stop=true;std::lock_guard<std::mutex> lock(error_mutex);if(!error)error=std::current_exception();}};
    say({{"engine",ENGINE},{"checkpoint_io_revision",fan_io::revision},{"dataset",c.fingerprint},{"machine",machine},{"machines",machines},{"threads",args.threads()},{"assigned_tasks",tasks.size()},{"task_order",task_order},{"symmetry",options.symmetry}});
    std::vector<std::thread> workers;for(unsigned i=0;i<args.threads();++i)workers.emplace_back(worker);for(auto& w:workers)w.join();
    if(error)std::rethrow_exception(error);
    say({{"attempts_this_run",attempted.load()},{"wall_seconds",elapsed(began)},{"stopped",stopped()},{"proof_verified",false}});
}

static void pilot(const Args& args) {
    const auto full_began=Clock::now();
    args.allowed({"--data","--cases","--threads","--symmetry","--seconds","--output"});
    Catalog c(args.get("--data","data"));auto raw=json::parse(bytes(args.get("--cases","data/benchmark_cases.json")));
    if(!raw.is_array()||raw.empty())throw std::runtime_error("--cases must contain a nonempty JSON array");
    std::vector<Pair> cases;for(const auto& entry:raw){auto id=entry.is_number_unsigned()?entry.get<std::uint64_t>():entry.at("case").get<std::uint64_t>();auto p=c.pair(id);if(entry.is_object()&&entry.contains("seed_indices")&&entry["seed_indices"]!=json::array({p.left,p.right}))throw std::runtime_error("Benchmark seed indices disagree");cases.push_back(p);}
    fan::SolveOptions options;options.seconds=args.seconds();options.symmetry=args.symmetry();
    std::vector<json> results(cases.size());std::atomic<std::size_t> next{0};std::atomic<bool> stop{false};std::exception_ptr error;std::mutex mutex;auto began=Clock::now();
    auto worker=[&]{try{while(!stop&&!interrupted){auto i=next.fetch_add(1);if(i>=cases.size())break;auto t=Clock::now();auto r=solve(c,cases[i],options);auto j=result_json(r);j["case"]=cases[i].id;j["seed_indices"]={cases[i].left,cases[i].right};j["worker_seconds"]=elapsed(t);results[i]=std::move(j);if(r.status=="SAT")stop=true;}}catch(...){stop=true;std::lock_guard<std::mutex> lock(mutex);if(!error)error=std::current_exception();}};
    std::vector<std::thread> workers;for(unsigned i=0;i<args.threads();++i)workers.emplace_back(worker);for(auto& w:workers)w.join();if(error)std::rethrow_exception(error);
    const double solve_wall=elapsed(began),wall=elapsed(full_began);std::map<std::string,std::uint64_t> cnt;json completed=json::array();for(auto& j:results)if(!j.is_null()){++cnt[j.at("status").get<std::string>()];completed.push_back(j);}
    json out={{"engine",ENGINE},{"dataset",c.fingerprint},{"threads",args.threads()},{"symmetry",options.symmetry},{"seconds",options.seconds},
        {"requested_cases",cases.size()},{"completed_cases",completed.size()},{"wall_seconds",wall},{"solve_threads_wall_seconds",solve_wall},{"startup_seconds",wall-solve_wall},{"counts",cnt},{"runs",completed},{"proof_verified",false},
        {"estimate_caveat","This sample measures a time-limited first pass only; it does not predict time to a witness or complete exclusion."}};
    if(!completed.empty())out["extrapolated_first_pass_hours_same_threads"]=
        ((wall-solve_wall)+solve_wall/completed.size()*c.total)/3600;
    atomic_json(args.get("--output","benchmark.json"),out);out.erase("runs");say(out);
}

static void merge(const Args& args) {
    args.allowed({"--data","--inputs","--output"});if(!args.has("--inputs"))throw std::runtime_error("--inputs is required");
    Catalog c(args.get("--data","data"));fs::path output=args.get("--output","merged");
    if(fs::exists(output))for(const auto& entry:fs::directory_iterator(output)) {
        auto name=entry.path().filename().string();
        if(entry.is_regular_file()&&name.rfind("task_",0)==0&&entry.path().extension()==".json")throw std::runtime_error("Merge output already contains checkpoints; choose a fresh --output directory");
    }
    fs::create_directories(output);DirLock lock(output/"RUN.lock");
    std::map<std::uint64_t,Checkpoint> joined;std::uint64_t duplicate_entries=0,files=0;
    for(const auto& dir:args.values.at("--inputs")) {
        const fs::path root(dir);if(!fs::is_directory(root))throw std::runtime_error("Input is not a directory: "+dir);
        if(fs::weakly_canonical(root)==fs::weakly_canonical(output))throw std::runtime_error("Merge output must differ from every input");
        if(fs::exists(root/"RUN.lock"))throw std::runtime_error("Input is running or has a stale lock: "+dir);
        for(const auto& entry:fs::directory_iterator(root)) {
            auto name=entry.path().filename().string();if(!entry.is_regular_file()||name.rfind("task_",0)!=0||entry.path().extension()!=".json")continue;
            auto v=read_checkpoint(c,entry.path());if(task_path(root,v.task).filename()!=entry.path().filename())throw std::runtime_error("Checkpoint filename mismatch");++files;
            auto it=joined.find(v.task);if(it==joined.end()){joined.emplace(v.task,std::move(v));continue;}auto& dst=it->second;
            for(std::size_t i=0;i<v.status.size();++i) {
                char a=dst.status[i],b=v.status[i];if(a!='0'&&b!='0')++duplicate_entries;
                if((a=='1'&&b=='3')||(a=='3'&&b=='1'))throw std::runtime_error("Conflicting SAT/UNSAT at case "+std::to_string(v.start+i));
                if(a=='0'||(a=='2'&&(b=='1'||b=='3')))dst.status[i]=b;
                if(b=='3')dst.witnesses[std::to_string(v.start+i)]=v.witnesses.at(std::to_string(v.start+i));
            }
            dst.attempts+=v.attempts;dst.work_seconds+=v.work_seconds;
        }
        // A persistent witness marker may have reached disk immediately before
        // an interrupted checkpoint write. It must still prevent exclusion.
        if(fs::exists(root/"SAT_FOUND.json")) {
            auto marker=json::parse(bytes(root/"SAT_FOUND.json"));
            if(marker.at("dataset")!=c.fingerprint||marker.at("engine")!=ENGINE)throw std::runtime_error("SAT marker dataset mismatch");
            auto id=marker.at("case").get<std::uint64_t>();witness_check(c,id,marker.at("red_adjacency"));
            auto task=id/c.chunk;auto it=joined.find(task);if(it==joined.end())it=joined.emplace(task,blank(c,task)).first;
            auto& v=it->second;auto offset=std::size_t(id-v.start);
            if(v.status[offset]=='1')throw std::runtime_error("SAT marker conflicts with UNSAT checkpoint");
            if(v.status[offset]=='0')++v.attempts;
            v.status[offset]='3';v.witnesses[std::to_string(id)]=marker.at("red_adjacency");
        }
    }
    std::array<std::uint64_t,4> totals{};json pending_tasks=json::array(),unknown_tasks=json::array();
    for(std::uint64_t id=0;id<c.tasks();++id) {
        auto it=joined.find(id);if(it==joined.end()){auto b=c.bounds(id);totals[0]+=b.second-b.first;pending_tasks.push_back(id);continue;}
        auto cnt=counts(it->second.status);for(int k=0;k<4;++k)totals[k]+=cnt[k];if(cnt[0])pending_tasks.push_back(id);if(cnt[2])unknown_tasks.push_back(id);
        save_checkpoint(c,task_path(output,id),it->second);
    }
    json summary={{"engine",ENGINE},{"dataset",c.fingerprint},{"total_pairs",c.total},{"input_checkpoint_files",files},
      {"duplicate_completed_entries",duplicate_entries},{"PENDING",totals[0]},{"UNSAT",totals[1]},{"UNKNOWN",totals[2]},{"SAT",totals[3]},
      {"all_pairs_resolved",totals[0]==0&&totals[2]==0},{"solver_reported_exclusion",totals[1]==c.total},{"proof_verified",false}};
    atomic_json(output/"summary.json",summary);atomic_json(output/"pending_tasks.json",pending_tasks);atomic_json(output/"unknown_tasks.json",unknown_tasks);say(summary);
}

static void pair_command(const Args& args) {
    args.allowed({"--data","--left-index","--right-index","--seconds","--symmetry","--output","--dump-cnf"});
    if(!args.has("--left-index")||!args.has("--right-index"))throw std::runtime_error("Both seed indices are required");
    Catalog c(args.get("--data","data"));auto left=args.number("--left-index",0),right=args.number("--right-index",0);
    if(left>=c.graphs_left.size()||right>=c.graphs_right.size())throw std::runtime_error("Seed index outside catalog");
    fan::SolveOptions options;options.seconds=args.seconds();options.symmetry=args.symmetry();options.dump_cnf=args.get("--dump-cnf");
    auto r=solve(c,{0,int(left),int(right)},options);auto j=result_json(r);j["seed_indices"]={left,right};j["dataset"]=c.fingerprint;j["engine"]=ENGINE;
    if(args.has("--output"))atomic_json(args.get("--output"),j);say(j);
}
static void verify_command(const Args& args) {
    args.allowed({"--input"});if(!args.has("--input"))throw std::runtime_error("--input is required");
    auto raw=json::parse(bytes(args.get("--input")));
    auto red=parse_graph(raw.is_array()?raw:raw.at("red_adjacency"));
    say({{"order",red.size()},{"valid",fan::valid_fan_coloring(red)},
         {"scope","Verification of this colouring against red F3 and blue F4 only"}});
}
static void catalog_command(const Args& args) {
    args.allowed({"--data"}); Catalog c(args.get("--data","data"));
    say({{"engine",ENGINE},{"dataset",c.fingerprint},{"order",17},
         {"left_order",8},{"right_order",9},{"cross_variables",72},
         {"left_seeds",c.graphs_left.size()},{"right_seeds",c.graphs_right.size()},
         {"total_pairs",c.total},{"chunk_size",c.chunk},{"tasks",c.tasks()},
         {"proof_verified",false}});
}
static void index_command(const Args& args) {
    args.allowed({"--data","--cases","--output"});
    if(!args.has("--cases"))throw std::runtime_error("--cases is required");
    Catalog c(args.get("--data","data"));auto raw=json::parse(bytes(args.get("--cases")));
    if(!raw.is_array())throw std::runtime_error("Case indices must be a JSON array");
    json mapped=json::array();for(const auto& entry:raw) {
        const auto& raw_id=entry.is_object()?entry.at("case"):entry;
        if(!raw_id.is_number_unsigned())throw std::runtime_error("Case index must be a nonnegative integer");
        auto p=c.pair(raw_id.get<std::uint64_t>());
        if(entry.is_object()&&entry.contains("seed_indices")&&entry.at("seed_indices")!=json::array({p.left,p.right}))
            throw std::runtime_error("Independent case fixture disagrees with C++ mapping");
        mapped.push_back({{"case",p.id},{"seed_indices",{p.left,p.right}}});
    }
    if(args.has("--output"))atomic_json(args.get("--output"),mapped);else say(mapped);
}
static void help() {
    std::cout<<"fan_ramsey17 (C++17, CPU; fixed 8+9 gluing)\n"
      "  self-test\n"
      "  catalog --data data\n"
      "  index --data data --cases case_ids.json --output indexed.json\n"
      "  pilot --data data --cases data/benchmark_cases.json --threads 4 --symmetry on --seconds 5 --output benchmark.json\n"
      "  run --data data --machine 1 --machines 1 --threads 4 --seconds 5 --results results/machine_01\n"
      "      [--symmetry on|off] [--retry-unknown] [--task-ids 0,11 | --task-file pending_tasks.json] [--case-budget 5]\n"
      "      [--task-order spread|sequential] (default spread; visits every assigned task)\n"
      "  stop --results results/machine_01\n"
      "  merge --data data --inputs results/machine_01 results/machine_02 --output merged\n"
      "  pair --data data --left-index 0 --right-index 1 --seconds 5 --symmetry on --output pair.json [--dump-cnf pair.cnf]\n"
      "  verify --input witness.json\n"
      "Case and seed IDs are zero-based. Left IDs refer to order 8; right IDs to order 9.\n"
      "Machines are numbered 1..--machines. Order-18 checkpoints are incompatible.\n"
      "Resume by repeating run. UNKNOWN is retried only with --retry-unknown.\n"
      "Task files are filtered by machine modulo. Explicit --task-ids override machine allocation.\n"
      "Case budget limits attempts across all threads for this invocation. Merge needs a fresh output directory.\n"
      "Stop is checked between cases; an active case observes its own time limit.\n"
      "All UNSAT results are solver reports; proof_verified remains false.\n";
}
int main(int argc,char** argv) {
    std::signal(SIGINT,signal_handler);std::signal(SIGTERM,signal_handler);
    try {
        Args args(argc,argv);
        if(args.command=="run")run(args);
        else if(args.command=="pilot")pilot(args);
        else if(args.command=="merge")merge(args);
        else if(args.command=="pair")pair_command(args);
        else if(args.command=="verify")verify_command(args);
        else if(args.command=="catalog")catalog_command(args);
        else if(args.command=="index")index_command(args);
        else if(args.command=="stop") {args.allowed({"--results"});fs::path root=args.get("--results","results/machine_01");if(!fs::is_directory(root))throw std::runtime_error("Results directory does not exist");std::ofstream f(root/"STOP");if(!f)throw std::runtime_error("Cannot write stop request");f<<"stop\n";say({{"stop_requested",root.u8string()}});}
        else if(args.command=="self-test") {args.allowed({});fan_symmetry::run_self_tests();fan::self_test_core();say({{"self_test","passed"},{"engine",ENGINE},{"checkpoint_io_revision",fan_io::revision}});}
        else if(args.command=="help"||args.command=="--help")help();
        else throw std::runtime_error("Unknown command: "+args.command);
        return 0;
    }catch(const std::exception& e){std::cerr<<"ERROR: "<<e.what()<<std::endl;return 1;}
}
