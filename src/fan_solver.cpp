#include "fan_solver.hpp"
#include "minisat/core/Solver.h"
#include <algorithm>
#include <chrono>
#include <cmath>
#include <fstream>
#include <functional>
#include <numeric>
#include <stdexcept>
#include <utility>

namespace fan {
namespace {
constexpr int LEFT = 8, RIGHT = 9, TOTAL = LEFT+RIGHT, CROSS = LEFT*RIGHT;
using Clock = std::chrono::steady_clock;
using Matching = std::vector<std::pair<int, int>>;
using Minisat::lbool;
#ifndef MINISAT_CONSTANTS_AS_MACROS
using Minisat::l_True;
using Minisat::l_False;
using Minisat::l_Undef;
#endif

int popcount(std::uint32_t x) {
    int count = 0;
    while (x) { x &= x-1; ++count; }
    return count;
}
int first_vertex(std::uint32_t x) {
    if (!x) throw std::logic_error("Zero vertex mask");
    int v = 0;
    while (!(x & 1u)) { ++v; x >>= 1; }
    return v;
}
double elapsed(Clock::time_point from) {
    return std::chrono::duration<double>(Clock::now()-from).count();
}

bool find_matching(const Graph& adj, std::uint32_t mask, int k, Matching& selected) {
    if (k == 0) return true;
    if (popcount(mask) < 2*k) return false;
    const int v = first_vertex(mask);
    const auto rest = mask & ~(1u << v);
    auto mates = adj[v] & rest;
    while (mates) {
        const int w = first_vertex(mates);
        mates &= mates-1;
        selected.emplace_back(v, w);
        if (find_matching(adj, rest & ~(1u << w), k-1, selected)) return true;
        selected.pop_back();
    }
    return find_matching(adj, rest, k, selected);
}

bool find_clique(const Graph& adj, std::uint32_t mask, int k, std::vector<int>& selected) {
    if (k == 0) return true;
    if (popcount(mask) < k) return false;
    while (mask) {
        const int v = first_vertex(mask);
        mask &= mask-1;
        selected.push_back(v);
        if (find_clique(adj, mask & adj[v], k-1, selected)) return true;
        selected.pop_back();
    }
    return false;
}

std::array<unsigned char, 512> matching_table(const Graph9& adj) {
    std::array<unsigned char, 512> table{};
    for (unsigned mask = 1; mask < 512; ++mask) {
        const int v = first_vertex(mask);
        const auto rest = mask & ~(1u << v);
        int best = table[rest];
        auto mates = adj[v] & rest;
        while (mates) {
            const auto bit = mates & (~mates+1u);
            mates ^= bit;
            best = std::max(best, 1+int(table[rest ^ bit]));
        }
        table[mask] = static_cast<unsigned char>(best);
    }
    return table;
}

class Formula {
public:
    Minisat::Solver solver;
    std::uint64_t clause_count = 0;
    bool retain;
    std::vector<std::vector<int>> clauses;
    explicit Formula(bool keep=false) : retain(keep) { solver.verbosity = 0; }
    int variable() { return solver.newVar()+1; }
    void add(const std::vector<int>& clause) {
        ++clause_count;
        if (retain) clauses.push_back(clause);
        // Once contradictory, retaining further clauses is optional for solving,
        // but diagnostic DIMACS retains every generated constraint.
        if (!solver.okay()) return;
        Minisat::vec<Minisat::Lit> values;
        for (int lit : clause) {
            if (!lit || std::abs(lit) > solver.nVars()) throw std::logic_error("Invalid CNF literal");
            values.push(Minisat::mkLit(std::abs(lit)-1, lit < 0));
        }
        solver.addClause(values);
    }
    void at_most(const std::vector<int>& x, int k) {
        const int n = int(x.size());
        if (k < 0) { add({}); return; }
        if (k >= n) return;
        if (k == 0) { for (int lit : x) add({-lit}); return; }
        // Sequential threshold implications.  s[i][j] means prefix i+1
        // contains at least j true literals.  Existential projection is sum<=k.
        std::vector<std::vector<int>> s(std::max(0, n-1));
        for (int i = 0; i < n-1; ++i) {
            s[i].resize(std::min(k, i+1)+1);
            for (int j = 1; j < int(s[i].size()); ++j) s[i][j] = variable();
            add({-x[i], s[i][1]});
            if (i > 0) {
                for (int j = 1; j < int(s[i-1].size()); ++j) add({-s[i-1][j], s[i][j]});
                for (int j = 2; j < int(s[i].size()); ++j)
                    add({-x[i], -s[i-1][j-1], s[i][j]});
            }
        }
        for (int i = k; i < n; ++i) add({-x[i], -s[i-1][k]});
    }
    void at_least(const std::vector<int>& x, int k) {
        std::vector<int> negated;
        for (int v : x) negated.push_back(-v);
        at_most(negated, int(x.size())-k);
    }
    void lex_leq(const std::vector<int>& x, const std::vector<int>& y) {
        if (x.size() != y.size()) throw std::logic_error("Lex vector sizes differ");
        int equal_prefix = 0; // zero is the constant true prefix before position 0
        std::vector<std::size_t> moved;
        for (std::size_t i = 0; i < x.size(); ++i) if (x[i] != y[i]) moved.push_back(i);
        for (std::size_t at = 0; at < moved.size(); ++at) {
            const auto i = moved[at];
            if (equal_prefix) add({-equal_prefix, -x[i], y[i]});
            else add({-x[i], y[i]});
            if (at+1 == moved.size()) break;
            const int next = variable();
            // next <=> equal_prefix AND (x[i] <=> y[i]).
            if (equal_prefix) {
                add({-equal_prefix, -x[i], -y[i], next});
                add({-equal_prefix, x[i], y[i], next});
                add({-next, equal_prefix});
            } else {
                add({-x[i], -y[i], next});
                add({x[i], y[i], next});
            }
            add({-next, -x[i], y[i]});
            add({-next, x[i], -y[i]});
            equal_prefix = next;
        }
    }
    bool solve_fixed(const std::vector<int>& literals) {
        Minisat::vec<Minisat::Lit> assumptions;
        for (int lit : literals) assumptions.push(Minisat::mkLit(std::abs(lit)-1, lit < 0));
        return solver.solve(assumptions);
    }
    void dump(const std::string& name) const {
        std::ofstream out(name);
        if (!out) throw std::runtime_error("Cannot write CNF file: "+name);
        out << "p cnf " << solver.nVars() << ' ' << clauses.size() << '\n';
        for (const auto& c : clauses) {
            for (int lit : c) out << lit << ' ';
            out << "0\n";
        }
        if (!out) throw std::runtime_error("CNF write failed");
    }
};

int cross_variable(int i, int j) {
    if (i > j) std::swap(i, j);
    if (i < 0 || i >= LEFT || j < LEFT || j >= TOTAL) throw std::logic_error("Not a cross edge");
    return RIGHT*i+(j-LEFT)+1;
}

void add_forbidden(Formula& formula, const SeedInfo& a, const SeedInfo& b,
                   const Matching& edges, bool red) {
    std::vector<int> clause;
    for (auto edge : edges) {
        int u = edge.first, v = edge.second;
        if (u > v) std::swap(u, v);
        if (u < LEFT && v >= LEFT) {
            const int variable = cross_variable(u, v);
            clause.push_back(red ? -variable : variable);
        } else {
            const auto& seed = u < LEFT ? a : b;
            const int offset = u < LEFT ? 0 : LEFT;
            const bool actual = (seed.red[u-offset] >> (v-offset)) & 1;
            if (actual != red) return; // Fixed edge already forbids this copy.
        }
    }
    std::sort(clause.begin(), clause.end());
    clause.erase(std::unique(clause.begin(), clause.end()), clause.end());
    formula.add(clause);
}

void require(bool value, const char* what) {
    if (!value) throw std::logic_error(what);
}
} // namespace

Graph9 read_graph6(const std::string& input) {
    std::string line = input;
    if (!line.empty() && line.back() == '\r') line.pop_back();
    if (line.empty() || (line[0] != 'G' && line[0] != 'H'))
        throw std::invalid_argument("Expected graph6 of order 8 or 9");
    const int n = line[0]-63;
    if (line.size() != std::size_t(1+(n*(n-1)/2+5)/6))
        throw std::invalid_argument("Incorrect graph6 length");
    for (char ch : line) if (ch < 63 || ch > 126) throw std::invalid_argument("Invalid graph6 character");
    if (n == 8 && ((line.back()-63) & 3)) throw std::invalid_argument("Nonzero graph6 padding");
    Graph9 red{};
    int bit = 0;
    for (int j = 1; j < n; ++j) for (int i = 0; i < j; ++i, ++bit)
        if (((line[1+bit/6]-63) >> (5-bit%6)) & 1) {
            red[i] |= std::uint16_t(1u << j);
            red[j] |= std::uint16_t(1u << i);
        }
    return red;
}

SeedInfo::SeedInfo(const Graph9& graph, bool compute_automorphisms, int order) : n(order), red(graph) {
    fan_symmetry::validate_graph(red, n);
    const auto all = (1u << n)-1;
    for (int v = 0; v < n; ++v) {
        blue[v] = std::uint16_t(all ^ (1u << v) ^ red[v]);
        degree[v] = popcount(red[v]);
    }
    for (int colour = 0; colour < 2; ++colour) {
        const auto& adj = colour == 0 ? red : blue;
        const int cap = colour == 0 ? 2 : 3;
        const auto table = matching_table(adj);
        for (unsigned mask = 0; mask <= all; ++mask) {
            const int size = popcount(mask);
            if (size % 2 == 0 && table[mask] == size/2)
                matching_endpoints[colour][size/2].push_back(std::uint16_t(mask));
        }
        for (int v = 0; v < n; ++v) {
            internal_nu[colour][v] = table[adj[v]];
            if (internal_nu[colour][v] > cap) throw std::invalid_argument("Seed contains a forbidden fan");
            if (internal_nu[colour][v] == cap) {
                for (int w = 0; w < n; ++w)
                    if ((adj[v] & (1u << w)) && table[adj[v] & ~(1u << w)] == cap)
                        free_vertices[colour][v] |= std::uint16_t(1u << w);
            }
        }
    }
    if (compute_automorphisms) {
        automorphisms = fan_symmetry::automorphism_group(red, n);
        automorphisms_ready = true;
    }
}

bool valid_fan_coloring(const Graph& red) {
    const int n = int(red.size());
    if (n < 1 || n > 31) return false;
    const auto all = (std::uint32_t(1) << n)-1;
    Graph blue(n);
    for (int v = 0; v < n; ++v) {
        if ((red[v] & ~all) || (red[v] & (1u << v))) return false;
        for (int w = 0; w < n; ++w)
            if (bool(red[v] & (1u << w)) != bool(red[w] & (1u << v))) return false;
        blue[v] = all ^ (1u << v) ^ red[v];
    }
    for (int colour = 0; colour < 2; ++colour) {
        const auto& adj = colour == 0 ? red : blue;
        for (int v = 0; v < n; ++v) {
            Matching m;
            if (find_matching(adj, adj[v], colour == 0 ? 3 : 4, m)) return false;
        }
    }
    return true;
}

SolveResult solve_pair(const SeedInfo& left, const SeedInfo& right, const SolveOptions& options) {
    if (left.n != LEFT || right.n != RIGHT)
        throw std::invalid_argument("Order-17 gluing requires left order 8 and right order 9");
    if (!(options.seconds > 0) || !std::isfinite(options.seconds)) throw std::invalid_argument("seconds must be finite and positive");
    if (options.symmetry && !options.fixed_cross.empty())
        throw std::invalid_argument("Fixed labelled cross assignments require symmetry=false");
    const auto began = Clock::now();
    Formula formula(!options.dump_cnf.empty());
    for (int i = 0; i < CROSS; ++i) formula.variable();
    SolveResult result;
    if (!options.fixed_cross.empty()) {
        if (options.fixed_cross.size() != CROSS) throw std::invalid_argument("fixed_cross needs 72 bits");
        for (int k = 0; k < CROSS; ++k) {
            if (options.fixed_cross[k] != 0 && options.fixed_cross[k] != 1) throw std::invalid_argument("fixed_cross is not binary");
            formula.add({options.fixed_cross[k] ? k+1 : -(k+1)});
        }
    }
    if (options.target_bounds) {
        for (int v = 0; v < TOTAL; ++v) {
            const int degree = v < LEFT ? left.degree[v] : right.degree[v-LEFT];
            std::vector<int> row;
            for (int w = v < LEFT ? LEFT : 0; w < (v < LEFT ? TOTAL : LEFT); ++w) row.push_back(cross_variable(v, w));
            formula.at_least(row, std::max(0, 7-degree));
            formula.at_most(row, std::min(int(row.size()), 10-degree));
        }
    }
    if (options.balanced) {
        for (int i = 0; i < LEFT; ++i) for (int j = 0; j < RIGHT; ++j) {
            std::vector<int> others;
            for (int k = 0; k < RIGHT; ++k) if (k != j) others.push_back(cross_variable(i, k+LEFT));
            for (int k = 0; k < LEFT; ++k) if (k != i) others.push_back(cross_variable(k, j+LEFT));
            formula.at_least(others, left.degree[i]+right.degree[j]);
        }
    }
    if (options.initial_matching_cuts) {
        for (int orientation = 0; orientation < 2; ++orientation) {
            const auto& a = orientation == 0 ? left : right;
            const auto& b = orientation == 0 ? right : left;
            const int oa = orientation == 0 ? 0 : LEFT, ob = LEFT-oa;
            for (int colour = 0; colour < 2; ++colour) {
                const int cap = colour == 0 ? 2 : 3;
                for (int u = 0; u < a.n; ++u) {
                    const int residual = cap+1-a.internal_nu[colour][u];
                    // Enumerate endpoint sets, rather than all perfect matchings
                    // with the same endpoint set.  This produces identical clauses
                    // to Python's matching enumeration after duplicate removal.
                    for (auto mask : b.matching_endpoints[colour][residual]) {
                        std::vector<int> clause;
                        for (int v = 0; v < b.n; ++v) if (mask & (1u << v)) {
                            int lit = cross_variable(u+oa, v+ob);
                            clause.push_back(colour == 0 ? -lit : lit);
                        }
                        formula.add(clause);
                    }
                    for (int t = 0; t < a.n; ++t) if (a.free_vertices[colour][u] & (1u << t)) {
                        if (u > t && (a.free_vertices[colour][t] & (1u << u))) continue;
                        for (int v = 0; v < b.n; ++v) {
                            const int x = cross_variable(u+oa, v+ob), y = cross_variable(t+oa, v+ob);
                            formula.add(colour == 0 ? std::vector<int>{-x, -y} : std::vector<int>{x, y});
                        }
                    }
                }
            }
        }
    }
    if (options.symmetry) {
        if (!left.automorphisms_ready || !right.automorphisms_ready) throw std::invalid_argument("Seed automorphisms were not prepared");
        fan_symmetry::GluingSymmetryDiagnostics diagnostics;
        const auto permutations = fan_symmetry::gluing_permutations(left.red, right.red,
                left.automorphisms, right.automorphisms, options.symmetry_cap, false, &diagnostics);
        std::vector<int> x(CROSS), y(CROSS);
        std::iota(x.begin(), x.end(), 1);
        for (const auto& p : permutations) {
            for (int i = 0; i < CROSS; ++i) y[i] = p[i]+1;
            formula.lex_leq(x, y);
        }
        result.symmetry_constraints = permutations.size();
        result.left_group_order = diagnostics.left_group_order;
        result.right_group_order = diagnostics.right_group_order;
        result.transpose_constraint = diagnostics.swap_included;
    }
    result.setup_seconds = elapsed(began);
    const auto solving_began = Clock::now();
    Minisat::vec<Minisat::Lit> assumptions;
    while (elapsed(solving_began) < options.seconds) {
        // Budgeted calls retain learned clauses and allow deadline checks without
        // one timer thread per pair.  The time limit is soft at budget boundaries.
        formula.solver.setConfBudget(1024);
        formula.solver.setPropBudget(100000);
        const auto answer = formula.solver.solveLimited(assumptions);
        if (answer == l_False) { result.status = "UNSAT"; break; }
        if (answer == l_Undef) continue;
        ++result.iterations;
        Graph red(TOTAL), blue(TOTAL);
        for (int i = 0; i < LEFT; ++i) red[i] = left.red[i];
        for (int i = 0; i < RIGHT; ++i) red[i+LEFT] = std::uint32_t(right.red[i]) << LEFT;
        for (int i = 0; i < LEFT; ++i) for (int j = 0; j < RIGHT; ++j)
            if (formula.solver.modelValue(RIGHT*i+j) == l_True) {
                red[i] |= 1u << (j+LEFT);
                red[j+LEFT] |= 1u << i;
            }
        for (int v = 0; v < TOTAL; ++v) blue[v] = ((1u << TOTAL)-1) ^ (1u << v) ^ red[v];
        bool invalid = false;
        for (int colour = 0; colour < 2; ++colour) {
            const auto& adj = colour == 0 ? red : blue;
            for (int centre = 0; centre < TOTAL; ++centre) {
                Matching matching;
                if (!find_matching(adj, adj[centre], colour == 0 ? 3 : 4, matching)) continue;
                invalid = true;
                Matching edges = matching;
                for (const auto& e : matching) {
                    edges.emplace_back(centre, e.first);
                    edges.emplace_back(centre, e.second);
                }
                add_forbidden(formula, left, right, edges, colour == 0);
            }
            if (options.clique_cuts) {
                std::vector<int> vertices;
                if (find_clique(adj, (1u << TOTAL)-1, colour == 0 ? 6 : 8, vertices)) {
                    invalid = true;
                    Matching edges;
                    for (std::size_t i = 0; i < vertices.size(); ++i)
                        for (std::size_t j = i+1; j < vertices.size(); ++j)
                            edges.emplace_back(vertices[i], vertices[j]);
                    add_forbidden(formula, left, right, edges, colour == 0);
                }
            }
        }
        if (!invalid) {
            if (!valid_fan_coloring(red)) throw std::logic_error("SAT model verification failed");
            std::copy(red.begin(), red.end(), result.red.begin());
            result.has_witness = true;
            result.status = "SAT";
            break;
        }
    }
    result.variables = formula.solver.nVars();
    result.clauses = formula.clause_count;
    if (!options.dump_cnf.empty()) formula.dump(options.dump_cnf);
    result.total_seconds = elapsed(began);
    return result;
}

void self_test_core() {
    // Exhaustive existential-projection check for positive and negative literals.
    for (int n = 1; n <= 9; ++n) for (int k = -1; k <= n+1; ++k) {
        for (int signs = 0; signs < 2; ++signs) {
            Formula f;
            std::vector<int> x;
            for (int i = 0; i < n; ++i) {
                int variable = f.variable();
                x.push_back(signs ? -variable : variable);
            }
            f.at_most(x, k);
            for (unsigned mask = 0; mask < (1u << n); ++mask) {
                std::vector<int> fixed;
                for (int i = 0; i < n; ++i) fixed.push_back(mask & (1u << i) ? i+1 : -(i+1));
                const int count = signs ? n-popcount(mask) : popcount(mask);
                require(f.solve_fixed(fixed) == (count <= k), "At-most projected encoding failed");
            }
        }
        Formula f;
        std::vector<int> x;
        for (int i = 0; i < n; ++i) x.push_back(f.variable());
        f.at_least(x, k);
        for (unsigned mask = 0; mask < (1u << n); ++mask) {
            std::vector<int> fixed;
            for (int i = 0; i < n; ++i) fixed.push_back(mask & (1u << i) ? i+1 : -(i+1));
            require(f.solve_fixed(fixed) == (popcount(mask) >= k), "At-least projected encoding failed");
        }
    }
    for (int n = 1; n <= 5; ++n) {
        std::vector<int> permutation(n);
        std::iota(permutation.begin(), permutation.end(), 0);
        do {
            Formula f;
            std::vector<int> x, y;
            for (int i = 0; i < n; ++i) x.push_back(f.variable());
            for (int p : permutation) y.push_back(x[p]);
            f.lex_leq(x, y);
            for (unsigned mask = 0; mask < (1u << n); ++mask) {
                std::vector<int> fixed, a, b;
                for (int i = 0; i < n; ++i) {
                    fixed.push_back(mask & (1u << i) ? i+1 : -(i+1));
                    a.push_back((mask >> i) & 1);
                    b.push_back((mask >> permutation[i]) & 1);
                }
                require(f.solve_fixed(fixed) == (a <= b), "Lex projected encoding failed");
            }
        } while (std::next_permutation(permutation.begin(), permutation.end()));
    }
    Graph k88(16);
    for (int i = 0; i < 16; ++i) for (int j = 0; j < 16; ++j)
        if ((i < 8) != (j < 8)) k88[i] |= 1u << j;
    require(valid_fan_coloring(k88), "Known order-16 fan-free witness rejected");
    Graph k7(7), empty9(9);
    for (int i = 0; i < 7; ++i) k7[i] = 127u ^ (1u << i);
    require(!valid_fan_coloring(k7), "Red F3 was missed");
    require(!valid_fan_coloring(empty9), "Blue F4 was missed");
    Graph9 k44{}, k45{};
    for (int i = 0; i < LEFT; ++i) for (int j = 0; j < LEFT; ++j)
        if ((i < 4) != (j < 4)) k44[i] |= std::uint16_t(1u << j);
    for (int i = 0; i < 9; ++i) for (int j = 0; j < 9; ++j)
        if ((i < 4) != (j < 4)) k45[i] |= std::uint16_t(1u << j);
    const SeedInfo left(k44, true, LEFT), right(k45, true, RIGHT);
    require(left.n == 8 && right.n == 9 && left.red[8] == 0 && left.blue[8] == 0,
            "Active seed order/padding is incorrect");
    require(left.automorphisms.order == 1152 && right.automorphisms.order == 2880,
            "Rectangular seed automorphism orders are incorrect");
    for (int colour = 0; colour < 2; ++colour) for (int k = 0; k <= 4; ++k)
        for (auto mask : left.matching_endpoints[colour][k])
            require((mask & 256u) == 0, "Order-8 endpoint mask contains padding");
    require(cross_variable(0, 8) == 1 && cross_variable(7, 16) == 72 &&
            cross_variable(16, 7) == 72, "Rectangular boundary indexing failed");
    std::array<bool, CROSS> seen{};
    for (int i = 0; i < LEFT; ++i) for (int j = 0; j < RIGHT; ++j) {
        const int variable = cross_variable(i, j+LEFT)-1;
        require(!seen[variable], "Duplicate cross variable");
        seen[variable] = true;
    }
    require(read_graph6("G?????") == Graph9{} && read_graph6("H??????") == Graph9{},
            "Order-8/9 graph6 empty graph parsing failed");
    const auto parsed_complete8 = read_graph6("G~~~~{");
    for (int v = 0; v < 8; ++v)
        require(parsed_complete8[v] == (255u ^ (1u << v)), "Order-8 graph6 bit order failed");
    require(parsed_complete8[8] == 0, "Graph6 reader did not zero padding");
    for (const std::string invalid : {"G????@", "G????", "H?????", "F?????"}) {
        bool rejected = false;
        try { (void)read_graph6(invalid); } catch (const std::invalid_argument&) { rejected = true; }
        require(rejected, "Malformed graph6 accepted");
    }
    SolveOptions options;
    options.symmetry = false;
    options.target_bounds = options.balanced = options.clique_cuts = options.initial_matching_cuts = false;
    options.fixed_cross.resize(CROSS);
    for (int i = 0; i < LEFT; ++i) for (int j = 0; j < RIGHT; ++j)
        options.fixed_cross[RIGHT*i+j] = ((i < 4) == (j < 4)); // red K8,9; blue K8 + K9
    Graph invalid17(TOTAL);
    for (int i = 0; i < LEFT; ++i) invalid17[i] = k44[i];
    for (int j = 0; j < RIGHT; ++j) invalid17[j+LEFT] = std::uint32_t(k45[j]) << LEFT;
    for (int i = 0; i < LEFT; ++i) for (int j = 0; j < RIGHT; ++j)
        if (options.fixed_cross[RIGHT*i+j]) {
            invalid17[i] |= 1u << (j+LEFT);
            invalid17[j+LEFT] |= 1u << i;
        }
    require(!valid_fan_coloring(invalid17), "Order-17 fixed blue K9 was missed");
    const auto lazy = solve_pair(left, right, options);
    require(lazy.status == "UNSAT" && lazy.iterations >= 1 && lazy.variables == CROSS,
            "Rectangular lazy fan cut did not reject fixed blue K9");
    options.target_bounds = options.balanced = options.clique_cuts = options.initial_matching_cuts = true;
    require(solve_pair(left, right, options).status == "UNSAT", "Initial rectangular cuts missed invalid fixture");
    options.fixed_cross.push_back(0);
    bool rejected_length = false;
    try { (void)solve_pair(left, right, options); }
    catch (const std::invalid_argument&) { rejected_length = true; }
    require(rejected_length, "Wrong fixed cross assignment length accepted");
    bool rejected_order = false;
    try { (void)solve_pair(right, left, options); }
    catch (const std::invalid_argument&) { rejected_order = true; }
    require(rejected_order, "Reversed 9+8 seed dimensions accepted");

    // A fixed internal blue K8 makes the whole order-17 instance impossible.
    // This also checks the symmetry setup without searching an unresolved pair.
    const SeedInfo blue_clique8(Graph9{}, true, 8);
    options = SolveOptions{};
    options.target_bounds = options.balanced = options.initial_matching_cuts = false;
    options.symmetry = false;
    const auto plain = solve_pair(blue_clique8, right, options);
    options.symmetry = true;
    const auto symmetric = solve_pair(blue_clique8, right, options);
    require(plain.status == "UNSAT" && symmetric.status == "UNSAT", "Fixed blue K8 regression failed");
    require(!symmetric.transpose_constraint && symmetric.symmetry_constraints > 0 &&
            symmetric.left_group_order == 40320 && symmetric.right_group_order == 2880,
            "Rectangular symmetry was omitted or transpose was applied");
}
} // namespace fan
