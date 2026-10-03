#pragma once

// Exact seed automorphism groups and safe (partial) gluing symmetry breaking.
// C++17, no external dependencies.  Eight rows, nine columns; index row*9+column.
#include <algorithm>
#include <array>
#include <cstddef>
#include <cstdint>
#include <map>
#include <numeric>
#include <stdexcept>
#include <utility>
#include <vector>

namespace fan_symmetry {

using Graph9 = std::array<std::uint16_t, 9>;
using VertexPermutation = std::array<int, 9>;
using CrossPermutation = std::array<int, 72>;

struct AutomorphismDiagnostics {
    std::uint64_t search_nodes = 0;
    std::uint32_t existence_queries = 0;
    std::uint32_t successful_queries = 0;
    std::array<int, 9> stabilizer_orbit_sizes{};
};

struct AutomorphismGroup {
    // These generators generate the complete seed automorphism group.
    // They are stabilizer transversals, not necessarily a minimal generating set.
    std::vector<VertexPermutation> generators;
    std::uint64_t order = 1;
    AutomorphismDiagnostics diagnostics;
};

struct GluingSymmetryDiagnostics {
    std::uint64_t left_group_order = 1;
    std::uint64_t right_group_order = 1;
    std::size_t available_permutations = 0;
    std::size_t selected_permutations = 0;
    bool swap_eligible = false;
    bool swap_included = false;
    // Even all generators' lex inequalities need not select one point per orbit.
    bool full_isomorphism_elimination = false;
};

inline int bit_count(std::uint16_t x) {
    int n = 0;
    while (x) { x &= static_cast<std::uint16_t>(x - 1); ++n; }
    return n;
}

inline VertexPermutation identity_vertex_permutation() {
    VertexPermutation p{};
    std::iota(p.begin(), p.end(), 0);
    return p;
}

inline void validate_graph(const Graph9& g, int order = 9) {
    if (order != 8 && order != 9)
        throw std::invalid_argument("Seed order must be 8 or 9");
    const auto all = std::uint16_t((1u << order)-1);
    for (int u = 0; u < 9; ++u) {
        if ((u >= order && g[u]) || (g[u] & ~all) != 0 || ((g[u] >> u) & 1))
            throw std::invalid_argument("Graph9 has a loop or out-of-range bit");
        for (int v = u + 1; v < 9; ++v)
            if (((g[u] >> v) & 1) != ((g[v] >> u) & 1))
                throw std::invalid_argument("Graph9 adjacency is not symmetric");
    }
}

inline bool is_automorphism(const Graph9& g, const VertexPermutation& p, int order = 9) {
    if (order != 8 && order != 9) return false;
    unsigned used = 0;
    for (int u = 0; u < 9; ++u) {
        if (p[u] < 0 || p[u] >= 9 || (used & (1u << p[u]))) return false;
        if ((u < order && p[u] >= order) || (u >= order && p[u] != u)) return false;
        used |= 1u << p[u];
    }
    for (int u = 0; u < 9; ++u)
        for (int v = u + 1; v < 9; ++v)
            if (((g[u] >> v) & 1) != ((g[p[u]] >> p[v]) & 1)) return false;
    return true;
}

namespace detail {

// Stable degree/neighbour-colour refinement is an automorphism invariant.
inline std::array<int, 9> refined_colours(const Graph9& g, int order) {
    std::array<int, 9> colour{};
    for (int u = 0; u < 9; ++u) colour[u] = bit_count(g[u]);
    for (;;) {
        std::array<std::array<int, 10>, 9> signature{};
        for (int u = 0; u < 9; ++u) {
            signature[u][0] = colour[u];
            for (int v = 0; v < 9; ++v)
                if ((g[u] >> v) & 1) ++signature[u][1 + colour[v]];
        }
        auto sorted = signature;
        std::sort(sorted.begin(), sorted.begin()+order);
        const auto last = std::unique(sorted.begin(), sorted.begin()+order);
        std::array<int, 9> next{};
        for (int u = 0; u < order; ++u)
            next[u] = static_cast<int>(std::lower_bound(sorted.begin(), last,
                                                       signature[u]) - sorted.begin());
        if (next == colour) return colour;
        colour = next;
    }
}

class AutomorphismSearch {
    const Graph9& g_;
    int order_;
    std::array<int, 9> colour_;
    VertexPermutation image_{};
    unsigned used_ = 0;
    AutomorphismDiagnostics& diagnostics_;

    bool compatible(int u, int v) const {
        if (colour_[u] != colour_[v] || (used_ & (1u << v))) return false;
        for (int w = 0; w < 9; ++w)
            if (image_[w] >= 0 && (((g_[u] >> w) & 1) !=
                                   ((g_[v] >> image_[w]) & 1))) return false;
        return true;
    }

    bool search() {
        ++diagnostics_.search_nodes;
        int chosen = -1;
        unsigned choices = 0;
        int fewest = 10;
        // Minimum remaining values reduces unsuccessful existence queries.
        for (int u = 0; u < order_; ++u) {
            if (image_[u] >= 0) continue;
            unsigned candidates = 0;
            for (int v = 0; v < order_; ++v)
                if (compatible(u, v)) candidates |= 1u << v;
            const int count = bit_count(static_cast<std::uint16_t>(candidates));
            if (count == 0) return false;
            if (count < fewest) {
                chosen = u; choices = candidates; fewest = count;
            }
        }
        if (chosen < 0) return true;
        for (int v = 0; v < order_; ++v) {
            if (!(choices & (1u << v))) continue;
            image_[chosen] = v;
            used_ |= 1u << v;
            if (search()) return true;
            used_ &= ~(1u << v);
            image_[chosen] = -1;
        }
        return false;
    }

public:
    AutomorphismSearch(const Graph9& g, int order, AutomorphismDiagnostics& diagnostics)
        : g_(g), order_(order), colour_(refined_colours(g, order)), diagnostics_(diagnostics) {}

    bool same_colour(int u, int v) const { return colour_[u] == colour_[v]; }

    // Find an automorphism fixing 0,...,base-1 and mapping base to target.
    bool find(int base, int target, VertexPermutation& output) {
        ++diagnostics_.existence_queries;
        image_.fill(-1);
        used_ = 0;
        // Padding is outside the active graph, even when active vertices are isolated.
        for (int u = order_; u < 9; ++u) {
            image_[u] = u; used_ |= 1u << u;
        }
        for (int u = 0; u < base; ++u) {
            image_[u] = u; used_ |= 1u << u;
        }
        if (!compatible(base, target)) return false;
        image_[base] = target;
        used_ |= 1u << target;
        if (!search()) return false;
        ++diagnostics_.successful_queries;
        output = image_;
        return true;
    }
};

inline void add_edge(Graph9& g, int u, int v) {
    g[u] |= std::uint16_t(1u << v);
    g[v] |= std::uint16_t(1u << u);
}

} // namespace detail

inline AutomorphismGroup automorphism_group(const Graph9& g, int order = 9) {
    validate_graph(g, order);
    AutomorphismGroup result;
    result.diagnostics.stabilizer_orbit_sizes.fill(1);
    detail::AutomorphismSearch search(g, order, result.diagnostics);
    for (int base = 0; base < order; ++base) {
        int orbit_size = 1; // The identity maps base to itself.
        for (int target = base + 1; target < order; ++target) {
            if (!search.same_colour(base, target)) continue;
            VertexPermutation p{};
            if (!search.find(base, target, p)) continue;
            if (!is_automorphism(g, p, order))
                throw std::logic_error("Automorphism backtracking invariant failed");
            ++orbit_size;
            result.generators.push_back(p);
        }
        result.diagnostics.stabilizer_orbit_sizes[base] = orbit_size;
        result.order *= static_cast<std::uint64_t>(orbit_size);
    }
    // Let G_i fix vertices 0,...,i-1.  The searches give one representative
    // of every nonidentity coset of G_(i+1) in G_i.  Their union generates G_0;
    // orbit-stabilizer gives |G_0| = product_i |i^(G_i)|.  At most 36
    // representatives are needed, even when |G_0| = 9!.
    return result;
}

// Optional cache.  Obtain groups once per seed; concurrent callers must lock
// this cache externally (or keep one cache per worker).
class AutomorphismCache {
    std::map<std::pair<int, Graph9>, AutomorphismGroup> cache_;
public:
    const AutomorphismGroup& get(const Graph9& g, int order = 9) {
        const auto key = std::make_pair(order, g);
        auto it = cache_.find(key);
        if (it == cache_.end()) it = cache_.emplace(key, automorphism_group(g, order)).first;
        return it->second;
    }
    std::size_t size() const { return cache_.size(); }
};

inline std::vector<CrossPermutation> gluing_permutations(
        const Graph9& left, const Graph9& right,
        const AutomorphismGroup& left_group,
        const AutomorphismGroup& right_group,
        std::size_t cap = 73, bool include_swap = true,
        GluingSymmetryDiagnostics* diagnostics = nullptr) {
    validate_graph(left, 8);
    validate_graph(right, 9);
    (void)include_swap; // Unequal part sizes never permit a transpose.
    GluingSymmetryDiagnostics info;
    info.left_group_order = left_group.order;
    info.right_group_order = right_group.order;
    info.swap_eligible = false;
    info.available_permutations = left_group.generators.size() +
                                  right_group.generators.size();
    std::vector<CrossPermutation> result;
    result.reserve(std::min(cap, info.available_permutations));

    // Alternate row and column generators when a small cap is requested.
    const std::size_t count = std::max(left_group.generators.size(),
                                       right_group.generators.size());
    for (std::size_t k = 0; k < count && result.size() < cap; ++k) {
        for (int side = 0; side < 2 && result.size() < cap; ++side) {
            const auto& generators = side == 0 ? left_group.generators
                                               : right_group.generators;
            if (k >= generators.size()) continue;
            if (!is_automorphism(side == 0 ? left : right, generators[k], side == 0 ? 8 : 9))
                throw std::invalid_argument("Gluing generator moves padding or is not an automorphism");
            CrossPermutation p{};
            for (int i = 0; i < 8; ++i)
                for (int j = 0; j < 9; ++j)
                    p[9 * i + j] = side == 0 ? 9 * generators[k][i] + j
                                             : 9 * i + generators[k][j];
            result.push_back(p);
        }
    }
    info.selected_permutations = result.size();
    if (diagnostics) *diagnostics = info;
    // p maps an old variable index to its image.  Either convention x[p[i]]
    // or x[p^{-1}[i]] is sound if used consistently, since inverses are also
    // symmetries.  Add x <=lex (x[p[0]],...,x[p[71]]) with 0 < 1.
    // Every full-group orbit has a lexicographically least element; it obeys
    // all these inequalities.  Therefore no orbit of feasible gluings is lost.
    // Generator inequalities alone generally leave multiple orbit members.
    return result;
}

inline std::vector<CrossPermutation> gluing_permutations(
        const Graph9& left, const Graph9& right,
        std::size_t cap = 73, bool include_swap = true,
        GluingSymmetryDiagnostics* diagnostics = nullptr) {
    const auto a = automorphism_group(left, 8);
    const auto b = automorphism_group(right, 9);
    return gluing_permutations(left, right, a, b, cap, include_swap, diagnostics);
}

inline void run_self_tests() {
    auto require = [](bool ok, const char* message) {
        if (!ok) throw std::logic_error(message);
    };
    Graph9 empty{}, complete{}, path{}, cycle{}, bipartite{};
    for (int i = 0; i < 9; ++i) {
        complete[i] = std::uint16_t(511 ^ (1u << i));
        if (i < 8) detail::add_edge(path, i, i + 1);
        detail::add_edge(cycle, i, (i + 1) % 9);
        for (int j = 4; i < 4 && j < 9; ++j)
            detail::add_edge(bipartite, i, j);
    }
    const std::array<Graph9, 5> graphs{empty, complete, path, cycle, bipartite};
    const std::array<std::uint64_t, 5> orders{362880, 362880, 2, 18, 2880};
    for (std::size_t i = 0; i < graphs.size(); ++i) {
        const auto group = automorphism_group(graphs[i]);
        require(group.order == orders[i], "Incorrect known automorphism order");
        require(group.generators.size() <= 36, "Too many stabilizer generators");
        for (const auto& p : group.generators)
            require(is_automorphism(graphs[i], p), "Invalid automorphism generator");
    }

    // Independent direct permutation enumeration checks an asymmetric fixture.
    Graph9 irregular{};
    const std::array<std::array<int, 2>, 19> edges{{
        {{0,1}}, {{0,2}}, {{0,4}}, {{0,7}}, {{1,2}}, {{1,3}}, {{1,5}},
        {{2,3}}, {{2,4}}, {{2,8}}, {{3,4}}, {{3,6}}, {{4,5}}, {{4,7}},
        {{5,6}}, {{5,8}}, {{6,7}}, {{6,8}}, {{7,8}}
    }};
    for (const auto& edge : edges) detail::add_edge(irregular, edge[0], edge[1]);
    auto p = identity_vertex_permutation();
    std::uint64_t brute_order = 0;
    do { if (is_automorphism(irregular, p)) ++brute_order; }
    while (std::next_permutation(p.begin(), p.end()));
    require(brute_order == 1, "Asymmetric fixture unexpectedly has a symmetry");
    require(automorphism_group(irregular).order == brute_order,
            "Stabilizer order disagrees with independent enumeration");

    Graph9 empty8{}, complete8{}, path8{}, cycle8{}, bipartite8{};
    for (int i = 0; i < 8; ++i) {
        complete8[i] = std::uint16_t(255 ^ (1u << i));
        if (i < 7) detail::add_edge(path8, i, i+1);
        detail::add_edge(cycle8, i, (i+1)%8);
        for (int j = 4; i < 4 && j < 8; ++j) detail::add_edge(bipartite8, i, j);
    }
    const std::array<Graph9, 5> graphs8{empty8, complete8, path8, cycle8, bipartite8};
    const std::array<std::uint64_t, 5> orders8{40320, 40320, 2, 16, 1152};
    for (std::size_t i = 0; i < graphs8.size(); ++i) {
        const auto group = automorphism_group(graphs8[i], 8);
        require(group.order == orders8[i], "Incorrect order-8 automorphism order");
        require(group.generators.size() <= 28, "Too many order-8 generators");
        for (const auto& generator : group.generators)
            require(generator[8] == 8 && is_automorphism(graphs8[i], generator, 8),
                    "Order-8 generator moves inactive padding");
    }
    auto moves_dummy = identity_vertex_permutation();
    std::swap(moves_dummy[0], moves_dummy[8]);
    require(!is_automorphism(empty8, moves_dummy, 8), "Isolated dummy was allowed to move");
    AutomorphismCache cache;
    require(cache.get(empty8, 8).order == 40320 && cache.get(empty8, 9).order == 362880 && cache.size() == 2,
            "Automorphism cache conflates padded orders");

    GluingSymmetryDiagnostics diagnostics;
    const auto symmetries = gluing_permutations(bipartite8, bipartite, 73, true,
                                               &diagnostics);
    require(!diagnostics.swap_eligible && !diagnostics.swap_included, "Rectangular parts were swapped");
    for (const auto& cross : symmetries) {
        auto sorted = cross;
        std::sort(sorted.begin(), sorted.end());
        for (int k = 0; k < 72; ++k)
            require(sorted[k] == k, "Cross action is not a permutation");
    }
    const auto capped = gluing_permutations(empty, empty, 1, true, &diagnostics);
    require(capped.size() == 1 && !diagnostics.swap_included,
            "Capped rectangular symmetry list is incorrect");
    gluing_permutations(empty, complete, 73, true, &diagnostics);
    require(!diagnostics.swap_eligible && !diagnostics.swap_included,
            "Unequal labelled seeds were incorrectly swapped");
    gluing_permutations(empty, empty, 0, true, &diagnostics);
    require(diagnostics.selected_permutations == 0 && !diagnostics.swap_included,
            "Zero symmetry cap was ignored");
}

} // namespace fan_symmetry
