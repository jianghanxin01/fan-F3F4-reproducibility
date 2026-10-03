#pragma once
#include "symmetry.hpp"
#include <array>
#include <cstdint>
#include <string>
#include <vector>

namespace fan {
using Graph9 = fan_symmetry::Graph9;
using Graph = std::vector<std::uint32_t>;

struct SeedInfo {
    int n = 9; // Active order; Graph9 is padded with a fixed zero vertex at order 8.
    Graph9 red{}, blue{};
    std::array<int, 9> degree{};
    std::array<std::array<int, 9>, 2> internal_nu{}; // colour 0=red, 1=blue
    std::array<std::array<std::uint16_t, 9>, 2> free_vertices{};
    std::array<std::array<std::vector<std::uint16_t>, 5>, 2> matching_endpoints;
    fan_symmetry::AutomorphismGroup automorphisms;
    bool automorphisms_ready = false;
    explicit SeedInfo(const Graph9& graph, bool compute_automorphisms = true, int order = 9);
};

struct SolveOptions {
    double seconds = 5.0;
    bool symmetry = true;
    std::size_t symmetry_cap = 73;
    bool target_bounds = true;
    bool balanced = true;
    bool clique_cuts = true;
    bool initial_matching_cuts = true;
    std::string dump_cnf;
    // Empty in production. Test/projection audit can fix all 72 original variables.
    std::vector<int> fixed_cross;
};

struct SolveResult {
    std::string status = "UNKNOWN";
    double setup_seconds = 0.0, total_seconds = 0.0;
    std::uint64_t iterations = 0, clauses = 0, variables = 0;
    std::uint64_t symmetry_constraints = 0;
    std::uint64_t left_group_order = 1, right_group_order = 1;
    bool transpose_constraint = false;
    bool has_witness = false;
    std::array<std::uint32_t, 17> red{};
};

Graph9 read_graph6(const std::string& line);
bool valid_fan_coloring(const Graph& red);
SolveResult solve_pair(const SeedInfo& left, const SeedInfo& right, const SolveOptions& options);
void self_test_core();
} // namespace fan
