#!/usr/bin/env sh
set -eu
cd -- "$(dirname -- "$0")"

# Set CXX=g++ or CXX=clang++ if the default C++ compiler is not the desired one.
fan_cxx="${CXX:-c++}"
if ! command -v "$fan_cxx" >/dev/null 2>&1; then
    printf '%s\n' "C++ compiler not found: $fan_cxx. Load a C++17 compiler in the batch job, or set CXX to its executable path." >&2
    exit 1
fi
fan_probe_dir=$(mktemp -d "${TMPDIR:-/tmp}/fan-ramsey-build.XXXXXX")
trap 'rm -f -- "$fan_probe_dir/filesystem.cpp" "$fan_probe_dir/filesystem" "$fan_probe_dir/compiler.log"; rmdir -- "$fan_probe_dir"' EXIT
cat > "$fan_probe_dir/filesystem.cpp" <<'FAN_CPP'
#include <filesystem>
int main() { return std::filesystem::exists(std::filesystem::path(".")) ? 0 : 1; }
FAN_CPP
# GCC 8 needs an extra filesystem library; GCC 9+ generally does not.
# Probe by linking only. Do not run the probe or require network access.
if "$fan_cxx" -std=c++17 "$fan_probe_dir/filesystem.cpp" -o "$fan_probe_dir/filesystem" > "$fan_probe_dir/compiler.log" 2>&1; then
    set --
elif "$fan_cxx" -std=c++17 "$fan_probe_dir/filesystem.cpp" -o "$fan_probe_dir/filesystem" -lstdc++fs >> "$fan_probe_dir/compiler.log" 2>&1; then
    set -- -lstdc++fs
else
    cat "$fan_probe_dir/compiler.log" >&2
    printf '%s\n' 'A working C++17 compiler with std::filesystem is required. Ask the cluster administrator for the compiler module or path.' >&2
    exit 1
fi

# No architecture-specific flags; the output uses the host standard C++ runtime.
"$fan_cxx" -O3 -DNDEBUG -std=c++17 -pthread -DMINISAT_NO_ZLIB \
    -Ivendor -Ivendor/minisat -Ivendor/nlohmann \
    main.cpp fan_solver.cpp \
    vendor/minisat/minisat/core/Solver.cc \
    vendor/minisat/minisat/utils/Options.cc \
    vendor/minisat/minisat/utils/System.cc \
    "$@" -o fan_ramsey17
printf '%s\n' 'Built fan_ramsey17'
