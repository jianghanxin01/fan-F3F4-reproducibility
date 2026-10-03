R(F3,F4): REPRODUCIBILITY MATERIAL

Start with docs/reproducibility_guide.pdf (editable LaTeX also supplied).
It gives complete build, cluster, restart, retry, merge, seed-regeneration
and certificate-regeneration instructions. Run commands from this directory.

QUICK CHECK (Python 3.9+, standard library only)
  python3 verify40.py
Expected: all 40 fixed cases excluded; report results/verified40.json.

BUILD BOTH PROGRAMS (C++17, CMake 3.15+)
  cmake -S src -B build -DCMAKE_BUILD_TYPE=Release
  cmake --build build --config Release --parallel 4
  ./build/fan_ramsey17 self-test
  ./build/fan_ramsey17 catalog --data data
For Visual Studio use build\Release\fan_ramsey17.exe and an x64 developer
terminal. The guide also documents the supplied direct-build scripts.
Those scripts build the main search program only. To compile the certificate
program directly, create build/ first and use one of these commands:
  Linux: c++ -O3 -std=c++17 src/csp_rows.cpp -o build/fan_tail_certify
  Windows x64 developer terminal:
  cl /nologo /O2 /EHsc /std:c++17 /utf-8 /MT src\csp_rows.cpp /Fo:build\csp_rows.obj /Fe:build\fan_tail_certify.exe
For the direct Windows build, the binary is build/fan_tail_certify.exe.

REGENERATE THE LOCAL CERTIFICATES
  python3 tools/regenerate_certificates.py --binary build/fan_tail_certify --output generated_certificates --seconds 120
On Windows use build/Release/fan_tail_certify.exe. The output directory must
be empty. Generation is followed automatically by independent verification.

CHECK A COMPLETE FRESH MERGED RUN
  python3 combine_results.py --results results/merged_01 --output results/combined.json
Every task is checked; any remaining UNKNOWN must belong to the fixed forty
verified cases. This command does not change the original checkpoints.

CONTENTS
src/          Search/generator source, portable builds and vendor licences.
data/         Two graph6 libraries, catalogue and dataset identity.
tools/        Complete seed/profile generation and independent checkers.
certificates/ Forty fixed cases and final counting/finite-domain certificates.
docs/         Detailed English reproducibility guide, PDF and LaTeX.

SCOPE
The fixed data contain 88,294,674 ordered 8+9 seed pairs. The quick check
verifies 34 counting exclusions and six finite-domain certificates. It does
not verify all earlier bulk UNSAT decisions or prove catalogue completeness.
The full-run combiner preserves that distinction. No historical checkpoints,
research logs, binaries or intermediate experiments are included.

Original third-party licences: src/vendor/minisat/LICENSE and
src/vendor/nlohmann/LICENSE.MIT. Upstream identities and portability patches
are recorded in src/THIRD_PARTY_NOTICES.txt and src/vendor/minisat/.
