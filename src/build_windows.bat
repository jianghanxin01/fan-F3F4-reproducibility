@echo off
setlocal
cd /d "%~dp0"
where cl.exe >nul 2>nul
if errorlevel 1 (
    echo Microsoft C++ compiler not found.
    echo Open "x64 Native Tools Command Prompt for VS 2022", change to this directory,
    echo and run build_windows.bat again.
    exit /b 2
)
if defined VSCMD_ARG_TGT_ARCH if /I not "%VSCMD_ARG_TGT_ARCH%"=="x64" (
    echo Please use the x64 Native Tools Command Prompt.
    exit /b 2
)
if not exist build_windows mkdir build_windows
if errorlevel 1 exit /b 1
pushd build_windows
cl /nologo /O2 /DNDEBUG /EHsc /std:c++17 /utf-8 /MT ^
    /DMINISAT_NO_ZLIB /D_CRT_SECURE_NO_WARNINGS ^
    /I"..\vendor" /I"..\vendor\minisat" /I"..\vendor\nlohmann" ^
    ..\main.cpp ..\fan_solver.cpp ^
    ..\vendor\minisat\minisat\core\Solver.cc ^
    ..\vendor\minisat\minisat\utils\Options.cc ^
    ..\vendor\minisat\minisat\utils\System.cc ^
    /Fe:"..\fan_ramsey17.exe"
set "build_exit=%errorlevel%"
popd
if not "%build_exit%"=="0" exit /b %build_exit%
echo Built fan_ramsey17.exe
exit /b 0
