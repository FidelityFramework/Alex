#!/usr/bin/env bash
set -euo pipefail
tool_dir=$(cd -P "$(dirname "$0")/.." && pwd)
repo_dir=$(git -C "$tool_dir" rev-parse --show-toplevel)
evidence="$repo_dir/artifacts/alex-analyzers-tests/inproject-control"
mkdir -p "$evidence"
project="$tool_dir/tests/InProject/InProject.fsproj"
source="$tool_dir/tests/InProject/Cases.fs"
status=0
(cd "$tool_dir" && dotnet fsharp-analyzers --project "$project" --analyzers-path "$tool_dir/bin/Debug/net10.0" --include-analyzers 'Alex published boundary' --fail-on-type-errors) > "$evidence/analysis.log" 2>&1 || status=$?
[[ $status -ne 0 ]] || { printf 'In-project negative was not refused.\n' >&2; exit 1; }
[[ $(rg -c 'Error AX[AC][0-9]+' "$evidence/analysis.log" || true) -eq 1 ]] || { printf 'Unexpected in-project diagnostic count.\n' >&2; exit 1; }
rg -Fq "$source(7,6): Error AXA002 : Alex must not derive an admission predicate from a nominal declaration name." "$evidence/analysis.log" || { printf 'Missing in-project historical diagnostic.\n' >&2; exit 1; }
env -u DEPENDENCY_CONTROL_ONLY dotnet fsi "$tool_dir/tests/DependencyControls.fsx" > "$evidence/dependency.log" 2>&1
clef_status=0
bash "$tool_dir/check-project.sh" clef "$project" > "$evidence/clef-refusal.log" 2>&1 || clef_status=$?
[[ $clef_status -ne 0 ]] && rg -Fq 'Clef mode is suspended pending an owner convention for permitted dependency sets (P-dep4).' "$evidence/clef-refusal.log" || { printf 'Missing explicit clef dependency refusal.\n' >&2; exit 1; }
sha256sum "$tool_dir/bin/Debug/net10.0/Alex.Analyzers.dll" "$tool_dir/ProjectInputs.fsx" "$tool_dir/check-project.sh" "$tool_dir/tests/ContractFixture/Contract.fs" "$tool_dir/tests/ContractFixture/ContractFixture.fsproj" "$tool_dir/tests/InProject/InProject.fsproj" "$tool_dir/tests/InProject/Ensure.fs" "$source" "$tool_dir/tests/DependencyControls.fsx" "$tool_dir/tests/project-control.sh" "$evidence/analysis.log" "$evidence/dependency.log" "$evidence/clef-refusal.log" > "$evidence/truth.sha256"
printf 'PASS in-project historical predicate; published-width control clean\n'
