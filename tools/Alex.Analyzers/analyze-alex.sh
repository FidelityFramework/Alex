#!/usr/bin/env bash
set -euo pipefail

tool_dir=$(cd -P "$(dirname "$0")" && pwd)
repo_dir=$(git -C "$tool_dir" rev-parse --show-toplevel)
project="$repo_dir/src/Alex/Alex.fsproj"
requested_project=${ALEX_ANALYZER_PROJECT:-$project}
[[ "$requested_project" = /* && "$requested_project" -ef "$project" && -f "$project" ]] || {
  printf 'Alex rules require the Alex production project in this checkout.\n' >&2; exit 2;
}
bozzetto_dir=$(cd -P "${BOZZETTO_DIR:-$repo_dir/../Bozzetto}" && pwd)
lease_script="$bozzetto_dir/tools/build/lease.fsx"
[[ -f "$lease_script" ]] || { printf 'Missing Bozzetto lease runner: %s\n' "$lease_script" >&2; exit 2; }
export ALEX_ANALYZER_PROJECT="$project"
export BOZZETTO_PROJECT="$project"
cd "$tool_dir"
lease() { dotnet fsi "$lease_script" "$@"; }
lease full_build dotnet tool restore
lease full_build dotnet build Alex.Analyzers.fsproj
lease full_build dotnet build tests/ContractFixture/ContractFixture.fsproj
lease full_build dotnet build tests/ImpostorFixture/ImpostorFixture.fsproj
lease full_build dotnet build tests/AlexFixture/AlexFixture.fsproj
lease full_build dotnet build tests/StaleContract/StaleContract.fsproj
lease full_build dotnet build tests/AliasFixture/AliasFixture.fsproj
lease full_build bash tests/project-control.sh
lease test_suite_run bash tests/run.sh --pipeline
lease full_build bash check-project.sh alex-boundary
lease full_build bash check-project.sh alex
