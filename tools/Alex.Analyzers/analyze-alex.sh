#!/usr/bin/env bash
set -euo pipefail

tool_dir=$(cd -P "$(dirname "$0")" && pwd)
repo_dir=$(git -C "$tool_dir" rev-parse --show-toplevel)
bozzetto_dir=$(cd -P "${BOZZETTO_DIR:-$repo_dir/../Bozzetto}" && pwd)
lease_script="$bozzetto_dir/tools/build/lease.fsx"
[[ -f "$lease_script" ]] || { printf 'Missing Bozzetto lease runner: %s\n' "$lease_script" >&2; exit 2; }
ALEX_ANALYZER_PROJECT=${ALEX_ANALYZER_PROJECT:-$repo_dir/src/Alex/Alex.fsproj}
[[ "$ALEX_ANALYZER_PROJECT" = /* && -f "$ALEX_ANALYZER_PROJECT" ]] || { printf 'Alex project must be an existing absolute path.\n' >&2; exit 2; }
export ALEX_ANALYZER_PROJECT
export BOZZETTO_PROJECT="$ALEX_ANALYZER_PROJECT"
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
