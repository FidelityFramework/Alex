#!/usr/bin/env bash
set -euo pipefail
export MSBUILDDISABLENODEREUSE=1

tool_dir=$(cd -P "$(dirname "$0")" && pwd)
repo_dir=$(git -C "$tool_dir" rev-parse --show-toplevel)
mode=${1:?expected alex, alex-boundary or clef}
if [[ "$mode" == alex || "$mode" == alex-boundary ]]; then
  project=${2:-${ALEX_ANALYZER_PROJECT:-$repo_dir/src/Alex/Alex.fsproj}}
else
  project=${2:-${ALEX_ANALYZER_PROJECT:?set ALEX_ANALYZER_PROJECT or supply an absolute F# project path}}
fi
[[ "$project" = /* && -f "$project" ]] || { printf 'Project must be an existing absolute path.\n' >&2; exit 2; }
project=$(realpath "$project")
case "$mode" in
  alex|alex-boundary)
    alex_project=$(realpath "${ALEX_ANALYZER_PROJECT:-$repo_dir/src/Alex/Alex.fsproj}")
    [[ "$project" == "$alex_project" ]] || { printf 'Alex rules require the configured Alex production project.\n' >&2; exit 2; }
    if [[ "$mode" == alex ]]; then analyzers=("Clef production baseline" "Alex published boundary"); else analyzers=("Alex published boundary"); fi
    ;;
  clef) printf 'Clef mode is suspended pending an owner convention for permitted dependency sets (P-dep4).\n' >&2; exit 2 ;;
  *) printf 'Expected alex, alex-boundary or clef mode.\n' >&2; exit 2 ;;
esac

[[ -f "$tool_dir/bin/Debug/net10.0/Alex.Analyzers.dll" ]] || { printf 'Analyzer assembly is not built.\n' >&2; exit 1; }
receipt=${ALEX_ANALYZER_TRUTH_RECEIPT:-$repo_dir/artifacts/alex-analyzers-tests/latest-truth.sha256}
[[ -f "$receipt" ]] && sha256sum --check --status "$receipt" || { printf 'Truth receipt is missing or does not bind current inputs.\n' >&2; exit 1; }
for required in "$tool_dir/bin/Debug/net10.0/Alex.Analyzers.dll" "$tool_dir/Analyzer.fs" "$tool_dir/tests/run.sh" "$tool_dir/.config/dotnet-tools.json" "$tool_dir/check-project.sh" "$tool_dir/ProjectInputs.fsx" "$tool_dir/VerifyProjectLog.fsx" "$tool_dir/Alex.Analyzers.fsproj" "$tool_dir/Directory.Packages.props" "$tool_dir/packages.lock.json" "$tool_dir/NuGet.Config" "$tool_dir/tests/ContractFixture/Contract.fs" "$tool_dir/tests/ContractFixture/ContractFixture.fsproj" "$tool_dir/tests/ContractFixture/bin/Debug/net10.0/Fidelity.PSG.dll" "$tool_dir/tests/ImpostorFixture/ImpostorFixture.fsproj" "$tool_dir/tests/ImpostorFixture/bin/Debug/net10.0/Unrelated.Contract.dll" "$tool_dir/tests/AlexFixture/Ensure.fs" "$tool_dir/tests/AlexFixture/AlexFixture.fsproj" "$tool_dir/tests/AlexFixture/bin/Debug/net10.0/Alex.dll"; do
  binding=$(sha256sum "$required")
  rg -Fqx "$binding" "$receipt" || { printf 'Truth receipt does not bind %s.\n' "$required" >&2; exit 1; }
done
for required in "$tool_dir/tests/StaleContract/Contract.fs" "$tool_dir/tests/StaleContract/StaleContract.fsproj" "$tool_dir/tests/StaleContract/bin/Debug/net10.0/Fidelity.PSG.dll" "$tool_dir/tests/InProject/InProject.fsproj" "$tool_dir/tests/InProject/Ensure.fs" "$tool_dir/tests/InProject/Cases.fs" "$tool_dir/tests/DependencyControls.fsx" "$tool_dir/tests/project-control.sh" "$tool_dir/analyze-alex.sh" "$repo_dir/artifacts/alex-analyzers-tests/inproject-control/truth.sha256"; do
  binding=$(sha256sum "$required")
  rg -Fqx "$binding" "$receipt" || { printf 'Truth receipt does not bind %s.\n' "$required" >&2; exit 1; }
done
for required in "$tool_dir/tests/AliasFixture/Aliases.fs" "$tool_dir/tests/AliasFixture/AliasFixture.fsproj" "$tool_dir/tests/AliasFixture/packages.lock.json" "$tool_dir/tests/AliasFixture/bin/Debug/net10.0/AliasFixture.dll"; do
  binding=$(sha256sum "$required")
  rg -Fqx "$binding" "$receipt" || { printf 'Truth receipt does not bind %s.\n' "$required" >&2; exit 1; }
done
mkdir -p "$repo_dir/artifacts/alex-analyzers-tests"
scratch=$(mktemp -d "$repo_dir/artifacts/alex-analyzers-tests/project.XXXXXXXX")
cd "$tool_dir"
host=$(dotnet fsi "$tool_dir/ProjectInputs.fsx" --host)
[[ "$host" = /* && -x "$host" ]] || { printf 'Cannot identify executing dotnet host.\n' >&2; exit 2; }
if [[ "$mode" == alex ]]; then
  [[ -n ${HOME:-} ]] || { printf 'Cannot establish the retained HOME trust input.\n' >&2; exit 2; }
  host_root=$(dirname "$host")
  scrub=(env -i "HOME=$HOME" 'PATH=/usr/bin:/bin' "DOTNET_ROOT=$host_root" 'MSBUILDDISABLENODEREUSE=1')
  printf 'normal-HOME=%s\nnormal-PATH=%s\nnormal-DOTNET_ROOT=%s\nnormal-DOTNET_CLI_HOME=%s\nnormal-NUGET_PACKAGES=%s\nscrub-HOME=%s\nscrub-PATH=/usr/bin:/bin\nscrub-DOTNET_ROOT=%s\nMSBUILDDISABLENODEREUSE=1\nmsbuild-noAutoResponse=true\n' "$HOME" "${PATH:-<unset>}" "${DOTNET_ROOT:-<unset>}" "${DOTNET_CLI_HOME:-<unset>}" "${NUGET_PACKAGES:-<unset>}" "$HOME" "$host_root" > "$scratch/retained-environment.txt"
  "$host" msbuild -noAutoResponse "$project" -property:Configuration=Debug -property:Platform=AnyCPU "-preprocess:$scratch/preprocess-before.xml" > "$scratch/preprocess-before.log"
  "${scrub[@]}" "$host" msbuild -noAutoResponse "$project" -property:Configuration=Debug -property:Platform=AnyCPU "-preprocess:$scratch/preprocess-scrubbed.xml" > "$scratch/preprocess-scrubbed.log"
  "$host" fsi "$tool_dir/ProjectInputs.fsx" --compare-preprocess "$scratch/preprocess-before.xml" "$scratch/preprocess-scrubbed.xml"
  "$host" msbuild -noAutoResponse "$project" -property:Configuration=Debug -property:Platform=AnyCPU -target:GenerateRestoreGraphFile "-property:RestoreGraphOutputPath=$scratch/restore-graph.json" > "$scratch/restore-graph.log"
  "${scrub[@]}" "$host" msbuild -noAutoResponse "$project" -property:Configuration=Debug -property:Platform=AnyCPU -target:GenerateRestoreGraphFile "-property:RestoreGraphOutputPath=$scratch/restore-graph-scrubbed.json" > "$scratch/restore-graph-scrubbed.log"
  properties=AlexBoundaryPermitted,AlexBoundaryAlsoPermitted,AlexPermittedPackages,PsgContractProject,PsgContractLibrary,Configuration,Platform,NetCoreTargetingPackRoot,NETCoreSdkVersion,NetCoreRoot,MSBuildExtensionsPath
  "$host" msbuild -noAutoResponse "$project" -property:Configuration=Debug -property:Platform=AnyCPU -target:ResolveReferences -getItem:ResolvedTargetingPack,ReferencePath "-getProperty:$properties" > "$scratch/references.json"
  "${scrub[@]}" "$host" msbuild -noAutoResponse "$project" -property:Configuration=Debug -property:Platform=AnyCPU -target:ResolveReferences -getItem:ResolvedTargetingPack,ReferencePath "-getProperty:$properties" > "$scratch/references-scrubbed.json"
  "$host" fsi "$tool_dir/ProjectInputs.fsx" --check-owner-properties "$scratch/references.json"
  "$host" fsi "$tool_dir/ProjectInputs.fsx" --compare-references "$scratch/references.json" "$scratch/references-scrubbed.json"
  "$host" fsi "$tool_dir/ProjectInputs.fsx" --compare-graph "$scratch/restore-graph.json" "$scratch/restore-graph-scrubbed.json"
  "$host" fsi "$tool_dir/ProjectInputs.fsx" --dependencies "$project" "$scratch/restore-graph.json" "$scratch/references.json" "$scratch/dependencies.txt"
  "$host" msbuild -noAutoResponse "$project" -property:Configuration=Debug -property:Platform=AnyCPU "-preprocess:$scratch/preprocess-after.xml" > "$scratch/preprocess-after.log"
  "$host" fsi "$tool_dir/ProjectInputs.fsx" --compare-preprocess "$scratch/preprocess-before.xml" "$scratch/preprocess-after.xml"
  sha256sum "$scratch/restore-graph.json" "$scratch/restore-graph-scrubbed.json" "$scratch/references.json" "$scratch/references-scrubbed.json" "$scratch/dependencies.txt" "$scratch/preprocess-before.xml" "$scratch/preprocess-scrubbed.xml" "$scratch/preprocess-after.xml" "$scratch/retained-environment.txt" > "$scratch/dependencies.sha256"
fi
"$host" msbuild -noAutoResponse "$project" -property:Configuration=Debug -property:Platform=AnyCPU -getItem:Compile > "$scratch/items.json"
"$host" fsi "$tool_dir/ProjectInputs.fsx" "$scratch/items.json" "$scratch/inputs.txt"
mapfile -t sources < "$scratch/inputs.txt"
set +e
"$host" fsharp-analyzers --project "$project" --analyzers-path "$tool_dir/bin/Debug/net10.0" \
  --include-analyzers "${analyzers[@]}" --include-files "${sources[@]}" --fail-on-type-errors --verbosity d --report "$scratch/report.sarif" \
  2>&1 | tee "$scratch/analysis.log"
status=${PIPESTATUS[0]}
set -e
[[ -f "$scratch/report.sarif" ]] || { printf 'Analyzer did not produce SARIF (exit %s).\n' "$status" >&2; exit 1; }
if [[ $status -ne 0 ]]; then printf 'Analyzer exited %s; see %s.\n' "$status" "$scratch/analysis.log" >&2; fi
"$host" fsi "$tool_dir/VerifyProjectLog.fsx" "$scratch/inputs.txt" "$scratch/analysis.log" "$mode"
if [[ "$mode" == alex ]]; then
  "$host" msbuild -noAutoResponse "$project" -property:Configuration=Debug -property:Platform=AnyCPU "-preprocess:$scratch/preprocess-after-analysis.xml" > "$scratch/preprocess-after-analysis.log"
  "$host" fsi "$tool_dir/ProjectInputs.fsx" --compare-preprocess "$scratch/preprocess-before.xml" "$scratch/preprocess-after-analysis.xml"
  sha256sum "$scratch/preprocess-after-analysis.xml" >> "$scratch/dependencies.sha256"
fi
printf 'Evidence: %s\n' "$scratch"
exit "$status"
