#!/usr/bin/env bash
set -euo pipefail
export MSBUILDDISABLENODEREUSE=1

tool_dir=$(cd -P "$(dirname "$0")" && pwd)
repo_dir=$(git -C "$tool_dir" rev-parse --show-toplevel)
mode=${1:-}
case "$mode" in
  alex) analyzers=("Alex pure-core baseline" "Alex published boundary" "Alex dependency context") ;;
  alex-boundary) analyzers=("Alex published boundary") ;;
  *) printf 'Expected alex or alex-boundary mode.\n' >&2; exit 2 ;;
esac
# The published PSG boundary applies to tooling: https://forge.spkez.dev/FidelityFramework/Alex/wiki/01_Boundary
project="$repo_dir/src/Alex/Alex.fsproj"
requested_project=${2:-${ALEX_ANALYZER_PROJECT:-$project}}
[[ "$requested_project" = /* && "$requested_project" -ef "$project" && -f "$project" ]] || {
  printf 'Alex rules require the Alex production project in this checkout.\n' >&2; exit 2;
}

[[ -f "$tool_dir/bin/Debug/net10.0/Alex.Analyzers.dll" ]] || { printf 'Analyzer assembly is not built.\n' >&2; exit 1; }
receipt=${ALEX_ANALYZER_TRUTH_RECEIPT:-$repo_dir/artifacts/alex-analyzers-tests/latest-truth.sha256}
[[ -f "$receipt" ]] && sha256sum --check --status "$receipt" || { printf 'Truth receipt is missing or does not bind current inputs.\n' >&2; exit 1; }
truth_json_rows=$(grep -E '^[0-9a-f]{64}  .*/artifacts/alex-analyzers-tests/run\.[^/]+/truth\.json$' "$receipt" || true)
[[ $(printf '%s\n' "$truth_json_rows" | sed '/^$/d' | wc -l) -eq 1 ]] || { printf 'Truth receipt does not bind truth.json.\n' >&2; exit 1; }
truth_json_path=${truth_json_rows#*  }
[[ -f "$truth_json_path" ]] && jq -e '(.executed | type == "number" and . >= 302) and (.cases | type == "array") and ((.cases | length) == .executed)' "$truth_json_path" > /dev/null 2>&1 || { printf 'Truth receipt truth.json is missing or invalid.\n' >&2; exit 1; }
inproject_receipt="$repo_dir/artifacts/alex-analyzers-tests/inproject-control/truth.sha256"
[[ -f "$inproject_receipt" ]] && sha256sum --check --status "$inproject_receipt" || { printf 'In-project control receipt failed verification.\n' >&2; exit 1; }
for required in "$tool_dir/bin/Debug/net10.0/Alex.Analyzers.dll" "$tool_dir/Analyzer.fs" "$tool_dir/tests/run.sh" "$tool_dir/.config/dotnet-tools.json" "$tool_dir/check-project.sh" "$tool_dir/ProjectInputs.fsx" "$tool_dir/VerifyProjectLog.fsx" "$tool_dir/Alex.Analyzers.fsproj" "$tool_dir/Directory.Packages.props" "$tool_dir/packages.lock.json" "$tool_dir/NuGet.Config" "$tool_dir/tests/ContractFixture/Contract.fs" "$tool_dir/tests/ContractFixture/ContractFixture.fsproj" "$tool_dir/tests/ContractFixture/bin/Debug/net10.0/Fidelity.PSG.dll" "$tool_dir/tests/ImpostorFixture/ImpostorFixture.fsproj" "$tool_dir/tests/ImpostorFixture/bin/Debug/net10.0/Unrelated.Contract.dll" "$tool_dir/tests/AlexFixture/Ensure.fs" "$tool_dir/tests/AlexFixture/AlexFixture.fsproj" "$tool_dir/tests/AlexFixture/bin/Debug/net10.0/Alex.dll"; do
  binding=$(sha256sum "$required")
  grep -Fqx "$binding" "$receipt" || { printf 'Truth receipt does not bind %s.\n' "$required" >&2; exit 1; }
done
for required in "$tool_dir/tests/StaleContract/Contract.fs" "$tool_dir/tests/StaleContract/StaleContract.fsproj" "$tool_dir/tests/StaleContract/bin/Debug/net10.0/Fidelity.PSG.dll" "$tool_dir/tests/AlexFixture/packages.lock.json" "$tool_dir/tests/InProject/InProject.fsproj" "$tool_dir/tests/InProject/Ensure.fs" "$tool_dir/tests/InProject/Cases.fs" "$tool_dir/tests/InProject/Dialects/Cases.fs" "$tool_dir/tests/InProject/Elements/Cases.fs" "$tool_dir/tests/InProject/Elements/CleanCases.fs" "$tool_dir/tests/InProject/Patterns/Cases.fs" "$tool_dir/tests/InProject/Witnesses/Cases.fs" "$tool_dir/tests/InProject/Traversal/Values.fs" "$tool_dir/tests/DependencyControls.fsx" "$tool_dir/tests/project-control.sh" "$tool_dir/analyze-alex.sh" "$repo_dir/artifacts/alex-analyzers-tests/inproject-control/truth.sha256"; do
  binding=$(sha256sum "$required")
  grep -Fqx "$binding" "$receipt" || { printf 'Truth receipt does not bind %s.\n' "$required" >&2; exit 1; }
done
for required in "$tool_dir/tests/AliasFixture/Aliases.fs" "$tool_dir/tests/AliasFixture/AliasFixture.fsproj" "$tool_dir/tests/AliasFixture/packages.lock.json" "$tool_dir/tests/AliasFixture/bin/Debug/net10.0/AliasFixture.dll"; do
  binding=$(sha256sum "$required")
  grep -Fqx "$binding" "$receipt" || { printf 'Truth receipt does not bind %s.\n' "$required" >&2; exit 1; }
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
  properties=AlexBoundaryPermitted,AlexBoundaryAlsoPermitted,AlexPermittedPackages,PsgContractProject,PsgContractLibrary,Configuration,Platform,NetCoreTargetingPackRoot,NETCoreSdkVersion,NetCoreRoot,MSBuildExtensionsPath,IntermediateOutputPath,GeneratedAssemblyInfoFile,TargetFrameworkMonikerAssemblyAttributesPath,GenerateAssemblyInfo,GenerateTargetFrameworkAttribute,TargetFrameworkMoniker
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
  "$host" fsi "$tool_dir/ProjectInputs.fsx" --compare-project-context "$scratch/report.sarif" "$scratch/references.json" "$scratch/dependencies.txt" "$scratch/inputs.txt" "$scratch/restore-graph.json" > "$scratch/loader-context.txt"
  "$host" msbuild -noAutoResponse "$project" -property:Configuration=Debug -property:Platform=AnyCPU "-preprocess:$scratch/preprocess-after-analysis.xml" > "$scratch/preprocess-after-analysis.log"
  "$host" fsi "$tool_dir/ProjectInputs.fsx" --compare-preprocess "$scratch/preprocess-before.xml" "$scratch/preprocess-after-analysis.xml"
  sha256sum "$scratch/preprocess-after-analysis.xml" "$scratch/items.json" "$scratch/inputs.txt" "$scratch/report.sarif" "$scratch/analysis.log" "$scratch/loader-context.txt" >> "$scratch/dependencies.sha256"
fi
printf 'Evidence: %s\n' "$scratch"
exit "$status"
