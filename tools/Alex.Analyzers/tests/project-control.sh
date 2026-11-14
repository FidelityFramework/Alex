#!/usr/bin/env bash
set -euo pipefail
tool_dir=$(cd -P "$(dirname "$0")/.." && pwd)
repo_dir=$(git -C "$tool_dir" rev-parse --show-toplevel)
evidence="$repo_dir/artifacts/alex-analyzers-tests/inproject-control"
mkdir -p "$evidence"
project="$tool_dir/tests/InProject/InProject.fsproj"
source="$tool_dir/tests/InProject/Cases.fs"
dialects_source="$tool_dir/tests/InProject/Dialects/Cases.fs"
elements_source="$tool_dir/tests/InProject/Elements/Cases.fs"
elements_clean_source="$tool_dir/tests/InProject/Elements/CleanCases.fs"
status=0
(cd "$tool_dir" && dotnet fsharp-analyzers --project "$project" --analyzers-path "$tool_dir/bin/Debug/net10.0" --include-analyzers 'Alex published boundary' --fail-on-type-errors) > "$evidence/analysis.log" 2>&1 || status=$?
[[ $status -ne 0 ]] || { printf 'In-project negative was not refused.\n' >&2; exit 1; }
[[ $(rg -c 'Error AX[AC][0-9]+' "$evidence/analysis.log" || true) -eq 26 ]] || { printf 'Unexpected in-project diagnostic count.\n' >&2; exit 1; }
rg -Fq "$source(7,6): Error AXA002 : Alex must not derive an admission predicate from a nominal declaration name." "$evidence/analysis.log" || { printf 'Missing in-project historical diagnostic.\n' >&2; exit 1; }
rg -Fq "$dialects_source(5,52): Error AXA003 : Alex must confine Revision.Nodes and Revision.tryNode to Traversal/, XParsec/, or Generation.fs (in 'badNodesAccess')." "$evidence/analysis.log" || { printf 'Missing in-project AXA003 diagnostic.\n' >&2; exit 1; }
rg -Fq "$dialects_source(7,8): Error AXA004 : Alex must not write recursive SemanticKind or Revision.Nodes catamorphisms outside Traversal/NanopassArchitecture.fs (tryWitnesses) (in 'badSemanticCata')." "$evidence/analysis.log" || { printf 'Missing in-project AXA004 diagnostic.\n' >&2; exit 1; }
rg -Fq "$dialects_source(13,14): Error AXA005 : Mutable local 'count' is forbidden in non-traversal Alex layers." "$evidence/analysis.log" || { printf 'Missing in-project AXA005 mutable diagnostic.\n' >&2; exit 1; }
rg -Fq "$dialects_source(18,13): Error AXA005 : Mutable ref cells (ref) are forbidden in non-traversal Alex layers." "$evidence/analysis.log" || { printf 'Missing in-project AXA005 ref diagnostic.\n' >&2; exit 1; }
rg -Fq "$dialects_source(22,2): Error AXA006 : Alex must not extract payloads from BoundaryImport.DeclarationFacts; only key-presence checks (ContainsKey / Map.containsKey) are permitted." "$evidence/analysis.log" || { printf 'Missing in-project AXA006 diagnostic.\n' >&2; exit 1; }
rg -Fq "$dialects_source(28,37): Error AXA007 : Alex must not collapse None from a published-fact or symbol lookup into a fallback value (in 'badFallbackDefault')." "$evidence/analysis.log" || { printf 'Missing in-project AXA007 diagnostic.\n' >&2; exit 1; }
! rg -Fq "$elements_clean_source" "$evidence/analysis.log" || { printf 'Unexpected diagnostic in allowed Elements fixture.\n' >&2; exit 1; }
[[ $(rg -c "$elements_source" "$evidence/analysis.log" || true) -eq 19 ]] || { printf 'Unexpected Elements negative diagnostic count.\n' >&2; exit 1; }
env -u DEPENDENCY_CONTROL_ONLY dotnet fsi "$tool_dir/tests/DependencyControls.fsx" > "$evidence/dependency.log" 2>&1
clef_status=0
bash "$tool_dir/check-project.sh" clef "$project" > "$evidence/clef-refusal.log" 2>&1 || clef_status=$?
[[ $clef_status -ne 0 ]] && rg -Fq 'Clef mode is suspended pending an owner convention for permitted dependency sets (P-dep4).' "$evidence/clef-refusal.log" || { printf 'Missing explicit clef dependency refusal.\n' >&2; exit 1; }
ratchet_dir="$evidence/ratchet"
rm -rf "$ratchet_dir"
mkdir -p "$ratchet_dir/src/Alex/Dialects/Core" "$ratchet_dir/src/Alex/Patterns"
ratchet_proj="$ratchet_dir/Alex.fsproj"
ratchet_corr="$ratchet_dir/src/Alex/Correspondence.fs"
ratchet_types="$ratchet_dir/src/Alex/Dialects/Core/Types.fs"
ratchet_mem="$ratchet_dir/src/Alex/Patterns/MemoryPatterns.fs"
psg_ref="$tool_dir/tests/ContractFixture/bin/Debug/net10.0/Fidelity.PSG.dll"
cat > "$ratchet_proj" <<EOF
<Project Sdk="Microsoft.NET.Sdk">
  <PropertyGroup>
    <TargetFramework>net10.0</TargetFramework>
    <OutputType>Library</OutputType>
    <ManagePackageVersionsCentrally>false</ManagePackageVersionsCentrally>
  </PropertyGroup>
  <ItemGroup>
    <Reference Include="Fidelity.PSG">
      <HintPath>$psg_ref</HintPath>
    </Reference>
    <Compile Include="src/Alex/Correspondence.fs" />
    <Compile Include="src/Alex/Dialects/Core/Types.fs" />
    <Compile Include="src/Alex/Patterns/MemoryPatterns.fs" />
  </ItemGroup>
</Project>
EOF
cat > "$ratchet_corr" <<'EOF'
module Alex.Correspondence
open Fidelity.PSG
let validateOccurrence () = 0
let newUnpinned (g: Revision) (id: NodeId) = g.Nodes.TryFind id
EOF
cat > "$ratchet_types" <<'EOF'
module Alex.Dialects.Core.Types
open Fidelity.PSG
let conditionalTagSelectionAt (g: Revision) (id: NodeId) (fb: SemanticNode) =
  let a = g.Nodes.TryFind id |> Option.defaultValue fb
  (a, Revision.tryNode id g, g.Nodes.TryFind id)
EOF
cat > "$ratchet_mem" <<'EOF'
module Alex.Patterns.MemoryPatterns
open Fidelity.PSG
let pArenaCreateIntrinsic (g: Revision) (id: NodeId) =
  (g.Nodes.TryFind id, Revision.tryNode id g)
EOF
ratchet_status=0
(cd "$tool_dir" && dotnet fsharp-analyzers --project "$ratchet_proj" --analyzers-path "$tool_dir/bin/Debug/net10.0" --include-analyzers 'Alex published boundary' --fail-on-type-errors) > "$evidence/ratchet.log" 2>&1 || ratchet_status=$?
[[ $ratchet_status -ne 0 ]] || { printf 'Ratchet negative was not refused.\n' >&2; exit 1; }
! rg -Fq "$ratchet_types" "$evidence/ratchet.log" || { printf 'Unexpected diagnostic on matched pin Types.fs.\n' >&2; exit 1; }
rg -Fq "$ratchet_corr(1,0): Error AXA003 : AXA003 ratchet mismatch: 'validateOccurrence' in 'Correspondence.fs' pins 1 site(s) but actual count is 0; tighten downward." "$evidence/ratchet.log" || { printf 'Missing AXA003 stale under-count ratchet mismatch diagnostic.\n' >&2; exit 1; }
rg -Fq "$ratchet_corr(4,45): Error AXA003 : Alex must confine Revision.Nodes and Revision.tryNode to Traversal/, XParsec/, or Generation.fs (unpinned 'newUnpinned' in 'Correspondence.fs')." "$evidence/ratchet.log" || { printf 'Missing AXA003 unpinned diagnostic.\n' >&2; exit 1; }
rg -Fq "$ratchet_mem(4,23): Error AXA003 : Alex must confine Revision.Nodes and Revision.tryNode to Traversal/, XParsec/, or Generation.fs ('pArenaCreateIntrinsic' in 'Patterns/MemoryPatterns.fs' has 2 sites, exceeding downward ratchet cap 1)." "$evidence/ratchet.log" || { printf 'Missing AXA003 over-cap diagnostic.\n' >&2; exit 1; }
[[ $(rg -F "$ratchet_corr(1,0): Error AXA003 : AXA003 stale ratchet pin:" "$evidence/ratchet.log" | sort -u | wc -l) -eq 24 ]] || { printf 'Unexpected distinct stale AXA003 ratchet pin count.\n' >&2; exit 1; }
sha256sum "$tool_dir/bin/Debug/net10.0/Alex.Analyzers.dll" "$tool_dir/ProjectInputs.fsx" "$tool_dir/check-project.sh" "$tool_dir/tests/ContractFixture/Contract.fs" "$tool_dir/tests/ContractFixture/ContractFixture.fsproj" "$tool_dir/tests/InProject/InProject.fsproj" "$tool_dir/tests/InProject/Ensure.fs" "$source" "$dialects_source" "$elements_source" "$elements_clean_source" "$tool_dir/tests/DependencyControls.fsx" "$tool_dir/tests/project-control.sh" "$evidence/analysis.log" "$evidence/dependency.log" "$evidence/clef-refusal.log" "$evidence/ratchet.log" > "$evidence/truth.sha256"
printf 'PASS in-project historical predicate and AXA003-AXA007 layer controls; clean controls clean\n'
