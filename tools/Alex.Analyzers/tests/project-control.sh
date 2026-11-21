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
patterns_source="$tool_dir/tests/InProject/Patterns/Cases.fs"
witnesses_source="$tool_dir/tests/InProject/Witnesses/Cases.fs"
values_source="$tool_dir/tests/InProject/Traversal/Values.fs"
ensure_source="$tool_dir/tests/InProject/Ensure.fs"
if [[ ${1:-} == --scoped-loader ]]; then
  scoped=$(mktemp -d "$evidence/scoped-loader.XXXXXXXX")
else
  scoped="$evidence/scoped-loader"
fi
mkdir -p "$scoped/fixture/NativeTypedTree"
scoped_project="$scoped/fixture/Scoped.fsproj"
export ScopedProvenanceFixtureProject="$tool_dir/tests/ContractFixture/ContractFixture.fsproj"
cat > "$scoped_project" <<'PROJECT'
<Project Sdk="Microsoft.NET.Sdk">
  <PropertyGroup><TargetFramework>net10.0</TargetFramework><DisableImplicitFSharpCoreReference>true</DisableImplicitFSharpCoreReference><NuGetAudit>false</NuGetAudit></PropertyGroup>
  <ItemGroup>
    <ProjectReference Include="$(ScopedProvenanceFixtureProject)" />
    <Reference Include="FSharp.Core" HintPath="$(MSBuildToolsPath)/FSharp/FSharp.Core.dll" />
    <Compile Include="NativeTypedTree/First.fs" /><Compile Include="Host.fs" /><Compile Include="Last.fs" Link="Baker/Last.fs" />
  </ItemGroup>
</Project>
PROJECT
printf "module First\nlet value = 1\n" > "$scoped/fixture/NativeTypedTree/First.fs"
printf "module Host\nlet package () = typeof<System.IO.File>.Assembly\n" > "$scoped/fixture/Host.fs"
printf "module Last\nlet value = First.value + 1\n" > "$scoped/fixture/Last.fs"
dotnet msbuild "$scoped_project" -noAutoResponse -restore -property:Configuration=Debug -property:Platform=AnyCPU -target:Build -property:ProvideCommandLineArgs=true -getItem:Compile,ReferencePathWithRefAssemblies,ProjectReference > "$scoped/loader.json"
inputs=(dotnet fsi "$tool_dir/ProjectInputs.fsx")
"${inputs[@]}" --capture-loader "$scoped_project" "$scoped/loader.json" "$scoped/loader.tsv"
first="$scoped/fixture/NativeTypedTree/First.fs"; last="$scoped/fixture/Last.fs"
dotnet msbuild "$scoped_project" -noAutoResponse -getItem:Compile > "$scoped/authored.json"
"${inputs[@]}" --clef-sources "$scoped_project" "$scoped/authored.json" "$scoped/selected.txt"
diff -u <(printf "%s\n" "$first" "$last" | sort) "$scoped/selected.txt"
(cd "$tool_dir" && dotnet fsharp-analyzers --project "$scoped_project" --analyzers-path "$tool_dir/bin/Debug/net10.0" --include-analyzers "Alex dependency context" --include-files "$first" "$last" --fail-on-type-errors --verbosity d --report "$scoped/report.sarif") > "$scoped/analysis.log" 2>&1
dotnet fsi "$tool_dir/VerifyProjectLog.fsx" "$scoped/selected.txt" "$scoped/analysis.log" clef-provenance "$scoped/visited.txt"
ln -sfn "$first" "$scoped/selected-alias.fs"
printf "%s\n" "$scoped/selected-alias.fs" "$last" > "$scoped/aliases.txt"
verify=( "${inputs[@]}" --verify-scoped-loader )
"${verify[@]}" "$scoped/report.sarif" "$scoped/loader.tsv" "$scoped/aliases.txt" "$scoped/visited.txt" > "$scoped/verified.log"
grep -Fq 'AXD000 provenance only: 2 analyzed files' "$scoped/verified.log"
refuses() {
  local name=$1 reason=$2; shift 2
  if "${verify[@]}" "$@" > "$scoped/$name.log" 2>&1; then printf 'Unexpected successful scoped check: %s\n' "$name" >&2; return 1; fi
  grep -Fq "Dependency evidence incomplete: $reason" "$scoped/$name.log"
}
printf '%s\n' '{"runs":[{"results":[]}]}' > "$scoped/empty.sarif"
refuses empty 'missing loader context records' "$scoped/empty.sarif" "$scoped/loader.tsv" "$scoped/aliases.txt" "$scoped/visited.txt"
printf '%s\n' "$first" > "$scoped/omitted.txt"
refuses omitted 'analyzed source coverage mismatch' "$scoped/report.sarif" "$scoped/loader.tsv" "$scoped/omitted.txt" "$scoped/visited.txt"
awk -F'\t' '$1=="source" && !swapped { if (!held) {held=$0;next} print;print held;swapped=1;next }{print}' "$scoped/loader.tsv" > "$scoped/reordered.tsv"
refuses reordered 'loader source order mismatch' "$scoped/report.sarif" "$scoped/reordered.tsv" "$scoped/aliases.txt" "$scoped/visited.txt"
awk -F'\t' '$1=="reference" && !removed {removed=1;next}{print}' "$scoped/loader.tsv" > "$scoped/omitted-ref.tsv"
refuses omitted-reference 'loader reference coverage mismatch' "$scoped/report.sarif" "$scoped/omitted-ref.tsv" "$scoped/aliases.txt" "$scoped/visited.txt"
awk -F'\t' '$1!="project-reference"{print}' "$scoped/loader.tsv" > "$scoped/omitted-project.tsv"
refuses omitted-project 'loader project reference coverage mismatch' "$scoped/report.sarif" "$scoped/omitted-project.tsv" "$scoped/aliases.txt" "$scoped/visited.txt"
unset ScopedProvenanceFixtureProject
awk -F'\t' 'BEGIN{OFS="\t"} $1=="reference" && !replaced {$3=prev;replaced=1} {print;prev=$3}' "$scoped/loader.tsv" > "$scoped/replaced.tsv"
refuses replaced 'loader input changed after evaluation' "$scoped/report.sarif" "$scoped/replaced.tsv" "$scoped/aliases.txt" "$scoped/visited.txt"
if [[ ${1:-} == --scoped-loader ]]; then exit 0; fi
status=0
(cd "$tool_dir" && dotnet fsharp-analyzers --project "$project" --analyzers-path "$tool_dir/bin/Debug/net10.0" --include-analyzers 'Alex published boundary' --fail-on-type-errors) > "$evidence/analysis.log" 2>&1 || status=$?
[[ $status -ne 0 ]] || { printf 'In-project refusal case was not refused.\n' >&2; exit 1; }
[[ $(rg 'Error AX[AC][0-9]+' "$evidence/analysis.log" | wc -l) -eq 48 ]] || { printf 'Unexpected in-project diagnostic count.\n' >&2; exit 1; }
rg -Fq "$source(7,6): Error AXA002 : Alex must not derive an admission predicate from a nominal declaration name." "$evidence/analysis.log" || { printf 'Missing in-project historical diagnostic.\n' >&2; exit 1; }
rg -Fq "$dialects_source(5,52): Error AXA003 : Alex must confine Revision.Nodes and Revision.tryNode to Traversal/, XParsec/, or Generation.fs (in 'badNodesAccess')." "$evidence/analysis.log" || { printf 'Missing in-project AXA003 diagnostic.\n' >&2; exit 1; }
rg -Fq "$dialects_source(7,8): Error AXA004 : Alex must not write recursive SemanticKind or Revision.Nodes catamorphisms outside Traversal/NanopassArchitecture.fs (tryWitnesses) (in 'badSemanticCata')." "$evidence/analysis.log" || { printf 'Missing in-project AXA004 diagnostic.\n' >&2; exit 1; }
rg -Fq "$dialects_source(13,14): Error AXA005 : Mutable local 'count' is forbidden in non-traversal Alex layers." "$evidence/analysis.log" || { printf 'Missing in-project AXA005 mutable diagnostic.\n' >&2; exit 1; }
rg -Fq "$dialects_source(18,13): Error AXA005 : Mutable ref cells (ref) are forbidden in non-traversal Alex layers." "$evidence/analysis.log" || { printf 'Missing in-project AXA005 ref diagnostic.\n' >&2; exit 1; }
rg -Fq "$dialects_source(22,2): Error AXA006 : Alex must not extract payloads from BoundaryImport.DeclarationFacts; only key-presence checks (ContainsKey / Map.containsKey) are permitted." "$evidence/analysis.log" || { printf 'Missing in-project AXA006 diagnostic.\n' >&2; exit 1; }
rg -Fq "$dialects_source(28,37): Error AXA007 : Alex must not collapse None from a published-fact or symbol lookup into a fallback value (in 'badFallbackDefault')." "$evidence/analysis.log" || { printf 'Missing in-project AXA007 diagnostic.\n' >&2; exit 1; }
rg -Fq "$dialects_source(38,28): Error AXA009 : Alex must not construct an SSA union case outside Traversal/Values.fs (in 'badSsaConstruction')." "$evidence/analysis.log" || { printf 'Missing in-project AXA009 SSA construction diagnostic.\n' >&2; exit 1; }
rg -Fq "$dialects_source(41,2): Error AXA009 : Alex must take SSA names from getNodeSSA / getNodeSSAs; direct uses of the SSA-producing members of Alex.Traversal.Values are confined to Traversal/Values.fs and XParsec/PSGCombinators.fs (in 'badValuesDirect')." "$evidence/analysis.log" || { printf 'Missing in-project AXA009 Values.value diagnostic.\n' >&2; exit 1; }
rg -Fq "$dialects_source(41,36): Error AXA009 : Alex must take SSA names from getNodeSSA / getNodeSSAs; direct uses of the SSA-producing members of Alex.Traversal.Values are confined to Traversal/Values.fs and XParsec/PSGCombinators.fs (in 'badValuesDirect')." "$evidence/analysis.log" || { printf 'Missing in-project AXA009 Values.continuationValue diagnostic.\n' >&2; exit 1; }
rg -Fq "$elements_source(12,79): Error AXA008 : Alex must not call MLIRAccumulator.bind*, completeVoid, forgetVoid, restoreOperands or registerSSAType, or assign an MLIRAccumulator property, outside Traversal/TransferTypes.fs and Traversal/NanopassArchitecture.fs (in 'badAccumulatorAssign')." "$evidence/analysis.log" || { printf 'Missing in-project Elements AXA008 property assignment diagnostic.\n' >&2; exit 1; }
rg -Fq "$patterns_source(7,2): Error AXA008 : Alex must not call MLIRAccumulator.bind*, completeVoid, forgetVoid, restoreOperands or registerSSAType, or assign an MLIRAccumulator property, outside Traversal/TransferTypes.fs and Traversal/NanopassArchitecture.fs (in 'badBindNode')." "$evidence/analysis.log" || { printf 'Missing in-project Patterns AXA008 bindNode diagnostic.\n' >&2; exit 1; }
rg -Fq "$patterns_source(10,2): Error AXA008 : Alex must not call MLIRAccumulator.bind*, completeVoid, forgetVoid, restoreOperands or registerSSAType, or assign an MLIRAccumulator property, outside Traversal/TransferTypes.fs and Traversal/NanopassArchitecture.fs (in 'badAccumulatorAssign')." "$evidence/analysis.log" || { printf 'Missing in-project Patterns AXA008 property assignment diagnostic.\n' >&2; exit 1; }
rg -Fq "$patterns_source(13,2): Error AXA010 : Alex must not call NanopassArchitecture.visitAllNodes or ScopeContext.root / createChild / addOp / addOps / enterScope / exitScope in Patterns/ or in a Witnesses/ function that is not a pinned scope boundary (in 'badVisitAll')." "$evidence/analysis.log" || { printf 'Missing in-project Patterns AXA010 visitAllNodes diagnostic.\n' >&2; exit 1; }
rg -Fq "$patterns_source(16,2): Error AXA010 : Alex must not call NanopassArchitecture.visitAllNodes or ScopeContext.root / createChild / addOp / addOps / enterScope / exitScope in Patterns/ or in a Witnesses/ function that is not a pinned scope boundary (in 'badScopeTransition')." "$evidence/analysis.log" || { printf 'Missing in-project Patterns AXA010 exitScope diagnostic.\n' >&2; exit 1; }
rg -Fq "$patterns_source(16,41): Error AXA010 : Alex must not call NanopassArchitecture.visitAllNodes or ScopeContext.root / createChild / addOp / addOps / enterScope / exitScope in Patterns/ or in a Witnesses/ function that is not a pinned scope boundary (in 'badScopeTransition')." "$evidence/analysis.log" || { printf 'Missing in-project Patterns AXA010 enterScope diagnostic.\n' >&2; exit 1; }
rg -Fq "$patterns_source(19,2): Error AXA010 : Alex must not call SMTTransfer.operations or SMTTransfer.transfer in Patterns/ or Witnesses/ (in 'badSmtTransfer')." "$evidence/analysis.log" || { printf 'Missing in-project Patterns AXA010 SMTTransfer.operations diagnostic.\n' >&2; exit 1; }
rg -Fq "$patterns_source(19,53): Error AXA010 : Alex must not call SMTTransfer.operations or SMTTransfer.transfer in Patterns/ or Witnesses/ (in 'badSmtTransfer')." "$evidence/analysis.log" || { printf 'Missing in-project Patterns AXA010 SMTTransfer.transfer diagnostic.\n' >&2; exit 1; }
rg -Fq "$witnesses_source(7,14): Error AXA005 : Mutable locals, mutable bindings and ref cells are forbidden in Witnesses/ (in 'badMutableLocal')." "$evidence/analysis.log" || { printf 'Missing in-project Witnesses AXA005 mutable local diagnostic.\n' >&2; exit 1; }
rg -Fq "$witnesses_source(12,13): Error AXA005 : Mutable locals, mutable bindings and ref cells are forbidden in Witnesses/ (in 'badRefCell')." "$evidence/analysis.log" || { printf 'Missing in-project Witnesses AXA005 ref cell diagnostic.\n' >&2; exit 1; }
rg -Fq "$witnesses_source(16,2): Error AXA008 : Alex must not call MLIRAccumulator.bind*, completeVoid, forgetVoid, restoreOperands or registerSSAType, or assign an MLIRAccumulator property, outside Traversal/TransferTypes.fs and Traversal/NanopassArchitecture.fs (in 'badBindNode')." "$evidence/analysis.log" || { printf 'Missing in-project Witnesses AXA008 bindNode diagnostic.\n' >&2; exit 1; }
rg -Fq "$witnesses_source(19,2): Error AXA010 : Alex must not call NanopassArchitecture.visitAllNodes or ScopeContext.root / createChild / addOp / addOps / enterScope / exitScope in Patterns/ or in a Witnesses/ function that is not a pinned scope boundary (in 'badVisitAll')." "$evidence/analysis.log" || { printf 'Missing in-project Witnesses AXA010 visitAllNodes diagnostic.\n' >&2; exit 1; }
rg -Fq "$dialects_source(47,2): Error AXA008 : Alex must not call MLIRAccumulator.bind*, completeVoid, forgetVoid, restoreOperands or registerSSAType, or assign an MLIRAccumulator property, outside Traversal/TransferTypes.fs and Traversal/NanopassArchitecture.fs (in 'badRegisterType')." "$evidence/analysis.log" || { printf 'Missing in-project Dialects AXA008 registerSSAType diagnostic.\n' >&2; exit 1; }
rg -Fq "$dialects_source(50,2): Error AXA009 : Alex must take SSA names from getNodeSSA / getNodeSSAs; direct uses of the SSA-producing members of Alex.Traversal.Values are confined to Traversal/Values.fs and XParsec/PSGCombinators.fs (in 'badValuesMembers')." "$evidence/analysis.log" || { printf 'Missing in-project AXA009 Values.resultOf diagnostic.\n' >&2; exit 1; }
rg -Fq "$dialects_source(50,37): Error AXA009 : Alex must take SSA names from getNodeSSA / getNodeSSAs; direct uses of the SSA-producing members of Alex.Traversal.Values are confined to Traversal/Values.fs and XParsec/PSGCombinators.fs (in 'badValuesMembers')." "$evidence/analysis.log" || { printf 'Missing in-project AXA009 Values.undefined diagnostic.\n' >&2; exit 1; }
rg -Fq "$patterns_source(30,2): Error AXA008 : Alex must not call MLIRAccumulator.bind*, completeVoid, forgetVoid, restoreOperands or registerSSAType, or assign an MLIRAccumulator property, outside Traversal/TransferTypes.fs and Traversal/NanopassArchitecture.fs (in 'badForgetVoid')." "$evidence/analysis.log" || { printf 'Missing in-project Patterns AXA008 forgetVoid diagnostic.\n' >&2; exit 1; }
rg -Fq "$patterns_source(33,2): Error AXA010 : Alex must not call NanopassArchitecture.visitAllNodes or ScopeContext.root / createChild / addOp / addOps / enterScope / exitScope in Patterns/ or in a Witnesses/ function that is not a pinned scope boundary (in 'badScopeContext')." "$evidence/analysis.log" || { printf 'Missing in-project Patterns AXA010 ScopeContext.addOps diagnostic.\n' >&2; exit 1; }
rg -Fq "$patterns_source(33,55): Error AXA010 : Alex must not call NanopassArchitecture.visitAllNodes or ScopeContext.root / createChild / addOp / addOps / enterScope / exitScope in Patterns/ or in a Witnesses/ function that is not a pinned scope boundary (in 'badScopeContext')." "$evidence/analysis.log" || { printf 'Missing in-project Patterns AXA010 ScopeContext.root diagnostic.\n' >&2; exit 1; }
rg -Fq "$witnesses_source(26,2): Error AXA010 : Alex must not call SMTTransfer.operations or SMTTransfer.transfer in Patterns/ or Witnesses/ (in 'badSmtTransfer')." "$evidence/analysis.log" || { printf 'Missing in-project Witnesses AXA010 SMTTransfer.operations diagnostic.\n' >&2; exit 1; }
! rg -Fq "$values_source" "$evidence/analysis.log" || { printf 'Unexpected diagnostic in the Traversal/Values.fs acceptance case.\n' >&2; exit 1; }
! rg -Fq "$ensure_source" "$evidence/analysis.log" || { printf 'Unexpected diagnostic in the in-project stub file.\n' >&2; exit 1; }
[[ $(rg -F "$dialects_source" "$evidence/analysis.log" | wc -l) -eq 12 ]] || { printf 'Unexpected Dialects diagnostic count.\n' >&2; exit 1; }
[[ $(rg -F "$patterns_source" "$evidence/analysis.log" | wc -l) -eq 10 ]] || { printf 'Unexpected Patterns diagnostic count.\n' >&2; exit 1; }
[[ $(rg -F "$witnesses_source" "$evidence/analysis.log" | wc -l) -eq 5 ]] || { printf 'Unexpected Witnesses diagnostic count.\n' >&2; exit 1; }
! rg -Fq "$elements_clean_source" "$evidence/analysis.log" || { printf 'Unexpected diagnostic in allowed Elements fixture.\n' >&2; exit 1; }
[[ $(rg -F "$elements_source" "$evidence/analysis.log" | wc -l) -eq 20 ]] || { printf 'Unexpected Elements refusal case diagnostic count.\n' >&2; exit 1; }
env -u DEPENDENCY_CONTROL_ONLY dotnet fsi "$tool_dir/tests/DependencyControls.fsx" > "$evidence/dependency.log" 2>&1
clef_status=0
bash "$tool_dir/check-project.sh" clef "$project" > "$evidence/clef-refusal.log" 2>&1 || clef_status=$?
[[ $clef_status -ne 0 ]] && rg -Fq 'Clef mode is suspended pending an owner convention for permitted dependency sets (P-dep4).' "$evidence/clef-refusal.log" || { printf 'Missing explicit clef dependency refusal.\n' >&2; exit 1; }
ratchet_dir="$evidence/ratchet"
rm -rf "$ratchet_dir"
mkdir -p "$ratchet_dir/src/Alex/Dialects/Core" "$ratchet_dir/src/Alex/Patterns" "$ratchet_dir/src/Alex/Traversal" "$ratchet_dir/src/Alex/Witnesses"
ratchet_proj="$ratchet_dir/Alex.fsproj"
ratchet_corr="$ratchet_dir/src/Alex/Correspondence.fs"
ratchet_types="$ratchet_dir/src/Alex/Dialects/Core/Types.fs"
ratchet_mem="$ratchet_dir/src/Alex/Patterns/MemoryPatterns.fs"
ratchet_values="$ratchet_dir/src/Alex/Traversal/Values.fs"
ratchet_transfer="$ratchet_dir/src/Alex/Traversal/TransferTypes.fs"
ratchet_new_traversal="$ratchet_dir/src/Alex/Traversal/NewTraversal.fs"
ratchet_new_patterns="$ratchet_dir/src/Alex/Patterns/NewPatterns.fs"
ratchet_literal="$ratchet_dir/src/Alex/Witnesses/LiteralWitness.fs"
ratchet_match="$ratchet_dir/src/Alex/Witnesses/MatchWitness.fs"
ratchet_new_witness="$ratchet_dir/src/Alex/Witnesses/NewWitness.fs"
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
    <Compile Include="src/Alex/Traversal/Values.fs" />
    <Compile Include="src/Alex/Traversal/TransferTypes.fs" />
    <Compile Include="src/Alex/Traversal/NewTraversal.fs" />
    <Compile Include="src/Alex/Patterns/NewPatterns.fs" />
    <Compile Include="src/Alex/Witnesses/LiteralWitness.fs" />
    <Compile Include="src/Alex/Witnesses/MatchWitness.fs" />
    <Compile Include="src/Alex/Witnesses/NewWitness.fs" />
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
type SSA =
  | V of node: int * ordinal: int
  | Arg of int
EOF
cat > "$ratchet_mem" <<'EOF'
module Alex.Patterns.MemoryPatterns
open Fidelity.PSG
let pArenaCreateIntrinsic (g: Revision) (id: NodeId) =
  (g.Nodes.TryFind id, Revision.tryNode id g)
EOF
cat > "$ratchet_values" <<'EOF'
module Alex.Traversal.Values
open Fidelity.PSG
open Alex.Dialects.Core.Types
let value (NodeId node) (k: int) : SSA = V (node, k)
let values (id: NodeId) : SSA list = [ value id 0; value id 1 ]
let prologueValue (id: NodeId) (k: int) : SSA = value id (2000 + k)
EOF
cat > "$ratchet_transfer" <<'EOF'
namespace Alex.Traversal
module ScopeContext =
  type ScopeLevel = ModuleLevel | FunctionLevel | BlockLevel
  type ScopeContext = { Id: int64; Level: ScopeLevel; Parent: ScopeContext option }
  module ScopeContext =
    let root () : ScopeContext = { Id = 1L; Level = ModuleLevel; Parent = None }
    let createChild (parent: ScopeContext) (level: ScopeLevel) : ScopeContext = { Id = parent.Id + 1L; Level = level; Parent = Some parent }
module TransferTypes =
  type MLIRAccumulator() =
    member val WitnessScope: string option = None with get, set
    member val EmittedDefinitions: string list = [] with get, set
    member val WitnessEmissions: string list = [] with get, set
    member val AllOps: string list = [] with get, set
    member val Errors: string list = [] with get, set
    member val BoundaryScopes: Set<int> = Set.empty with get, set
    member val NodeAssoc: Map<int, string> = Map.empty with get, set
    member val CallableAssoc: Map<int, string> = Map.empty with get, set
    member val CallableCellAssoc: Map<int, string> = Map.empty with get, set
    member val SequenceAssoc: Map<int, string> = Map.empty with get, set
    member val LazyAssoc: Map<int, string> = Map.empty with get, set
    member val VoidAssoc: Map<int, string> = Map.empty with get, set
    member val SSATypes: Map<string, string> = Map.empty with get, set
    member val EmittedGlobals: Set<string> = Set.empty with get, set
    member val EmittedGlobalContents: Map<string, string> = Map.empty with get, set
    member val EmittedStaticGlobals: Map<string, string> = Map.empty with get, set
    member val PendingStaticGlobals: string list = [] with get, set
    member val RegionBufferAssoc: Map<int, string> = Map.empty with get, set
    member acc.OperationCount = List.length acc.AllOps
  module MLIRAccumulator =
    let bindNode (_: Fidelity.PSG.NodeId) (_: Alex.Dialects.Core.Types.SSA) (ty: string) (acc: MLIRAccumulator) = acc.SSATypes <- acc.SSATypes.Add(ty, ty)
    let registerSSAType (_: Alex.Dialects.Core.Types.SSA) (ty: string) (acc: MLIRAccumulator) = acc.SSATypes <- acc.SSATypes.Add(ty, ty)
  let meetFor (id: Fidelity.PSG.NodeId) = Alex.Traversal.Values.value id 0
  let requireSSA (id: Fidelity.PSG.NodeId) = Alex.Traversal.Values.value id 0
  let requireSSAs (id: Fidelity.PSG.NodeId) = Alex.Traversal.Values.values id
module NanopassArchitecture =
  let visitAllNodes (witness: Fidelity.PSG.SemanticNode -> unit) (node: Fidelity.PSG.SemanticNode) : unit = witness node
module SMTTransfer =
  let operations (obligations: string list) : Result<string list, string> = Result.Ok obligations
  let transfer (obligations: string list) : Result<string, string> = Result.Ok (String.concat ";" obligations)
EOF
cat > "$ratchet_new_traversal" <<'EOF'
module Alex.Traversal.NewTraversal
open Fidelity.PSG
open Alex.Traversal.TransferTypes
let newTraversalBind (id: NodeId) (ssa: Alex.Dialects.Core.Types.SSA) (acc: MLIRAccumulator) =
  MLIRAccumulator.bindNode id ssa "i64" acc
  MLIRAccumulator.registerSSAType ssa "i64" acc
EOF
cat > "$ratchet_new_patterns" <<'EOF'
module Alex.Patterns.NewPatterns
open Fidelity.PSG
open Alex.Traversal.TransferTypes
let newBind (id: NodeId) (acc: MLIRAccumulator) = MLIRAccumulator.bindNode id (Alex.Traversal.Values.value id 0) "i64" acc
let newVisit (node: SemanticNode) = Alex.Traversal.NanopassArchitecture.visitAllNodes ignore node
let newArgument () = Alex.Dialects.Core.Types.SSA.Arg 0
let newScope () = Alex.Traversal.ScopeContext.ScopeContext.root ()
let newPrologue (id: NodeId) = Alex.Traversal.Values.prologueValue id 0
let newSmt (obligations: string list) = Alex.Traversal.SMTTransfer.transfer obligations
EOF
cat > "$ratchet_literal" <<'EOF'
module Alex.Witnesses.LiteralWitness
open Fidelity.PSG
open Alex.Traversal.TransferTypes
let witnessLiteralNode (id: NodeId) (acc: MLIRAccumulator) =
  acc.SSATypes <- Map.empty
  acc.SSATypes <- Map.empty
  Alex.Traversal.Values.values id
EOF
cat > "$ratchet_match" <<'EOF'
module Alex.Witnesses.MatchWitness
open Fidelity.PSG
open Alex.Traversal.ScopeContext
let visitChild (node: SemanticNode) (obligations: string list) =
  Alex.Traversal.NanopassArchitecture.visitAllNodes ignore node
  Alex.Traversal.SMTTransfer.operations obligations
let witnessBranchScope (parent: ScopeContext) = ScopeContext.createChild parent BlockLevel
EOF
cat > "$ratchet_new_witness" <<'EOF'
module Alex.Witnesses.NewWitness
let newWitness () = let cell = ref 0 in cell.Value
EOF
ratchet_status=0
(cd "$tool_dir" && dotnet fsharp-analyzers --project "$ratchet_proj" --analyzers-path "$tool_dir/bin/Debug/net10.0" --include-analyzers 'Alex published boundary' --fail-on-type-errors) > "$evidence/ratchet.log" 2>&1 || ratchet_status=$?
[[ $ratchet_status -ne 0 ]] || { printf 'Ratchet refusal case was not refused.\n' >&2; exit 1; }
! rg -Fq "$ratchet_types" "$evidence/ratchet.log" || { printf 'Unexpected diagnostic on matched pin Types.fs.\n' >&2; exit 1; }
rg -Fq "$ratchet_corr(1,0): Error AXA003 : AXA003 ratchet mismatch: 'validateOccurrence' in 'Correspondence.fs' pins 1 site(s) but actual count is 0; tighten downward." "$evidence/ratchet.log" || { printf 'Missing AXA003 stale under-count ratchet mismatch diagnostic.\n' >&2; exit 1; }
rg -Fq "$ratchet_corr(4,45): Error AXA003 : Alex must confine Revision.Nodes and Revision.tryNode to Traversal/, XParsec/, or Generation.fs (unpinned 'newUnpinned' in 'Correspondence.fs')." "$evidence/ratchet.log" || { printf 'Missing AXA003 unpinned diagnostic.\n' >&2; exit 1; }
rg -Fq "$ratchet_mem(4,23): Error AXA003 : Alex must confine Revision.Nodes and Revision.tryNode to Traversal/, XParsec/, or Generation.fs ('pArenaCreateIntrinsic' in 'Patterns/MemoryPatterns.fs' has 2 sites, exceeding downward ratchet cap 1)." "$evidence/ratchet.log" || { printf 'Missing AXA003 over-cap diagnostic.\n' >&2; exit 1; }
[[ $(rg -F "$ratchet_corr(1,0): Error AXA003 : AXA003 stale ratchet pin:" "$evidence/ratchet.log" | sort -u | wc -l) -eq 24 ]] || { printf 'Unexpected distinct stale AXA003 ratchet pin count.\n' >&2; exit 1; }
rg -Fq "$ratchet_literal(6,2): Error AXA008 : Alex must not call MLIRAccumulator.bind*, completeVoid, forgetVoid, restoreOperands or registerSSAType, or assign an MLIRAccumulator property, outside Traversal/TransferTypes.fs and Traversal/NanopassArchitecture.fs ('witnessLiteralNode' in 'Witnesses/LiteralWitness.fs' has 2 sites, exceeding downward ratchet cap 1)." "$evidence/ratchet.log" || { printf 'Missing AXA008 over-cap diagnostic.\n' >&2; exit 1; }
[[ $(rg -F "$ratchet_literal" "$evidence/ratchet.log" | wc -l) -eq 1 ]] || { printf 'Unexpected diagnostic on the matched AXA009 pin in LiteralWitness.fs.\n' >&2; exit 1; }
rg -Fq "$ratchet_match(1,0): Error AXA005 : AXA005 ratchet mismatch: 'witnessBranchScope' in 'Witnesses/MatchWitness.fs' pins 1 site(s) but actual count is 0; tighten downward." "$evidence/ratchet.log" || { printf 'Missing AXA005 Witnesses under-count ratchet mismatch diagnostic.\n' >&2; exit 1; }
rg -Fq "$ratchet_match(6,2): Error AXA010 : Alex must not call SMTTransfer.operations or SMTTransfer.transfer in Patterns/ or Witnesses/ (unpinned 'visitChild' in 'Witnesses/MatchWitness.fs')." "$evidence/ratchet.log" || { printf 'Missing AXA010 SMTTransfer.operations diagnostic inside the pinned visitChild function.\n' >&2; exit 1; }
[[ $(rg -F "$ratchet_match" "$evidence/ratchet.log" | wc -l) -eq 2 ]] || { printf 'Unexpected diagnostic on the matched AXA010 pins in MatchWitness.fs.\n' >&2; exit 1; }
rg -Fq "$ratchet_new_patterns(4,50): Error AXA008 : Alex must not call MLIRAccumulator.bind*, completeVoid, forgetVoid, restoreOperands or registerSSAType, or assign an MLIRAccumulator property, outside Traversal/TransferTypes.fs and Traversal/NanopassArchitecture.fs (unpinned 'newBind' in 'Patterns/NewPatterns.fs')." "$evidence/ratchet.log" || { printf 'Missing AXA008 unpinned diagnostic.\n' >&2; exit 1; }
rg -Fq "$ratchet_new_patterns(4,79): Error AXA009 : Alex must take SSA names from getNodeSSA / getNodeSSAs; direct uses of the SSA-producing members of Alex.Traversal.Values are confined to Traversal/Values.fs and XParsec/PSGCombinators.fs (unpinned 'newBind' in 'Patterns/NewPatterns.fs')." "$evidence/ratchet.log" || { printf 'Missing AXA009 unpinned Values.value diagnostic.\n' >&2; exit 1; }
rg -Fq "$ratchet_new_patterns(5,36): Error AXA010 : Alex must not call NanopassArchitecture.visitAllNodes or ScopeContext.root / createChild / addOp / addOps / enterScope / exitScope in Patterns/ or in a Witnesses/ function that is not a pinned scope boundary (unpinned 'newVisit' in 'Patterns/NewPatterns.fs')." "$evidence/ratchet.log" || { printf 'Missing AXA010 unpinned diagnostic.\n' >&2; exit 1; }
rg -Fq "$ratchet_new_patterns(6,21): Error AXA009 : Alex must not construct an SSA union case outside Traversal/Values.fs (unpinned 'newArgument' in 'Patterns/NewPatterns.fs')." "$evidence/ratchet.log" || { printf 'Missing AXA009 unpinned SSA construction diagnostic.\n' >&2; exit 1; }
rg -Fq "$ratchet_new_patterns(7,18): Error AXA010 : Alex must not call NanopassArchitecture.visitAllNodes or ScopeContext.root / createChild / addOp / addOps / enterScope / exitScope in Patterns/ or in a Witnesses/ function that is not a pinned scope boundary (unpinned 'newScope' in 'Patterns/NewPatterns.fs')." "$evidence/ratchet.log" || { printf 'Missing AXA010 unpinned ScopeContext.root diagnostic.\n' >&2; exit 1; }
rg -Fq "$ratchet_new_patterns(8,31): Error AXA009 : Alex must take SSA names from getNodeSSA / getNodeSSAs; direct uses of the SSA-producing members of Alex.Traversal.Values are confined to Traversal/Values.fs and XParsec/PSGCombinators.fs (unpinned 'newPrologue' in 'Patterns/NewPatterns.fs')." "$evidence/ratchet.log" || { printf 'Missing AXA009 unpinned Values.prologueValue diagnostic.\n' >&2; exit 1; }
rg -Fq "$ratchet_new_patterns(9,40): Error AXA010 : Alex must not call SMTTransfer.operations or SMTTransfer.transfer in Patterns/ or Witnesses/ (unpinned 'newSmt' in 'Patterns/NewPatterns.fs')." "$evidence/ratchet.log" || { printf 'Missing AXA010 unpinned SMTTransfer.transfer diagnostic.\n' >&2; exit 1; }
[[ $(rg -F "$ratchet_new_patterns" "$evidence/ratchet.log" | wc -l) -eq 7 ]] || { printf 'Unexpected NewPatterns.fs diagnostic count.\n' >&2; exit 1; }
rg -Fq "$ratchet_new_traversal(5,2): Error AXA008 : Alex must not call MLIRAccumulator.bind*, completeVoid, forgetVoid, restoreOperands or registerSSAType, or assign an MLIRAccumulator property, outside Traversal/TransferTypes.fs and Traversal/NanopassArchitecture.fs (unpinned 'newTraversalBind' in 'Traversal/NewTraversal.fs')." "$evidence/ratchet.log" || { printf 'Missing AXA008 unpinned bindNode diagnostic in Traversal/.\n' >&2; exit 1; }
rg -Fq "$ratchet_new_traversal(6,2): Error AXA008 : Alex must not call MLIRAccumulator.bind*, completeVoid, forgetVoid, restoreOperands or registerSSAType, or assign an MLIRAccumulator property, outside Traversal/TransferTypes.fs and Traversal/NanopassArchitecture.fs (unpinned 'newTraversalBind' in 'Traversal/NewTraversal.fs')." "$evidence/ratchet.log" || { printf 'Missing AXA008 unpinned registerSSAType diagnostic in Traversal/.\n' >&2; exit 1; }
[[ $(rg -F "$ratchet_new_traversal" "$evidence/ratchet.log" | wc -l) -eq 2 ]] || { printf 'Unexpected NewTraversal.fs diagnostic count.\n' >&2; exit 1; }
rg -Fq "$ratchet_new_witness(2,31): Error AXA005 : Mutable locals, mutable bindings and ref cells are forbidden in Witnesses/ (unpinned 'newWitness' in 'Witnesses/NewWitness.fs')." "$evidence/ratchet.log" || { printf 'Missing AXA005 Witnesses unpinned diagnostic.\n' >&2; exit 1; }
[[ $(rg -F "$ratchet_new_witness" "$evidence/ratchet.log" | wc -l) -eq 1 ]] || { printf 'Unexpected NewWitness.fs diagnostic count.\n' >&2; exit 1; }
! rg -Fq "$ratchet_values" "$evidence/ratchet.log" || { printf 'Unexpected diagnostic in the ratchet Traversal/Values.fs acceptance case.\n' >&2; exit 1; }
rg -Fq "$ratchet_transfer(27,15): Error AXA008 : Alex must not add a settable property to MLIRAccumulator; 'RegionBufferAssoc' is outside the 17 settable properties declared at the introduction of AXA008." "$evidence/ratchet.log" || { printf 'Missing AXA008 diagnostic for a settable MLIRAccumulator property outside the closed set.\n' >&2; exit 1; }
[[ $(rg -F "$ratchet_transfer" "$evidence/ratchet.log" | wc -l) -eq 1 ]] || { printf 'Unexpected diagnostic on the 17 permitted properties, the get-only property or the matched pins in TransferTypes.fs.\n' >&2; exit 1; }
sha256sum "$tool_dir/bin/Debug/net10.0/Alex.Analyzers.dll" "$tool_dir/ProjectInputs.fsx" "$tool_dir/check-project.sh" "$tool_dir/tests/ContractFixture/Contract.fs" "$tool_dir/tests/ContractFixture/ContractFixture.fsproj" "$tool_dir/tests/InProject/InProject.fsproj" "$tool_dir/tests/InProject/Ensure.fs" "$source" "$dialects_source" "$elements_source" "$elements_clean_source" "$patterns_source" "$witnesses_source" "$values_source" "$tool_dir/tests/DependencyControls.fsx" "$tool_dir/tests/project-control.sh" "$evidence/analysis.log" "$evidence/dependency.log" "$evidence/clef-refusal.log" "$evidence/ratchet.log" > "$evidence/truth.sha256"
printf 'PASS in-project historical predicate, AXA003-AXA010 layer controls, ratchet controls and the MLIRAccumulator property control; acceptance cases clean\n'
sha256sum "$scoped_project" "$first" "$last" "$scoped/fixture/Host.fs" "$scoped/authored.json" "$scoped/selected.txt" "$scoped/loader.json" "$scoped/loader.tsv" "$scoped/report.sarif" "$scoped/visited.txt" "$scoped/verified.log" "$scoped"/{empty,omitted,reordered,omitted-reference,omitted-project,replaced}.log >> "$evidence/truth.sha256"
