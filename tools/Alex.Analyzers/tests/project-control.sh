#!/usr/bin/env bash
set -euo pipefail
tool_dir=$(cd -P "$(dirname "$0")/.." && pwd)
repo_dir=$(git -C "$tool_dir" rev-parse --show-toplevel)
evidence="$repo_dir/artifacts/alex-analyzers-tests/inproject-control"
mkdir -p "$evidence"
project="$tool_dir/tests/InProject/InProject.fsproj"
check="$tool_dir/check-project.sh"
project_refusal='Alex rules require the Alex production project in this checkout.'
refuses_subject() {
  local report="$evidence/$1.log" reason=$2 status=0
  shift 2
  "$@" > "$report" 2>&1 || status=$?
  [[ $status == 2 ]]
  grep -Fxq "$reason" "$report"
}
for retired in clef clef-provenance; do
  refuses_subject "$retired-mode" 'Expected alex or alex-boundary mode.' bash "$check" "$retired" "$project"
done
refuses_subject alternate-argument "$project_refusal" bash "$check" alex "$project"
refuses_subject alternate-environment "$project_refusal" env ALEX_ANALYZER_PROJECT="$project" bash "$check" alex-boundary
refuses_subject alternate-wrapper "$project_refusal" env ALEX_ANALYZER_PROJECT="$project" bash "$tool_dir/analyze-alex.sh"
source="$tool_dir/tests/InProject/Cases.fs"
dialects_source="$tool_dir/tests/InProject/Dialects/Cases.fs"
elements_source="$tool_dir/tests/InProject/Elements/Cases.fs"
elements_clean_source="$tool_dir/tests/InProject/Elements/CleanCases.fs"
patterns_source="$tool_dir/tests/InProject/Patterns/Cases.fs"
witnesses_source="$tool_dir/tests/InProject/Witnesses/Cases.fs"
values_source="$tool_dir/tests/InProject/Traversal/Values.fs"
ensure_source="$tool_dir/tests/InProject/Ensure.fs"
status=0
(cd "$tool_dir" && dotnet fsharp-analyzers --project "$project" --analyzers-path "$tool_dir/bin/Debug/net10.0" --include-analyzers 'Alex published boundary' --fail-on-type-errors) > "$evidence/analysis.log" 2>&1 || status=$?
[[ $status -ne 0 ]] || { printf 'In-project refusal case was not refused.\n' >&2; exit 1; }
[[ $(grep -E 'Error AX[AC][0-9]+' "$evidence/analysis.log" | wc -l) -eq 48 ]] || { printf 'Unexpected in-project diagnostic count.\n' >&2; exit 1; }
grep -Fq "$source(7,6): Error AXA002 : Alex must not derive an admission predicate from a nominal declaration name." "$evidence/analysis.log" || { printf 'Missing in-project historical diagnostic.\n' >&2; exit 1; }
grep -Fq "$dialects_source(5,52): Error AXA003 : Alex must confine Revision.Nodes and Revision.tryNode to Traversal/, XParsec/, or Generation.fs (in 'badNodesAccess')." "$evidence/analysis.log" || { printf 'Missing in-project AXA003 diagnostic.\n' >&2; exit 1; }
grep -Fq "$dialects_source(7,8): Error AXA004 : Alex must not write recursive SemanticKind or Revision.Nodes catamorphisms outside Traversal/NanopassArchitecture.fs (tryWitnesses) (in 'badSemanticCata')." "$evidence/analysis.log" || { printf 'Missing in-project AXA004 diagnostic.\n' >&2; exit 1; }
grep -Fq "$dialects_source(13,14): Error AXA005 : Mutable local 'count' is forbidden in non-traversal Alex layers." "$evidence/analysis.log" || { printf 'Missing in-project AXA005 mutable diagnostic.\n' >&2; exit 1; }
grep -Fq "$dialects_source(18,13): Error AXA005 : Mutable ref cells (ref) are forbidden in non-traversal Alex layers." "$evidence/analysis.log" || { printf 'Missing in-project AXA005 ref diagnostic.\n' >&2; exit 1; }
grep -Fq "$dialects_source(22,2): Error AXA006 : Alex must not extract payloads from BoundaryImport.DeclarationFacts; only key-presence checks (ContainsKey / Map.containsKey) are permitted." "$evidence/analysis.log" || { printf 'Missing in-project AXA006 diagnostic.\n' >&2; exit 1; }
grep -Fq "$dialects_source(28,37): Error AXA007 : Alex must not collapse None from a published-fact or symbol lookup into a fallback value (in 'badFallbackDefault')." "$evidence/analysis.log" || { printf 'Missing in-project AXA007 diagnostic.\n' >&2; exit 1; }
grep -Fq "$dialects_source(38,28): Error AXA009 : Alex must not construct an SSA union case outside Traversal/Values.fs (in 'badSsaConstruction')." "$evidence/analysis.log" || { printf 'Missing in-project AXA009 SSA construction diagnostic.\n' >&2; exit 1; }
grep -Fq "$dialects_source(41,2): Error AXA009 : Alex must take SSA names from getNodeSSA / getNodeSSAs; direct uses of the SSA-producing members of Alex.Traversal.Values are confined to Traversal/Values.fs and XParsec/PSGCombinators.fs (in 'badValuesDirect')." "$evidence/analysis.log" || { printf 'Missing in-project AXA009 Values.value diagnostic.\n' >&2; exit 1; }
grep -Fq "$dialects_source(41,36): Error AXA009 : Alex must take SSA names from getNodeSSA / getNodeSSAs; direct uses of the SSA-producing members of Alex.Traversal.Values are confined to Traversal/Values.fs and XParsec/PSGCombinators.fs (in 'badValuesDirect')." "$evidence/analysis.log" || { printf 'Missing in-project AXA009 Values.continuationValue diagnostic.\n' >&2; exit 1; }
grep -Fq "$elements_source(12,79): Error AXA008 : Alex must not call MLIRAccumulator.bind*, completeVoid, forgetVoid, restoreOperands or registerSSAType, or assign an MLIRAccumulator property, outside Traversal/TransferTypes.fs and Traversal/NanopassArchitecture.fs (in 'badAccumulatorAssign')." "$evidence/analysis.log" || { printf 'Missing in-project Elements AXA008 property assignment diagnostic.\n' >&2; exit 1; }
grep -Fq "$patterns_source(7,2): Error AXA008 : Alex must not call MLIRAccumulator.bind*, completeVoid, forgetVoid, restoreOperands or registerSSAType, or assign an MLIRAccumulator property, outside Traversal/TransferTypes.fs and Traversal/NanopassArchitecture.fs (in 'badBindNode')." "$evidence/analysis.log" || { printf 'Missing in-project Patterns AXA008 bindNode diagnostic.\n' >&2; exit 1; }
grep -Fq "$patterns_source(10,2): Error AXA008 : Alex must not call MLIRAccumulator.bind*, completeVoid, forgetVoid, restoreOperands or registerSSAType, or assign an MLIRAccumulator property, outside Traversal/TransferTypes.fs and Traversal/NanopassArchitecture.fs (in 'badAccumulatorAssign')." "$evidence/analysis.log" || { printf 'Missing in-project Patterns AXA008 property assignment diagnostic.\n' >&2; exit 1; }
grep -Fq "$patterns_source(13,2): Error AXA010 : Alex must not call NanopassArchitecture.visitAllNodes or ScopeContext.root / createChild / addOp / addOps / enterScope / exitScope in Patterns/ or in a Witnesses/ function that is not a pinned scope boundary (in 'badVisitAll')." "$evidence/analysis.log" || { printf 'Missing in-project Patterns AXA010 visitAllNodes diagnostic.\n' >&2; exit 1; }
grep -Fq "$patterns_source(16,2): Error AXA010 : Alex must not call NanopassArchitecture.visitAllNodes or ScopeContext.root / createChild / addOp / addOps / enterScope / exitScope in Patterns/ or in a Witnesses/ function that is not a pinned scope boundary (in 'badScopeTransition')." "$evidence/analysis.log" || { printf 'Missing in-project Patterns AXA010 exitScope diagnostic.\n' >&2; exit 1; }
grep -Fq "$patterns_source(16,41): Error AXA010 : Alex must not call NanopassArchitecture.visitAllNodes or ScopeContext.root / createChild / addOp / addOps / enterScope / exitScope in Patterns/ or in a Witnesses/ function that is not a pinned scope boundary (in 'badScopeTransition')." "$evidence/analysis.log" || { printf 'Missing in-project Patterns AXA010 enterScope diagnostic.\n' >&2; exit 1; }
grep -Fq "$patterns_source(19,2): Error AXA010 : Alex must not call SMTTransfer.operations or SMTTransfer.transfer in Patterns/ or Witnesses/ (in 'badSmtTransfer')." "$evidence/analysis.log" || { printf 'Missing in-project Patterns AXA010 SMTTransfer.operations diagnostic.\n' >&2; exit 1; }
grep -Fq "$patterns_source(19,53): Error AXA010 : Alex must not call SMTTransfer.operations or SMTTransfer.transfer in Patterns/ or Witnesses/ (in 'badSmtTransfer')." "$evidence/analysis.log" || { printf 'Missing in-project Patterns AXA010 SMTTransfer.transfer diagnostic.\n' >&2; exit 1; }
grep -Fq "$witnesses_source(7,14): Error AXA005 : Mutable locals, mutable bindings and ref cells are forbidden in Witnesses/ (in 'badMutableLocal')." "$evidence/analysis.log" || { printf 'Missing in-project Witnesses AXA005 mutable local diagnostic.\n' >&2; exit 1; }
grep -Fq "$witnesses_source(12,13): Error AXA005 : Mutable locals, mutable bindings and ref cells are forbidden in Witnesses/ (in 'badRefCell')." "$evidence/analysis.log" || { printf 'Missing in-project Witnesses AXA005 ref cell diagnostic.\n' >&2; exit 1; }
grep -Fq "$witnesses_source(16,2): Error AXA008 : Alex must not call MLIRAccumulator.bind*, completeVoid, forgetVoid, restoreOperands or registerSSAType, or assign an MLIRAccumulator property, outside Traversal/TransferTypes.fs and Traversal/NanopassArchitecture.fs (in 'badBindNode')." "$evidence/analysis.log" || { printf 'Missing in-project Witnesses AXA008 bindNode diagnostic.\n' >&2; exit 1; }
grep -Fq "$witnesses_source(19,2): Error AXA010 : Alex must not call NanopassArchitecture.visitAllNodes or ScopeContext.root / createChild / addOp / addOps / enterScope / exitScope in Patterns/ or in a Witnesses/ function that is not a pinned scope boundary (in 'badVisitAll')." "$evidence/analysis.log" || { printf 'Missing in-project Witnesses AXA010 visitAllNodes diagnostic.\n' >&2; exit 1; }
grep -Fq "$dialects_source(47,2): Error AXA008 : Alex must not call MLIRAccumulator.bind*, completeVoid, forgetVoid, restoreOperands or registerSSAType, or assign an MLIRAccumulator property, outside Traversal/TransferTypes.fs and Traversal/NanopassArchitecture.fs (in 'badRegisterType')." "$evidence/analysis.log" || { printf 'Missing in-project Dialects AXA008 registerSSAType diagnostic.\n' >&2; exit 1; }
grep -Fq "$dialects_source(50,2): Error AXA009 : Alex must take SSA names from getNodeSSA / getNodeSSAs; direct uses of the SSA-producing members of Alex.Traversal.Values are confined to Traversal/Values.fs and XParsec/PSGCombinators.fs (in 'badValuesMembers')." "$evidence/analysis.log" || { printf 'Missing in-project AXA009 Values.resultOf diagnostic.\n' >&2; exit 1; }
grep -Fq "$dialects_source(50,37): Error AXA009 : Alex must take SSA names from getNodeSSA / getNodeSSAs; direct uses of the SSA-producing members of Alex.Traversal.Values are confined to Traversal/Values.fs and XParsec/PSGCombinators.fs (in 'badValuesMembers')." "$evidence/analysis.log" || { printf 'Missing in-project AXA009 Values.undefined diagnostic.\n' >&2; exit 1; }
grep -Fq "$patterns_source(30,2): Error AXA008 : Alex must not call MLIRAccumulator.bind*, completeVoid, forgetVoid, restoreOperands or registerSSAType, or assign an MLIRAccumulator property, outside Traversal/TransferTypes.fs and Traversal/NanopassArchitecture.fs (in 'badForgetVoid')." "$evidence/analysis.log" || { printf 'Missing in-project Patterns AXA008 forgetVoid diagnostic.\n' >&2; exit 1; }
grep -Fq "$patterns_source(33,2): Error AXA010 : Alex must not call NanopassArchitecture.visitAllNodes or ScopeContext.root / createChild / addOp / addOps / enterScope / exitScope in Patterns/ or in a Witnesses/ function that is not a pinned scope boundary (in 'badScopeContext')." "$evidence/analysis.log" || { printf 'Missing in-project Patterns AXA010 ScopeContext.addOps diagnostic.\n' >&2; exit 1; }
grep -Fq "$patterns_source(33,55): Error AXA010 : Alex must not call NanopassArchitecture.visitAllNodes or ScopeContext.root / createChild / addOp / addOps / enterScope / exitScope in Patterns/ or in a Witnesses/ function that is not a pinned scope boundary (in 'badScopeContext')." "$evidence/analysis.log" || { printf 'Missing in-project Patterns AXA010 ScopeContext.root diagnostic.\n' >&2; exit 1; }
grep -Fq "$witnesses_source(26,2): Error AXA010 : Alex must not call SMTTransfer.operations or SMTTransfer.transfer in Patterns/ or Witnesses/ (in 'badSmtTransfer')." "$evidence/analysis.log" || { printf 'Missing in-project Witnesses AXA010 SMTTransfer.operations diagnostic.\n' >&2; exit 1; }
! grep -Fq "$values_source" "$evidence/analysis.log" || { printf 'Unexpected diagnostic in the Traversal/Values.fs acceptance case.\n' >&2; exit 1; }
! grep -Fq "$ensure_source" "$evidence/analysis.log" || { printf 'Unexpected diagnostic in the in-project stub file.\n' >&2; exit 1; }
[[ $(grep -F "$dialects_source" "$evidence/analysis.log" | wc -l) -eq 12 ]] || { printf 'Unexpected Dialects diagnostic count.\n' >&2; exit 1; }
[[ $(grep -F "$patterns_source" "$evidence/analysis.log" | wc -l) -eq 10 ]] || { printf 'Unexpected Patterns diagnostic count.\n' >&2; exit 1; }
[[ $(grep -F "$witnesses_source" "$evidence/analysis.log" | wc -l) -eq 5 ]] || { printf 'Unexpected Witnesses diagnostic count.\n' >&2; exit 1; }
! grep -Fq "$elements_clean_source" "$evidence/analysis.log" || { printf 'Unexpected diagnostic in allowed Elements fixture.\n' >&2; exit 1; }
[[ $(grep -F "$elements_source" "$evidence/analysis.log" | wc -l) -eq 20 ]] || { printf 'Unexpected Elements refusal case diagnostic count.\n' >&2; exit 1; }
env -u DEPENDENCY_CONTROL_ONLY dotnet fsi "$tool_dir/tests/DependencyControls.fsx" > "$evidence/dependency.log" 2>&1
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
! grep -Fq "$ratchet_types" "$evidence/ratchet.log" || { printf 'Unexpected diagnostic on matched pin Types.fs.\n' >&2; exit 1; }
grep -Fq "$ratchet_corr(1,0): Error AXA003 : AXA003 ratchet mismatch: 'validateOccurrence' in 'Correspondence.fs' pins 1 site(s) but actual count is 0; tighten downward." "$evidence/ratchet.log" || { printf 'Missing AXA003 stale under-count ratchet mismatch diagnostic.\n' >&2; exit 1; }
grep -Fq "$ratchet_corr(4,45): Error AXA003 : Alex must confine Revision.Nodes and Revision.tryNode to Traversal/, XParsec/, or Generation.fs (unpinned 'newUnpinned' in 'Correspondence.fs')." "$evidence/ratchet.log" || { printf 'Missing AXA003 unpinned diagnostic.\n' >&2; exit 1; }
grep -Fq "$ratchet_mem(4,23): Error AXA003 : Alex must confine Revision.Nodes and Revision.tryNode to Traversal/, XParsec/, or Generation.fs ('pArenaCreateIntrinsic' in 'Patterns/MemoryPatterns.fs' has 2 sites, exceeding downward ratchet cap 1)." "$evidence/ratchet.log" || { printf 'Missing AXA003 over-cap diagnostic.\n' >&2; exit 1; }
[[ $(grep -F "$ratchet_corr(1,0): Error AXA003 : AXA003 stale ratchet pin:" "$evidence/ratchet.log" | sort -u | wc -l) -eq 24 ]] || { printf 'Unexpected distinct stale AXA003 ratchet pin count.\n' >&2; exit 1; }
grep -Fq "$ratchet_literal(6,2): Error AXA008 : Alex must not call MLIRAccumulator.bind*, completeVoid, forgetVoid, restoreOperands or registerSSAType, or assign an MLIRAccumulator property, outside Traversal/TransferTypes.fs and Traversal/NanopassArchitecture.fs ('witnessLiteralNode' in 'Witnesses/LiteralWitness.fs' has 2 sites, exceeding downward ratchet cap 1)." "$evidence/ratchet.log" || { printf 'Missing AXA008 over-cap diagnostic.\n' >&2; exit 1; }
[[ $(grep -F "$ratchet_literal" "$evidence/ratchet.log" | wc -l) -eq 1 ]] || { printf 'Unexpected diagnostic on the matched AXA009 pin in LiteralWitness.fs.\n' >&2; exit 1; }
grep -Fq "$ratchet_match(1,0): Error AXA005 : AXA005 ratchet mismatch: 'witnessBranchScope' in 'Witnesses/MatchWitness.fs' pins 1 site(s) but actual count is 0; tighten downward." "$evidence/ratchet.log" || { printf 'Missing AXA005 Witnesses under-count ratchet mismatch diagnostic.\n' >&2; exit 1; }
grep -Fq "$ratchet_match(6,2): Error AXA010 : Alex must not call SMTTransfer.operations or SMTTransfer.transfer in Patterns/ or Witnesses/ (unpinned 'visitChild' in 'Witnesses/MatchWitness.fs')." "$evidence/ratchet.log" || { printf 'Missing AXA010 SMTTransfer.operations diagnostic inside the pinned visitChild function.\n' >&2; exit 1; }
[[ $(grep -F "$ratchet_match" "$evidence/ratchet.log" | wc -l) -eq 2 ]] || { printf 'Unexpected diagnostic on the matched AXA010 pins in MatchWitness.fs.\n' >&2; exit 1; }
grep -Fq "$ratchet_new_patterns(4,50): Error AXA008 : Alex must not call MLIRAccumulator.bind*, completeVoid, forgetVoid, restoreOperands or registerSSAType, or assign an MLIRAccumulator property, outside Traversal/TransferTypes.fs and Traversal/NanopassArchitecture.fs (unpinned 'newBind' in 'Patterns/NewPatterns.fs')." "$evidence/ratchet.log" || { printf 'Missing AXA008 unpinned diagnostic.\n' >&2; exit 1; }
grep -Fq "$ratchet_new_patterns(4,79): Error AXA009 : Alex must take SSA names from getNodeSSA / getNodeSSAs; direct uses of the SSA-producing members of Alex.Traversal.Values are confined to Traversal/Values.fs and XParsec/PSGCombinators.fs (unpinned 'newBind' in 'Patterns/NewPatterns.fs')." "$evidence/ratchet.log" || { printf 'Missing AXA009 unpinned Values.value diagnostic.\n' >&2; exit 1; }
grep -Fq "$ratchet_new_patterns(5,36): Error AXA010 : Alex must not call NanopassArchitecture.visitAllNodes or ScopeContext.root / createChild / addOp / addOps / enterScope / exitScope in Patterns/ or in a Witnesses/ function that is not a pinned scope boundary (unpinned 'newVisit' in 'Patterns/NewPatterns.fs')." "$evidence/ratchet.log" || { printf 'Missing AXA010 unpinned diagnostic.\n' >&2; exit 1; }
grep -Fq "$ratchet_new_patterns(6,21): Error AXA009 : Alex must not construct an SSA union case outside Traversal/Values.fs (unpinned 'newArgument' in 'Patterns/NewPatterns.fs')." "$evidence/ratchet.log" || { printf 'Missing AXA009 unpinned SSA construction diagnostic.\n' >&2; exit 1; }
grep -Fq "$ratchet_new_patterns(7,18): Error AXA010 : Alex must not call NanopassArchitecture.visitAllNodes or ScopeContext.root / createChild / addOp / addOps / enterScope / exitScope in Patterns/ or in a Witnesses/ function that is not a pinned scope boundary (unpinned 'newScope' in 'Patterns/NewPatterns.fs')." "$evidence/ratchet.log" || { printf 'Missing AXA010 unpinned ScopeContext.root diagnostic.\n' >&2; exit 1; }
grep -Fq "$ratchet_new_patterns(8,31): Error AXA009 : Alex must take SSA names from getNodeSSA / getNodeSSAs; direct uses of the SSA-producing members of Alex.Traversal.Values are confined to Traversal/Values.fs and XParsec/PSGCombinators.fs (unpinned 'newPrologue' in 'Patterns/NewPatterns.fs')." "$evidence/ratchet.log" || { printf 'Missing AXA009 unpinned Values.prologueValue diagnostic.\n' >&2; exit 1; }
grep -Fq "$ratchet_new_patterns(9,40): Error AXA010 : Alex must not call SMTTransfer.operations or SMTTransfer.transfer in Patterns/ or Witnesses/ (unpinned 'newSmt' in 'Patterns/NewPatterns.fs')." "$evidence/ratchet.log" || { printf 'Missing AXA010 unpinned SMTTransfer.transfer diagnostic.\n' >&2; exit 1; }
[[ $(grep -F "$ratchet_new_patterns" "$evidence/ratchet.log" | wc -l) -eq 7 ]] || { printf 'Unexpected NewPatterns.fs diagnostic count.\n' >&2; exit 1; }
grep -Fq "$ratchet_new_traversal(5,2): Error AXA008 : Alex must not call MLIRAccumulator.bind*, completeVoid, forgetVoid, restoreOperands or registerSSAType, or assign an MLIRAccumulator property, outside Traversal/TransferTypes.fs and Traversal/NanopassArchitecture.fs (unpinned 'newTraversalBind' in 'Traversal/NewTraversal.fs')." "$evidence/ratchet.log" || { printf 'Missing AXA008 unpinned bindNode diagnostic in Traversal/.\n' >&2; exit 1; }
grep -Fq "$ratchet_new_traversal(6,2): Error AXA008 : Alex must not call MLIRAccumulator.bind*, completeVoid, forgetVoid, restoreOperands or registerSSAType, or assign an MLIRAccumulator property, outside Traversal/TransferTypes.fs and Traversal/NanopassArchitecture.fs (unpinned 'newTraversalBind' in 'Traversal/NewTraversal.fs')." "$evidence/ratchet.log" || { printf 'Missing AXA008 unpinned registerSSAType diagnostic in Traversal/.\n' >&2; exit 1; }
[[ $(grep -F "$ratchet_new_traversal" "$evidence/ratchet.log" | wc -l) -eq 2 ]] || { printf 'Unexpected NewTraversal.fs diagnostic count.\n' >&2; exit 1; }
grep -Fq "$ratchet_new_witness(2,31): Error AXA005 : Mutable locals, mutable bindings and ref cells are forbidden in Witnesses/ (unpinned 'newWitness' in 'Witnesses/NewWitness.fs')." "$evidence/ratchet.log" || { printf 'Missing AXA005 Witnesses unpinned diagnostic.\n' >&2; exit 1; }
[[ $(grep -F "$ratchet_new_witness" "$evidence/ratchet.log" | wc -l) -eq 1 ]] || { printf 'Unexpected NewWitness.fs diagnostic count.\n' >&2; exit 1; }
! grep -Fq "$ratchet_values" "$evidence/ratchet.log" || { printf 'Unexpected diagnostic in the ratchet Traversal/Values.fs acceptance case.\n' >&2; exit 1; }
grep -Fq "$ratchet_transfer(27,15): Error AXA008 : Alex must not add a settable property to MLIRAccumulator; 'RegionBufferAssoc' is outside the 17 settable properties declared at the introduction of AXA008." "$evidence/ratchet.log" || { printf 'Missing AXA008 diagnostic for a settable MLIRAccumulator property outside the closed set.\n' >&2; exit 1; }
[[ $(grep -F "$ratchet_transfer" "$evidence/ratchet.log" | wc -l) -eq 1 ]] || { printf 'Unexpected diagnostic on the 17 permitted properties, the get-only property or the matched pins in TransferTypes.fs.\n' >&2; exit 1; }
axc011_dir="$evidence/axc011-ratchet"
rm -rf "$axc011_dir"
mkdir -p "$axc011_dir/src/Alex/Traversal/obj" "$axc011_dir/src/Shared"
axc011_proj="$axc011_dir/src/Alex/Alex.fsproj"
axc011_smt="$axc011_dir/src/Alex/Traversal/SMTTransfer.fs"
axc011_new="$axc011_dir/src/Alex/Traversal/NewMutable.fs"
axc011_obj="$axc011_dir/src/Alex/Traversal/obj/AuthoredObjDebt.fs"
axc011_linked="$axc011_dir/src/Shared/LinkedDebt.fs"
axc011_clean="$axc011_dir/src/Alex/Traversal/CleanPure.fs"
cat > "$axc011_proj" <<'EOF'
<Project Sdk="Microsoft.NET.Sdk">
  <PropertyGroup>
    <TargetFramework>net10.0</TargetFramework>
    <OutputType>Library</OutputType>
    <ManagePackageVersionsCentrally>false</ManagePackageVersionsCentrally>
  </PropertyGroup>
  <ItemGroup>
    <Compile Include="Traversal/SMTTransfer.fs" />
    <Compile Include="Traversal/NewMutable.fs" />
    <Compile Include="Traversal/obj/AuthoredObjDebt.fs" />
    <Compile Include="../Shared/LinkedDebt.fs" />
    <Compile Include="Traversal/CleanPure.fs" />
  </ItemGroup>
</Project>
EOF
cat > "$axc011_smt" <<'EOF'
module Alex.Traversal.SMTTransfer
let empty () = System.Collections.Generic.Dictionary<string, int>()
EOF
cat > "$axc011_new" <<'EOF'
module Alex.Traversal.NewMutable
let bump () = let mutable total = 0 in total <- total + 1; total
EOF
cat > "$axc011_obj" <<'EOF'
module Alex.Traversal.ObjSubdirDebt
let authoredObj () = let mutable n = 0 in n <- n + 1; n
EOF
cat > "$axc011_linked" <<'EOF'
module Alex.Shared.LinkedDebt
let linked () = let mutable count = 0 in count <- count + 1; count
EOF
cat > "$axc011_clean" <<'EOF'
module Alex.Traversal.CleanPure
let sum (xs: int list) = List.sum xs
EOF
axc011_status=0
(cd "$tool_dir" && dotnet fsharp-analyzers --project "$axc011_proj" --analyzers-path "$tool_dir/bin/Debug/net10.0" --include-analyzers 'Alex pure-core baseline' 'Alex dependency context' --include-files "$axc011_smt" "$axc011_new" "$axc011_obj" "$axc011_linked" "$axc011_clean" --fail-on-type-errors --report "$evidence/axc011-ratchet.sarif") > "$evidence/axc011-ratchet.log" 2>&1 || axc011_status=$?
[[ $axc011_status -ne 0 ]] || { printf 'Project-mode AXC011 ratchet control was not refused.\n' >&2; exit 1; }
grep -Fq "$axc011_smt(1,0): Error AXC011 : Alex must shrink the legacy mutable ratchet: let mutable in 'Traversal/SMTTransfer.fs' pins 24 site(s) but actual count is 0; tighten downward." "$evidence/axc011-ratchet.log" || { printf 'Missing project-mode AXC011 zero-site shrink diagnostic for Traversal/SMTTransfer.fs.\n' >&2; exit 1; }
grep -Fq "$axc011_smt(2,15): Error AXC011 : Alex must not introduce legacy mutable state: System.Collections.Generic.Dictionary\`2 in 'Traversal/SMTTransfer.fs' is not a pinned ratchet target." "$evidence/axc011-ratchet.log" || { printf 'Missing project-mode AXC011 unpinned target diagnostic for Traversal/SMTTransfer.fs.\n' >&2; exit 1; }
grep -Fq "$axc011_new(2,14): Error AXC011 : Alex must not introduce legacy mutable state: let mutable in 'Traversal/NewMutable.fs' is outside the checked-in ratchet." "$evidence/axc011-ratchet.log" || { printf 'Missing project-mode AXC011 unpinned file diagnostic for Traversal/NewMutable.fs.\n' >&2; exit 1; }
grep -Fq "$axc011_obj(2,21): Error AXC011 : Alex must not introduce legacy mutable state: let mutable in 'Traversal/obj/AuthoredObjDebt.fs' is outside the checked-in ratchet." "$evidence/axc011-ratchet.log" || { printf 'Missing project-mode AXC011 authored obj-subdir diagnostic.\n' >&2; exit 1; }
grep -Fq "$axc011_linked(2,16): Error AXC011 : Alex must not introduce legacy mutable state: let mutable in '../Shared/LinkedDebt.fs' is outside the checked-in ratchet." "$evidence/axc011-ratchet.log" || { printf 'Missing project-mode AXC011 linked-source diagnostic for ../Shared/LinkedDebt.fs.\n' >&2; exit 1; }
! (grep -F "$axc011_clean" "$evidence/axc011-ratchet.log" | grep -Eq '(Error|Warning) AX') || { printf 'Unexpected diagnostic on clean project-mode AXC011 acceptance file.\n' >&2; exit 1; }
[[ $(grep -Ec 'Error AX[AC][0-9]+' "$evidence/axc011-ratchet.log" || true) -eq 6 ]] || { printf 'Unexpected project-mode AXC011 diagnostic count.\n' >&2; exit 1; }
axc011_growth_dir="$evidence/axc011-growth"
rm -rf "$axc011_growth_dir"
mkdir -p "$axc011_growth_dir/src/Alex/Traversal"
axc011_growth_proj="$axc011_growth_dir/src/Alex/Alex.fsproj"
axc011_growth_smt="$axc011_growth_dir/src/Alex/Traversal/SMTTransfer.fs"
cat > "$axc011_growth_proj" <<'EOF'
<Project Sdk="Microsoft.NET.Sdk">
  <PropertyGroup>
    <TargetFramework>net10.0</TargetFramework>
    <OutputType>Library</OutputType>
    <ManagePackageVersionsCentrally>false</ManagePackageVersionsCentrally>
  </PropertyGroup>
  <ItemGroup>
    <Compile Include="Traversal/SMTTransfer.fs" />
  </ItemGroup>
</Project>
EOF
{
  printf 'module Alex.Traversal.SMTTransfer\nlet grow () =\n'
  for i in $(seq 1 25); do
    printf '  let mutable v%d = %d\n' "$i" "$i"
  done
  printf '  v1 + v25\n'
} > "$axc011_growth_smt"
axc011_growth_status=0
(cd "$tool_dir" && dotnet fsharp-analyzers --project "$axc011_growth_proj" --analyzers-path "$tool_dir/bin/Debug/net10.0" --include-analyzers 'Alex pure-core baseline' --include-files "$axc011_growth_smt" --fail-on-type-errors) > "$evidence/axc011-growth.log" 2>&1 || axc011_growth_status=$?
[[ $axc011_growth_status -ne 0 ]] || { printf 'Project-mode AXC011 growth control was not refused.\n' >&2; exit 1; }
grep -Fq "$axc011_growth_smt(27,2): Error AXC011 : Alex must not grow the legacy mutable ratchet: let mutable in 'Traversal/SMTTransfer.fs' has 25 sites, exceeding the checked-in cap 24." "$evidence/axc011-growth.log" || { printf 'Missing project-mode AXC011 growth diagnostic for Traversal/SMTTransfer.fs.\n' >&2; exit 1; }
[[ $(grep -Ec 'Error AX[AC][0-9]+' "$evidence/axc011-growth.log" || true) -eq 1 ]] || { printf 'Unexpected project-mode AXC011 growth diagnostic count.\n' >&2; exit 1; }
axc011_stale_dir="$evidence/axc011-stale-pin"
rm -rf "$axc011_stale_dir"
mkdir -p "$axc011_stale_dir/src/Alex"
axc011_stale_proj="$axc011_stale_dir/src/Alex/Alex.fsproj"
axc011_stale_text="$axc011_stale_dir/src/Alex/Text.fs"
cat > "$axc011_stale_proj" <<'EOF'
<Project Sdk="Microsoft.NET.Sdk">
  <PropertyGroup>
    <TargetFramework>net10.0</TargetFramework>
    <OutputType>Library</OutputType>
    <ManagePackageVersionsCentrally>false</ManagePackageVersionsCentrally>
  </PropertyGroup>
  <ItemGroup>
    <Compile Include="Text.fs" />
  </ItemGroup>
</Project>
EOF
cat > "$axc011_stale_text" <<'EOF'
module Alex.Text
let greeting = "ok"
EOF
axc011_stale_status=0
(cd "$tool_dir" && dotnet fsharp-analyzers --project "$axc011_stale_proj" --analyzers-path "$tool_dir/bin/Debug/net10.0" --include-analyzers 'Alex pure-core baseline' --include-files "$axc011_stale_text" --fail-on-type-errors) > "$evidence/axc011-stale-pin.log" 2>&1 || axc011_stale_status=$?
[[ $axc011_stale_status -ne 0 ]] || { printf 'Project-mode AXC011 stale-pin control was not refused.\n' >&2; exit 1; }
grep -Fq "$axc011_stale_text(1,0): Error AXC011 : Alex must not keep an AXC011 ratchet entry for 'Traversal/SMTTransfer.fs'; the file is no longer compiled." "$evidence/axc011-stale-pin.log" || { printf 'Missing project-mode AXC011 stale-pin diagnostic.\n' >&2; exit 1; }
[[ $(grep -Ec 'Error AX[AC][0-9]+' "$evidence/axc011-stale-pin.log" || true) -eq 1 ]] || { printf 'Unexpected project-mode AXC011 stale-pin diagnostic count.\n' >&2; exit 1; }
axc010_dir="$evidence/axc010-refusal"
rm -rf "$axc010_dir"
mkdir -p "$axc010_dir"
axc010_proj="$axc010_dir/Axc010Refusal.fsproj"
axc010_next="$axc010_dir/NextRunId.fs"
axc010_clean="$axc010_dir/CleanLocalRef.fs"
cat > "$axc010_proj" <<'EOF'
<Project Sdk="Microsoft.NET.Sdk">
  <PropertyGroup>
    <TargetFramework>net10.0</TargetFramework>
    <OutputType>Library</OutputType>
    <ManagePackageVersionsCentrally>false</ManagePackageVersionsCentrally>
  </PropertyGroup>
  <ItemGroup>
    <Compile Include="NextRunId.fs" />
    <Compile Include="CleanLocalRef.fs" />
  </ItemGroup>
</Project>
EOF
cat > "$axc010_next" <<'EOF'
module Alex.NextRunId
let private nextRunId = ref 0L
EOF
cat > "$axc010_clean" <<'EOF'
module Alex.CleanLocalRef
let accumulator (keys: int list) =
  let total = ref 0
  for _ in keys do total.Value <- total.Value + 1
  total.Value
EOF
axc010_status=0
(cd "$tool_dir" && dotnet fsharp-analyzers --project "$axc010_proj" --analyzers-path "$tool_dir/bin/Debug/net10.0" --include-analyzers 'Alex pure-core baseline' 'Alex dependency context' --include-files "$axc010_next" "$axc010_clean" --fail-on-type-errors --report "$evidence/axc010-refusal.sarif") > "$evidence/axc010-refusal.log" 2>&1 || axc010_status=$?
[[ $axc010_status -ne 0 ]] || { printf 'Project-mode AXC010 refusal control was not refused.\n' >&2; exit 1; }
grep -Fq "$axc010_next(2,12): Error AXC010 : Alex production code must not hold module-level mutable state or ref cells: Microsoft.FSharp.Core.FSharpRef\`1 (binding 'nextRunId')." "$evidence/axc010-refusal.log" || { printf 'Missing project-mode AXC010 refusal diagnostic for nextRunId.\n' >&2; exit 1; }
! (grep -F "$axc010_clean" "$evidence/axc010-refusal.log" | grep -Eq '(Error|Warning) AX') || { printf 'Unexpected diagnostic on clean project-mode AXC010 local-ref file.\n' >&2; exit 1; }
[[ $(grep -Ec 'Error AX[AC][0-9]+' "$evidence/axc010-refusal.log" || true) -eq 1 ]] || { printf 'Unexpected project-mode AXC010 diagnostic count.\n' >&2; exit 1; }
axc009_dir="$evidence/axc009-refusal"
rm -rf "$axc009_dir"
mkdir -p "$axc009_dir"
axc009_proj="$axc009_dir/Axc009Refusal.fsproj"
axc009_refl="$axc009_dir/ReflectionRefusal.fs"
axc009_clean="$axc009_dir/CleanPure.fs"
cat > "$axc009_proj" <<'EOF'
<Project Sdk="Microsoft.NET.Sdk">
  <PropertyGroup>
    <TargetFramework>net10.0</TargetFramework>
    <OutputType>Library</OutputType>
    <ManagePackageVersionsCentrally>false</ManagePackageVersionsCentrally>
  </PropertyGroup>
  <ItemGroup>
    <Compile Include="ReflectionRefusal.fs" />
    <Compile Include="CleanPure.fs" />
  </ItemGroup>
</Project>
EOF
cat > "$axc009_refl" <<'EOF'
module Alex.ReflectionRefusal
open Microsoft.FSharp.Quotations
type PropAlias = System.Reflection.PropertyInfo
let keepProp (p: PropAlias) = p
let isUnion () = Microsoft.FSharp.Reflection.FSharpType.IsUnion(typeof<int option>)
let inspect expr = match expr with Patterns.Call(_, m, _) -> Some m | _ -> None
EOF
cat > "$axc009_clean" <<'EOF'
module Alex.CleanPure
let add (a: int) (b: int) = a + b
EOF
axc009_status=0
(cd "$tool_dir" && dotnet fsharp-analyzers --project "$axc009_proj" --analyzers-path "$tool_dir/bin/Debug/net10.0" --include-analyzers 'Alex pure-core baseline' 'Alex dependency context' --include-files "$axc009_refl" "$axc009_clean" --fail-on-type-errors --report "$evidence/axc009-refusal.sarif") > "$evidence/axc009-refusal.log" 2>&1 || axc009_status=$?
[[ $axc009_status -ne 0 ]] || { printf 'Project-mode AXC009 refusal control was not refused.\n' >&2; exit 1; }
grep -Fq "$axc009_refl(4,17): Error AXC009 : Alex production code must not use reflection APIs: System.Reflection.PropertyInfo" "$evidence/axc009-refusal.log" || { printf 'Missing project-mode AXC009 PropertyInfo alias diagnostic.\n' >&2; exit 1; }
grep -Fq "$axc009_refl(5,45): Error AXC009 : Alex production code must not use reflection APIs: Microsoft.FSharp.Reflection.FSharpType (assembly FSharp.Core)." "$evidence/axc009-refusal.log" || { printf 'Missing project-mode AXC009 FSharpType diagnostic.\n' >&2; exit 1; }
grep -Fq "$axc009_refl(6,35): Error AXC009 : Alex production code must not use reflection APIs: System.Reflection.MethodInfo" "$evidence/axc009-refusal.log" || { printf 'Missing project-mode AXC009 inferred MethodInfo diagnostic.\n' >&2; exit 1; }
! (grep -F "$axc009_clean" "$evidence/axc009-refusal.log" | grep -Eq '(Error|Warning) AX') || { printf 'Unexpected diagnostic on clean project-mode AXC009 file.\n' >&2; exit 1; }
cat > "$evidence/verify-refusal-sarif.fsx" <<'FSI'
open System
open System.IO
open System.Security.Cryptography
open System.Text.Json.Nodes

let sha256Hex (path: string) =
  use stream = File.OpenRead(path)
  SHA256.HashData(stream) |> Convert.ToHexString

let normalizeUri (uri: string) =
  let stripped =
    if uri.StartsWith("file://", StringComparison.OrdinalIgnoreCase) then Uri(uri).LocalPath
    else uri
  Path.GetFullPath(stripped)

let verifySarif (label: string) (sarifPath: string) (files: string list) (expectedRules: (string * string * string * int) list) =
  if not (File.Exists sarifPath) then failwithf "%s: missing SARIF %s" label sarifPath
  let doc = JsonNode.Parse(File.ReadAllText sarifPath)
  let results =
    doc.["runs"].AsArray()
    |> Seq.collect (fun run -> run.["results"].AsArray())
    |> Seq.toList
  let axdRecords =
    results
    |> List.choose (fun row ->
      if row.["ruleId"].GetValue<string>() = "AXD000" then
        Some (JsonNode.Parse(row.["message"].["text"].GetValue<string>()))
      else None)
  if axdRecords.Length <> files.Length then
    failwithf "%s: expected %d AXD000 records, found %d" label files.Length axdRecords.Length
  for path in files do
    let expectedHash = sha256Hex path
    let matched =
      axdRecords
      |> List.exists (fun recNode ->
        let hashedBy = recNode.["hashedBy"].GetValue<string>()
        let recorded = recNode.["hashes"].[path]
        hashedBy = path && not (isNull recorded) && String.Equals(recorded.GetValue<string>(), expectedHash, StringComparison.OrdinalIgnoreCase))
    if not matched then
      failwithf "%s: AXD000 record missing or hash mismatch for %s (expected %s)" label path expectedHash
  for (ruleId, expectedFile, expectedFragment, expectedLine) in expectedRules do
    let normExpected = Path.GetFullPath(expectedFile)
    let found =
      results
      |> List.exists (fun row ->
        let rid = row.["ruleId"].GetValue<string>()
        let levelNode = row.["level"]
        let isError = not (isNull levelNode) && levelNode.GetValue<string>() = "error"
        let msg = row.["message"].["text"].GetValue<string>()
        let locsNode = row.["locations"]
        let locMatches =
          not (isNull locsNode) &&
          locsNode.AsArray()
          |> Seq.exists (fun loc ->
            let phys = loc.["physicalLocation"]
            if isNull phys then false
            else
              let uriNode = phys.["artifactLocation"].["uri"]
              let regNode = phys.["region"]
              if isNull uriNode || isNull regNode then false
              else
                let lineNode = regNode.["startLine"]
                not (isNull lineNode) &&
                normalizeUri (uriNode.GetValue<string>()) = normExpected &&
                lineNode.GetValue<int>() = expectedLine)
        rid = ruleId && isError && locMatches && msg.Contains(expectedFragment, StringComparison.Ordinal))
    if not found then
      failwithf "%s: SARIF missing level=error %s at %s:%d containing '%s'" label ruleId normExpected expectedLine expectedFragment
  printfn "PASS %s SARIF + AXD000 (%d files verified, %d bound error checks)" label files.Length expectedRules.Length

let splitFiles (envName: string) =
  Environment.GetEnvironmentVariable(envName).Split(':', StringSplitOptions.RemoveEmptyEntries) |> Array.toList

let axc011Files = splitFiles "AXC011_FILES"
let axc010Files = splitFiles "AXC010_FILES"
let axc009Files = splitFiles "AXC009_FILES"
let mode = Environment.GetEnvironmentVariable "VERIFY_SARIF_MODE"

if String.IsNullOrEmpty mode || mode = "all" then
  verifySarif
    "axc011-ratchet"
    (Environment.GetEnvironmentVariable "AXC011_SARIF")
    axc011Files
    [ ("AXC011", axc011Files[0], "pins 24 site(s) but actual count is 0; tighten downward.", 1)
      ("AXC011", axc011Files[0], "System.Collections.Generic.Dictionary`2 in 'Traversal/SMTTransfer.fs' is not a pinned ratchet target.", 2)
      ("AXC011", axc011Files[1], "let mutable in 'Traversal/NewMutable.fs' is outside the checked-in ratchet.", 2)
      ("AXC011", axc011Files[2], "let mutable in 'Traversal/obj/AuthoredObjDebt.fs' is outside the checked-in ratchet.", 2)
      ("AXC011", axc011Files[3], "let mutable in '../Shared/LinkedDebt.fs' is outside the checked-in ratchet.", 2) ]
  verifySarif
    "axc010-refusal"
    (Environment.GetEnvironmentVariable "AXC010_SARIF")
    axc010Files
    [ ("AXC010", axc010Files[0], "Microsoft.FSharp.Core.FSharpRef`1 (binding 'nextRunId').", 2) ]
  verifySarif
    "axc009-refusal"
    (Environment.GetEnvironmentVariable "AXC009_SARIF")
    axc009Files
    [ ("AXC009", axc009Files[0], "System.Reflection.PropertyInfo", 4)
      ("AXC009", axc009Files[0], "Microsoft.FSharp.Reflection.FSharpType (assembly FSharp.Core).", 5)
      ("AXC009", axc009Files[0], "System.Reflection.MethodInfo", 6) ]
elif mode = "single-axc010" then
  verifySarif
    "axc010-refusal"
    (Environment.GetEnvironmentVariable "AXC010_SARIF")
    axc010Files
    [ ("AXC010", axc010Files[0], "Microsoft.FSharp.Core.FSharpRef`1 (binding 'nextRunId').", 2) ]
FSI
AXC011_SARIF="$evidence/axc011-ratchet.sarif" \
AXC011_FILES="$axc011_smt:$axc011_new:$axc011_obj:$axc011_linked:$axc011_clean" \
AXC010_SARIF="$evidence/axc010-refusal.sarif" \
AXC010_FILES="$axc010_next:$axc010_clean" \
AXC009_SARIF="$evidence/axc009-refusal.sarif" \
AXC009_FILES="$axc009_refl:$axc009_clean" \
dotnet fsi "$evidence/verify-refusal-sarif.fsx" > "$evidence/refusal-sarif-verify.log" 2>&1
# Negative controls for verify-refusal-sarif.fsx: tampered AXD000 hash and downgraded level/removed locations must fail
jq '(.runs[0].results[] | select(.ruleId == "AXD000") | .message.text) |= gsub("[0-9A-F]{64}"; "0000000000000000000000000000000000000000000000000000000000000000")' "$evidence/axc010-refusal.sarif" > "$evidence/axc010-tampered-hash.sarif"
tamper_hash_rc=0
VERIFY_SARIF_MODE=single-axc010 AXC011_FILES="$axc011_smt" AXC009_FILES="$axc009_refl" AXC010_SARIF="$evidence/axc010-tampered-hash.sarif" AXC010_FILES="$axc010_next:$axc010_clean" \
  dotnet fsi "$evidence/verify-refusal-sarif.fsx" > "$evidence/refusal-sarif-neg-hash.log" 2>&1 || tamper_hash_rc=$?
[[ $tamper_hash_rc -ne 0 ]] && grep -Fq 'AXD000 record missing or hash mismatch' "$evidence/refusal-sarif-neg-hash.log" || { printf 'verify-refusal-sarif.fsx failed to reject tampered AXD000 hash.\n' >&2; exit 1; }
jq '(.runs[0].results[] | select(.ruleId != "AXD000")) |= (.level = "note" | del(.locations))' "$evidence/axc010-refusal.sarif" > "$evidence/axc010-tampered-loc.sarif"
tamper_loc_rc=0
VERIFY_SARIF_MODE=single-axc010 AXC011_FILES="$axc011_smt" AXC009_FILES="$axc009_refl" AXC010_SARIF="$evidence/axc010-tampered-loc.sarif" AXC010_FILES="$axc010_next:$axc010_clean" \
  dotnet fsi "$evidence/verify-refusal-sarif.fsx" > "$evidence/refusal-sarif-neg-loc.log" 2>&1 || tamper_loc_rc=$?
[[ $tamper_loc_rc -ne 0 ]] && grep -Fq 'SARIF missing level=error AXC010' "$evidence/refusal-sarif-neg-loc.log" || { printf 'verify-refusal-sarif.fsx failed to reject downgraded level / stripped locations.\n' >&2; exit 1; }
rm -f "$evidence/axc010-tampered-hash.sarif" "$evidence/axc010-tampered-loc.sarif"
sha256sum "$tool_dir/bin/Debug/net10.0/Alex.Analyzers.dll" "$tool_dir/ProjectInputs.fsx" "$tool_dir/check-project.sh" "$tool_dir/tests/ContractFixture/Contract.fs" "$tool_dir/tests/ContractFixture/ContractFixture.fsproj" "$tool_dir/tests/InProject/InProject.fsproj" "$tool_dir/tests/InProject/Ensure.fs" "$source" "$dialects_source" "$elements_source" "$elements_clean_source" "$patterns_source" "$witnesses_source" "$values_source" "$tool_dir/tests/DependencyControls.fsx" "$tool_dir/tests/project-control.sh" "$evidence/analysis.log" "$evidence/dependency.log" "$evidence/ratchet.log" \
  "$axc011_proj" "$axc011_smt" "$axc011_new" "$axc011_obj" "$axc011_linked" "$axc011_clean" "$evidence/axc011-ratchet.log" "$evidence/axc011-ratchet.sarif" \
  "$axc011_growth_proj" "$axc011_growth_smt" "$evidence/axc011-growth.log" \
  "$axc011_stale_proj" "$axc011_stale_text" "$evidence/axc011-stale-pin.log" \
  "$axc010_proj" "$axc010_next" "$axc010_clean" "$evidence/axc010-refusal.log" "$evidence/axc010-refusal.sarif" \
  "$axc009_proj" "$axc009_refl" "$axc009_clean" "$evidence/axc009-refusal.log" "$evidence/axc009-refusal.sarif" \
  "$evidence/verify-refusal-sarif.fsx" "$evidence/refusal-sarif-verify.log" "$evidence/refusal-sarif-neg-hash.log" "$evidence/refusal-sarif-neg-loc.log" \
  "$evidence/clef-mode.log" "$evidence/clef-provenance-mode.log" "$evidence/alternate-argument.log" "$evidence/alternate-environment.log" "$evidence/alternate-wrapper.log" > "$evidence/truth.sha256"
printf 'PASS in-project historical predicate, AXA003-AXA010 layer controls, ratchet controls, project-mode AXC009/AXC010/AXC011 SARIF+AXD000 controls and the MLIRAccumulator property control; acceptance cases clean\n'
