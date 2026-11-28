#!/usr/bin/env bash
set -euo pipefail

pipeline=${1:-}
[[ -z "$pipeline" || "$pipeline" == --pipeline ]] || { printf 'Unknown truth-suite argument.\n' >&2; exit 2; }
if [[ "$pipeline" == --pipeline && -n ${ALEX_ANALYZER_ONLY:-} ]]; then
  printf 'Pipeline truth suite cannot be filtered.\n' >&2
  exit 2
fi

tool_dir=$(cd -P "$(dirname "$0")/.." && pwd)
repo_dir=$(git -C "$tool_dir" rev-parse --show-toplevel)
psg_dll=${ALEX_ANALYZER_PSG_DLL:-$tool_dir/tests/ContractFixture/bin/Debug/net10.0/Fidelity.PSG.dll}
impostor_dll=$tool_dir/tests/ImpostorFixture/bin/Debug/net10.0/Unrelated.Contract.dll
alex_dll=$tool_dir/tests/AlexFixture/bin/Debug/net10.0/Alex.dll
stale_dll=$tool_dir/tests/StaleContract/bin/Debug/net10.0/Fidelity.PSG.dll
alias_dll=$tool_dir/tests/AliasFixture/bin/Debug/net10.0/AliasFixture.dll
analyzers=${ALEX_ANALYZER_PATH:-$tool_dir/bin/Debug/net10.0}
[[ -f "$psg_dll" ]] || { printf 'Missing PSG contract assembly: %s\n' "$psg_dll" >&2; exit 1; }
[[ -f "$impostor_dll" ]] || { printf 'Missing impostor assembly: %s\n' "$impostor_dll" >&2; exit 1; }
[[ -f "$alex_dll" ]] || { printf 'Missing Alex fixture assembly: %s\n' "$alex_dll" >&2; exit 1; }
[[ -f "$stale_dll" ]] || { printf 'Missing stale contract assembly: %s\n' "$stale_dll" >&2; exit 1; }
[[ -f "$alias_dll" ]] || { printf 'Missing alias fixture assembly: %s\n' "$alias_dll" >&2; exit 1; }
if [[ -z ${ALEX_ANALYZER_ONLY:-} ]]; then
  sha256sum --check --status "$repo_dir/artifacts/alex-analyzers-tests/inproject-control/truth.sha256" || { printf 'In-project control receipt is missing or stale.\n' >&2; exit 1; }
fi
mkdir -p "$repo_dir/artifacts/alex-analyzers-tests"
scratch=$(mktemp -d "$repo_dir/artifacts/alex-analyzers-tests/run.XXXXXXXX")
printf '#r "%s"\nlet forward (r: Fidelity.PSG.Revision) = r\n' "$psg_dll" > "$scratch/forward.fsx"
printf '#r "%s"\nlet change (r: Fidelity.PSG.Revision) = { r with Header = r.Header }\n' "$psg_dll" > "$scratch/revision.fsx"
printf '#r "%s"\nlet change (n: Fidelity.PSG.SemanticNode) = { n with Kind = n.Kind }\n' "$psg_dll" > "$scratch/semantic-node.fsx"
printf '#r "%s"\nlet next (step: Fidelity.PSG.OccurrenceBreadcrumb) = { step with Ordinal = step.Ordinal + 1 }\n' "$psg_dll" > "$scratch/breadcrumb.fsx"
printf '#r "%s"\n#r "%s"\nlet change (r: Fidelity.PSG.Revision) = { r with Header = r.Header }\n' "$psg_dll" "$impostor_dll" > "$scratch/impostor.fsx"
printf '#r "%s"\nlet value = 1\n' "$impostor_dll" > "$scratch/missing-contract.fsx"
printf '#r "%s"\nlet value = 1\n' "$stale_dll" > "$scratch/stale-contract.fsx"
printf '#r "%s"\n#r "%s"\nopen Fidelity.PSG\nopen Alex.XParsec.PSGCombinators\nlet check (t: TypeIdentity) bits = ensure (match t with TypeIdentity.Application(c, []) -> c.Declaration.Name = "Mmio" + string bits | _ -> false) "bad"\n' "$psg_dll" "$alex_dll" > "$scratch/nominal-direct.fsx"
printf '#r "%s"\n#r "%s"\nopen Fidelity.PSG\nopen Alex.XParsec.PSGCombinators\nlet check (c: ConstructorIdentity) = let accepted = c.Declaration.Name = "Mmio8" in ensure accepted "bad"\n' "$psg_dll" "$alex_dll" > "$scratch/nominal-local.fsx"
printf '#r "%s"\n#r "%s"\nopen Fidelity.PSG\nopen Alex.XParsec.PSGCombinators\nlet check (c: ConstructorIdentity) = ensure true c.Declaration.Name\n' "$psg_dll" "$alex_dll" > "$scratch/nominal-message.fsx"
printf '#r "%s"\n#r "%s"\nopen Fidelity.PSG\nlet display (c: ConstructorIdentity) = c.Declaration.Name\n' "$psg_dll" "$alex_dll" > "$scratch/nominal-display.fsx"
printf '#r "%s"\n#r "%s"\nopen Fidelity.PSG\nlet ensure condition message = if condition then () else failwith message\nlet check (c: ConstructorIdentity) = ensure (c.Declaration.Name = "Mmio8") "bad"\n' "$psg_dll" "$alex_dll" > "$scratch/nominal-lookalike.fsx"
printf '#r "%s"\n#r "%s"\nopen Alex.XParsec.PSGCombinators\nlet check bits = ensure (bits = 8 || bits = 16 || bits = 32) "bad"\n' "$psg_dll" "$alex_dll" > "$scratch/published-width.fsx"
printf '#r "%s"\n#r "%s"\nopen Alex.XParsec.PSGCombinators\nlet check (operation: string) = ensure (operation.StartsWith "reg") "bad"\n' "$psg_dll" "$alex_dll" > "$scratch/published-string.fsx"
printf '#r "%s"\n#r "%s"\n#r "%s"\nopen Fidelity.PSG\nopen Alex.XParsec.PSGCombinators\nlet check (c: ConstructorIdentity) = ensure (c.Declaration.Name = "Mmio8") "bad"\n' "$psg_dll" "$impostor_dll" "$alex_dll" > "$scratch/nominal-impostor.fsx"
printf '#r "%s"\n#r "%s"\nopen Fidelity.PSG\nopen Alex.XParsec.PSGCombinators\nlet check (c: ConstructorIdentity) = ensure (c.Declaration.Name.StartsWith "Mmio") "bad"\n' "$psg_dll" "$alex_dll" > "$scratch/nominal-method.fsx"
printf '#r "%s"\n#r "%s"\nopen Fidelity.PSG\nopen Alex.XParsec.PSGCombinators\nlet check (c: ConstructorIdentity) = let n = c.Declaration.Name in ensure (n.StartsWith "M") "bad"\n' "$psg_dll" "$alex_dll" > "$scratch/nominal-method-local.fsx"
printf '#r "%s"\n#r "%s"\nopen Fidelity.PSG\nopen Alex.XParsec.PSGCombinators\nlet check (c: ConstructorIdentity) = ensure ("Mmio8".StartsWith c.Declaration.Name) "bad"\n' "$psg_dll" "$alex_dll" > "$scratch/nominal-method-arg.fsx"
printf '#r "%s"\n#r "%s"\nopen Fidelity.PSG\nopen Alex.XParsec.PSGCombinators\nlet check (c: ConstructorIdentity) = ensure (c.Declaration.Name.StartsWith("M", System.StringComparison.Ordinal)) "bad"\n' "$psg_dll" "$alex_dll" > "$scratch/nominal-method-overload.fsx"
printf '#r "%s"\n#r "%s"\nopen Fidelity.PSG\nopen Alex.XParsec.PSGCombinators\nlet check (c: ConstructorIdentity) = ensure (not (c.Declaration.Name.StartsWith "M")) "bad"\n' "$psg_dll" "$alex_dll" > "$scratch/nominal-method-not.fsx"
printf '#r "%s"\n#r "%s"\nopen Fidelity.PSG\nopen Alex.XParsec.PSGCombinators\nlet check (c: ConstructorIdentity) bits = ensure (bits = 8 && c.Declaration.Name.StartsWith "M") "bad"\n' "$psg_dll" "$alex_dll" > "$scratch/nominal-method-and.fsx"
printf '#r "%s"\n#r "%s"\nopen Fidelity.PSG\nopen Alex.XParsec.PSGCombinators\nlet check (c: ConstructorIdentity) = let mutable n = c.Declaration.Name in ensure (n.StartsWith "M") "bad"\n' "$psg_dll" "$alex_dll" > "$scratch/nominal-method-mutable.fsx"
printf '#r "%s"\n#r "%s"\nopen Alex.XParsec.PSGCombinators\nlet check () = ensure ("abc".StartsWith "a") "bad"\n' "$psg_dll" "$alex_dll" > "$scratch/nominal-method-literal.fsx"
printf '#r "%s"\n#r "%s"\nopen Alex.XParsec.PSGCombinators\nlet check (operation: string) x = let value, _ = operation, x in ensure (value.StartsWith "reg") "bad"\n' "$psg_dll" "$alex_dll" > "$scratch/nominal-method-published-local.fsx"
printf '#r "%s"\n#r "%s"\nopen Fidelity.PSG\nopen Alex.XParsec.PSGCombinators\nlet check (c: ConstructorIdentity) = ensure true (string (c.Declaration.Name.StartsWith "M"))\n' "$psg_dll" "$alex_dll" > "$scratch/nominal-method-message.fsx"
printf '#r "%s"\nopen Fidelity.PSG\nlet display (c: ConstructorIdentity) = c.Declaration.Name.StartsWith "M"\n' "$psg_dll" > "$scratch/nominal-method-display.fsx"
printf '#r "%s"\n#r "%s"\nopen Fidelity.PSG\nopen Alex.XParsec.PSGCombinators\nlet check (c: ConstructorIdentity) = ensure ((sprintf "%%s" c.Declaration.Name).StartsWith "M") "bad"\n' "$psg_dll" "$alex_dll" > "$scratch/nominal-method-format.fsx"
printf '#r "%s"\n#r "%s"\nopen Fidelity.PSG\nopen Alex.XParsec.PSGCombinators\nlet check (c: ConstructorIdentity) (table: Map<string, string>) = ensure ((Map.find c.Declaration.Name table).StartsWith "M") "bad"\n' "$psg_dll" "$alex_dll" > "$scratch/nominal-method-lookup.fsx"
printf '#r "%s"\n#r "%s"\nopen Fidelity.PSG\nopen Alex.XParsec.PSGCombinators\ntype Flag = { On: bool } with member f.StartsWith (_: string) = f.On\nlet check (c: ConstructorIdentity) (f: Flag) = ensure (f.StartsWith c.Declaration.Name) "bad"\n' "$psg_dll" "$alex_dll" > "$scratch/nominal-method-lookalike.fsx"
printf '#r "%s"\n#r "%s"\nopen Fidelity.PSG\nopen Alex.XParsec.PSGCombinators\nlet check (c: ConstructorIdentity) = ensure (c.Declaration.Module = "M") "bad"\n' "$psg_dll" "$alex_dll" > "$scratch/nominal-module.fsx"
printf '#r "%s"\n#r "%s"\nopen Fidelity.PSG\nopen Alex.XParsec.PSGCombinators\nlet check (c: CaptureInfo) = ensure (c.Name = "Mmio8") "bad"\n' "$psg_dll" "$alex_dll" > "$scratch/other-name-field.fsx"
printf '#r "%s"\n#r "%s"\nopen Fidelity.PSG\nopen Alex.XParsec.PSGCombinators\nlet check (c: ConstructorIdentity) = let a = c.Declaration.Name = "Mmio8" in let b = a in ensure b "bad"\n' "$psg_dll" "$alex_dll" > "$scratch/nominal-two-hop.fsx"
printf '#r "%s"\n#r "%s"\nopen Fidelity.PSG\nopen Alex.XParsec.PSGCombinators\nlet check (c: ConstructorIdentity) = let a = c.Declaration.Name = "Mmio8" in let b = a in let d = b in ensure d "bad"\n' "$psg_dll" "$alex_dll" > "$scratch/nominal-three-hop.fsx"
printf '#r "%s"\n#r "%s"\nopen Fidelity.PSG\nopen Alex.XParsec.PSGCombinators\nlet check (c: ConstructorIdentity) bits = let a = c.Declaration.Name = "Mmio8" in ensure (a && bits = 8) "bad"\n' "$psg_dll" "$alex_dll" > "$scratch/nominal-nested-and.fsx"
printf '#r "%s"\n#r "%s"\nopen Fidelity.PSG\nopen Alex.XParsec.PSGCombinators\nlet check (c: ConstructorIdentity) bits = let a = c.Declaration.Name = "Mmio8" in ensure (if a then true else bits = 8) "bad"\n' "$psg_dll" "$alex_dll" > "$scratch/nominal-nested-if.fsx"
printf '#r "%s"\n#r "%s"\nopen Fidelity.PSG\nopen Alex.XParsec.PSGCombinators\nlet check (t: TypeIdentity) = let a = match t with TypeIdentity.Application(c, []) -> c.Declaration.Name = "Mmio8" | _ -> false in ensure a "bad"\n' "$psg_dll" "$alex_dll" > "$scratch/nominal-local-match.fsx"
printf '#r "%s"\n#r "%s"\nopen Fidelity.PSG\nopen Alex.XParsec.PSGCombinators\nlet check (c: ConstructorIdentity) = let a = true in let result = a in let a = c.Declaration.Name = "Mmio8" in ensure result "bad"\n' "$psg_dll" "$alex_dll" > "$scratch/nominal-shadow.fsx"
printf '#r "%s"\n#r "%s"\nopen Fidelity.PSG\nopen Alex.XParsec.PSGCombinators\nlet check (c: ConstructorIdentity) bits = let name, width = c.Declaration.Name, bits in ensure (width = 8) "bad"\n' "$psg_dll" "$alex_dll" > "$scratch/nominal-destructured-width.fsx"
printf '#r "%s"\n#r "%s"\nopen Fidelity.PSG\nopen Alex.XParsec.PSGCombinators\nlet check (c: ConstructorIdentity) bits = let name, width = c.Declaration.Name, bits in ensure (name = "Mmio8") "bad"\n' "$psg_dll" "$alex_dll" > "$scratch/nominal-destructured-name.fsx"
printf '#r "%s"\n#r "%s"\nopen Fidelity.PSG\nopen Alex.XParsec.PSGCombinators\nlet check (c: ConstructorIdentity) = let mutable decision = c.Declaration.Name = "Mmio8" in ensure decision "bad"\n' "$psg_dll" "$alex_dll" > "$scratch/nominal-mutable-local.fsx"
printf '#r "%s"\n#r "%s"\nopen Fidelity.PSG\nopen Alex.XParsec.PSGCombinators\nlet nameIs (c: ConstructorIdentity) = c.Declaration.Name = "Mmio8"\nlet check c = let a = nameIs c in ensure a "bad"\n' "$psg_dll" "$alex_dll" > "$scratch/nominal-helper-local.fsx"
printf '#r "%s"\n#r "%s"\nopen Fidelity.PSG\nopen Alex.XParsec.PSGCombinators\nlet check (c: ConstructorIdentity) = ensure (not (c.Declaration.Name = "Mmio8")) "bad"\n' "$psg_dll" "$alex_dll" > "$scratch/nominal-not.fsx"
printf '#r "%s"\n#r "%s"\nopen Fidelity.PSG\nopen Alex.XParsec.PSGCombinators\nlet check (c: ConstructorIdentity) = let a = c.Declaration.Name = "Mmio8" in ensure (not a) "bad"\n' "$psg_dll" "$alex_dll" > "$scratch/nominal-not-local.fsx"
printf '#r "%s"\n#r "%s"\nopen Fidelity.PSG\nopen Alex.XParsec.PSGCombinators\nlet check (c: ConstructorIdentity) = let a = not (c.Declaration.Name = "Mmio8") in ensure a "bad"\n' "$psg_dll" "$alex_dll" > "$scratch/nominal-local-not.fsx"
printf '#r "%s"\n#r "%s"\nopen Fidelity.PSG\nopen Alex.XParsec.PSGCombinators\nlet check (c: ConstructorIdentity) bits = ensure (bits = 8 && not (c.Declaration.Name = "Mmio8")) "bad"\n' "$psg_dll" "$alex_dll" > "$scratch/nominal-not-nested.fsx"
printf '#r "%s"\n#r "%s"\nopen Fidelity.PSG\nopen Alex.XParsec.PSGCombinators\nlet check (c: ConstructorIdentity) = let mutable a = c.Declaration.Name = "Mmio8" in ensure (not a) "bad"\n' "$psg_dll" "$alex_dll" > "$scratch/nominal-not-mutable.fsx"
printf '#r "%s"\n#r "%s"\nopen Fidelity.PSG\nopen Alex.XParsec.PSGCombinators\n[<CompiledName("Not")>]\nlet not (v: bool) = v\nlet check (c: ConstructorIdentity) = ensure (not (c.Declaration.Name = "Mmio8")) "bad"\n' "$psg_dll" "$alex_dll" > "$scratch/nominal-not-lookalike.fsx"
printf '#r "%s"\n#r "%s"\nopen Fidelity.PSG\nopen Alex.XParsec.PSGCombinators\nlet check (c: ConstructorIdentity) table = ensure (not (Map.containsKey c.Declaration.Name table)) "bad"\n' "$psg_dll" "$alex_dll" > "$scratch/nominal-not-lookup.fsx"
printf '#r "%s"\n#r "%s"\nopen Fidelity.PSG\nopen Alex.XParsec.PSGCombinators\nlet nameIs (c: ConstructorIdentity) = c.Declaration.Name = "Mmio8"\nlet check c = ensure (not (nameIs c)) "bad"\n' "$psg_dll" "$alex_dll" > "$scratch/nominal-not-helper.fsx"
printf '#r "%s"\n#r "%s"\nopen Fidelity.PSG\nopen Alex.XParsec.PSGCombinators\nlet check (c: ConstructorIdentity) bits = ensure (not (bits = 8)) c.Declaration.Name\n' "$psg_dll" "$alex_dll" > "$scratch/nominal-not-message.fsx"
printf '#r "%s"\n#r "%s"\nopen Alex.XParsec.PSGCombinators\nlet check () = ensure (not false) "bad"\n' "$psg_dll" "$alex_dll" > "$scratch/nominal-not-pure.fsx"
printf '#r "%s"\n#r "%s"\nopen Fidelity.PSG\nopen Alex.XParsec.PSGCombinators\nlet check (c: ConstructorIdentity) = ensure (not (sprintf "%%s" c.Declaration.Name = "")) "bad"\n' "$psg_dll" "$alex_dll" > "$scratch/nominal-not-format.fsx"
printf '#r "%s"\n#r "%s"\nopen Fidelity.PSG\nopen Alex.XParsec.PSGCombinators\nlet check (c: ConstructorIdentity) = ensure ((c.Declaration.Name = "Mmio8") |> not) "bad"\n' "$psg_dll" "$alex_dll" > "$scratch/nominal-not-piped.fsx"
printf '#r "%s"\n#r "%s"\nopen Fidelity.PSG\nopen Alex.XParsec.PSGCombinators\nlet check (c: ConstructorIdentity) bits = let name = c.Declaration.Name in ensure (bits = 8) name\n' "$psg_dll" "$alex_dll" > "$scratch/nominal-message-local.fsx"
printf '#r "%s"\n#r "%s"\nopen Fidelity.PSG\nopen Alex.XParsec.PSGCombinators\nlet check (c: ConstructorIdentity) bits = let a = (ignore c.Declaration.Name; bits = 8) in ensure a "bad"\n' "$psg_dll" "$alex_dll" > "$scratch/nominal-logged-local.fsx"
printf '#r "%s"\n#r "%s"\nopen Fidelity.PSG\nopen Alex.XParsec.PSGCombinators\nlet check (c: ConstructorIdentity) bits = let a = ((c.Declaration.Name = "Mmio8"); bits = 8) in ensure a "bad"\n' "$psg_dll" "$alex_dll" > "$scratch/nominal-discarded-bool.fsx"
printf '#r "%s"\n#r "%s"\nopen Fidelity.PSG\nopen Alex.XParsec.PSGCombinators\nlet check (c: ConstructorIdentity) bits = ensure (ignore c.Declaration.Name; bits = 8) "bad"\n' "$psg_dll" "$alex_dll" > "$scratch/nominal-logged-direct.fsx"
printf '#r "%s"\n#r "%s"\nopen Fidelity.PSG\nopen Alex.XParsec.PSGCombinators\nlet check (c: ConstructorIdentity) bits = let a = (let unused = c.Declaration.Name in bits = 8) in ensure a "bad"\n' "$psg_dll" "$alex_dll" > "$scratch/nominal-unused-let.fsx"
printf '#r "%s"\n#r "%s"\nopen Fidelity.PSG\nopen Alex.XParsec.PSGCombinators\nlet check (c: ConstructorIdentity) = let nameIs (x: ConstructorIdentity) = x.Declaration.Name = "Mmio8" in ensure (nameIs c) "bad"\n' "$psg_dll" "$alex_dll" > "$scratch/nominal-local-function.fsx"
printf '#r "%s"\n#r "%s"\nopen Fidelity.PSG\nopen Alex.XParsec.PSGCombinators\nlet nameIs (c: ConstructorIdentity) = c.Declaration.Name = "Mmio8"\nlet check c = ensure (c |> nameIs) "bad"\n' "$psg_dll" "$alex_dll" > "$scratch/nominal-helper-piped.fsx"
printf '#r "%s"\n#r "%s"\nopen Fidelity.PSG\nlet display (c: ConstructorIdentity) = let name = c.Declaration.Name in name\n' "$psg_dll" "$alex_dll" > "$scratch/nominal-display-local.fsx"
printf '#r "%s"\n#r "%s"\nopen Fidelity.PSG\nopen Alex.XParsec.PSGCombinators\nlet decision = ({ Module = "M"; Name = "Mmio8" }: NominalTypeIdentity).Name = "Mmio8"\nlet check () = ensure decision "bad"\n' "$psg_dll" "$alex_dll" > "$scratch/nominal-module-value.fsx"
printf '#r "%s"\n#r "%s"\nopen Alex.XParsec.PSGCombinators\nlet check (flag: bool) = ensure flag "bad"\n' "$psg_dll" "$alex_dll" > "$scratch/nominal-parameter.fsx"
printf '#r "%s"\n#r "%s"\nopen Fidelity.PSG\nopen Alex.XParsec.PSGCombinators\nlet check (c: ConstructorIdentity) table = let row = Map.tryFind c.Declaration.Name table in ensure row.IsSome "bad"\n' "$psg_dll" "$alex_dll" > "$scratch/nominal-lookup.fsx"
printf '#r "%s"\n#r "%s"\nopen Fidelity.PSG\nopen Alex.XParsec.PSGCombinators\nlet check (c: ConstructorIdentity) table = ensure (Map.tryFind c.Declaration.Name table |> Option.isSome) "bad"\n' "$psg_dll" "$alex_dll" > "$scratch/nominal-lookup-direct.fsx"
printf 'let value: string = null\n' > "$scratch/null.fsx"
printf 'let check (s: string) = match s with null -> 0 | _ -> 1\n' > "$scratch/null-pattern.fsx"
printf 'open System\nlet value = 1\n' > "$scratch/system-open.fsx"
printf 'open type System.Math\nlet value = 1\n' > "$scratch/system-type-open.fsx"
printf 'let isUnion () = Microsoft.FSharp.Reflection.FSharpType.IsUnion(typeof<int option>)\n' > "$scratch/reflection-fsharp-type.fsx"
printf 'type Reader = Microsoft.FSharp.Reflection.FSharpValue\nlet keep (value: Reader) = value\n' > "$scratch/reflection-fsharp-alias.fsx"
printf 'let keep (value: System.Reflection.PropertyInfo) = value\n' > "$scratch/reflection-property.fsx"
printf 'let keep (value: System.Reflection.MethodInfo) = value\n' > "$scratch/reflection-method.fsx"
printf 'open Microsoft.FSharp.Quotations\nlet inspect expr = match expr with Patterns.Call(_, m, _) -> Some m | _ -> None\n' > "$scratch/reflection-quotation-call-inferred.fsx"
printf 'module FSharpValue =\n  let identity value = Option.map id value\nlet value = FSharpValue.identity (Some 1)\n' > "$scratch/reflection-lookalike.fsx"
printf 'module Entries =\n  let keep (value: System.Runtime.CompilerServices.ConditionalWeakTable<string, string>) = value\n' > "$scratch/cache-cwt.fsx"
printf 'type Table = System.Collections.Concurrent.ConcurrentDictionary<string, string>\nlet keep (table: Table) = table\n' > "$scratch/cache-concurrent-alias.fsx"
printf 'let slot: System.Threading.ThreadLocal<int> option = None\n' > "$scratch/cache-threadlocal.fsx"
printf 'type ConditionalWeakTable = { Entries: Map<string, string> } with member t.GetValue (key: string) = Map.tryFind key t.Entries\nlet cache: ConditionalWeakTable = { Entries = Map.empty }\nlet find key = cache.GetValue key\nlet names: Set<string> = Set.empty\nlet order: string list = []\n' > "$scratch/cache-lookalike.fsx"
printf 'let mutable cache: Map<string, int> = Map.empty\nlet remember (key: string) (value: int) = cache <- Map.add key value cache\n' > "$scratch/cache-module-mutable-map.fsx"
printf 'module Inner =\n  type Entries = Set<int>\n  let mutable nodes: Entries = Set.empty\n  let remember node = nodes <- Set.add node nodes\n' > "$scratch/cache-module-set-alias.fsx"
printf 'module Inner =\n  type Set<\x27T> = { Value: \x27T }\n  let mutable nodes: Set<int> = { Value = 0 }\n  let remember node = nodes <- { Value = node }\n' > "$scratch/cache-module-set-lookalike.fsx"
printf 'let collect (keys: string list) =\n  let mutable seen: Map<string, int> = Map.empty\n  for key in keys do seen <- Map.add key 1 seen\n  seen\n' > "$scratch/cache-local-mutable-map.fsx"
printf 'let table: Map<string, int> = Map.ofList [ ("a", 1); ("b", 2) ]\nlet lookup (key: string) = Map.tryFind key table\n' > "$scratch/cache-module-table.fsx"
printf 'let rows = ref Map.empty<string, int>\nlet remember key value = rows.Value <- Map.add key value rows.Value\n' > "$scratch/cache-module-ref-map.fsx"
printf 'module Inner =\n    type Entries = Set<int> ref\n    let rows: Entries = ref Set.empty\n    let remember value = rows.Value <- Set.add value rows.Value\n' > "$scratch/cache-module-ref-set-alias.fsx"
printf 'type Rows = Map<string, int>\nlet rows: Rows ref = ref Map.empty\n' > "$scratch/cache-module-ref-payload-alias.fsx"
printf 'let collect keys =\n    let rows = ref Map.empty<string, int>\n    for key in keys do rows.Value <- Map.add key 1 rows.Value\n    rows.Value\n' > "$scratch/cache-local-ref-map.fsx"
printf 'module Lookalike =\n    type FSharpRef<\x27T> = { mutable Value: \x27T }\n    let rows: FSharpRef<Map<string, int>> = { Value = Map.empty }\n' > "$scratch/cache-module-ref-lookalike.fsx"
printf 'module Lookalike =\n    type FSharpRef<\x27T> = { Value: \x27T }\n    let rows: FSharpRef<Map<string, int>> = { Value = Map.empty }\n' > "$scratch/cache-module-ref-lookalike-immutable.fsx"
printf 'type Holder = { Cell: int ref }\nlet holder = { Cell = ref 0 }\n' > "$scratch/cache-module-record-ref.fsx"
printf 'type ScopeIdSequence = { mutable Next: int64 }\nlet sequence = { Next = 0L }\n' > "$scratch/cache-module-scope-sequence.fsx"
printf 'type CellBox = Hold of int ref\nlet boxed = Hold (ref 0)\n' > "$scratch/cache-module-union-ref.fsx"
printf 'let pair = (1, ref 0)\n' > "$scratch/cache-module-tuple-ref.fsx"
printf 'let cells = [ ref 0 ]\n' > "$scratch/cache-module-list-ref.fsx"
printf 'let items = [| 0 |]\n' > "$scratch/cache-module-array.fsx"
printf 'type Counter() =\n  static let mutable count = 0\n  static member Next () = count <- count + 1; count\n' > "$scratch/cache-module-static-mutable.fsx"
printf 'type Counter() =\n  static member val Count = 0 with get, set\n' > "$scratch/cache-module-static-prop.fsx"
printf 'type Counter() =\n  static let cell = ref 0\n  static member Peek () = cell.Value\n' > "$scratch/cache-module-static-ref.fsx"
printf 'type Counter() =\n  static let zero = 0\n  static member val Constant = 1\n  static member Read () = zero\nlet instance = Counter()\n' > "$scratch/cache-module-static-immutable.fsx"
cat > "$scratch/cache-module-static-closure-ref.fsx" <<'FS'
type Counter() =
  static let next =
    let n = ref 0L
    fun () -> n.Value <- n.Value + 1L; n.Value
  static member Next () = next ()
FS
cat > "$scratch/cache-module-static-prop-closure-ref.fsx" <<'FS'
type Counter() =
  static member val Next =
    let n = ref 0L
    fun () -> n.Value <- n.Value + 1L; n.Value
FS
cat > "$scratch/cache-module-static-pure-fn.fsx" <<'FS'
type Counter() =
  static let pureAdd = fun (x: int) -> x + 1
  static member val PureAdd = fun (x: int) -> x + 1
  static member Apply x = pureAdd x
FS
cat > "$scratch/cache-module-static-tuple-closure-ref.fsx" <<'FS'
type Counter() =
  static let next, reset = let n = ref 0 in (fun () -> n.Value), (fun () -> n.Value <- 0)
  static member N () = next ()
  static member R () = reset ()
FS
cat > "$scratch/cache-module-static-tuple-pure.fsx" <<'FS'
type Counter() =
  static let inc, dec = let k = 1 in (fun x -> x + k), (fun x -> x - k)
  static member Inc x = inc x
  static member Dec x = dec x
FS
cat > "$scratch/cache-module-static-cctor-objexpr-ref.fsx" <<'FS'
type ICounter = abstract Next: unit -> int
type Counter() =
  static let n = ref 0
  static member val Shared : ICounter = { new ICounter with member _.Next() = n.Value <- n.Value + 1; n.Value }
FS
cat > "$scratch/cache-module-static-cctor-objexpr-pure.fsx" <<'FS'
type ICounter = abstract Next: unit -> int
type Counter() =
  static let k = 1
  static member val Shared : ICounter = { new ICounter with member _.Next() = k }
FS
cat > "$scratch/cache-module-static-cctor-id-lambda-ref.fsx" <<'FS'
type Counter() =
  static let n = ref 0
  static let next = id (fun () -> n.Value <- n.Value + 1; n.Value)
  static member Next () = next ()
FS
cat > "$scratch/cache-module-static-cctor-id-lambda-pure.fsx" <<'FS'
type Counter() =
  static let k = 1
  static let next = id (fun () -> k)
  static member Next () = next ()
FS
printf 'let next = (fun (n: int ref) () -> n.Value <- n.Value + 1; n.Value) (ref 0)\n' > "$scratch/cache-module-inline-app-ref.fsx"
printf 'let addOne = (fun (k: int) (x: int) -> k + x) 1\n' > "$scratch/cache-module-inline-app-pure.fsx"
printf 'let next = try (let n = ref 0 in fun () -> n.Value <- n.Value + 1; n.Value) finally ()\n' > "$scratch/cache-module-tryfinally-ref.fsx"
printf 'let pureFn = try (let k = 1 in fun () -> k) finally ()\n' > "$scratch/cache-module-tryfinally-pure.fsx"
cat > "$scratch/cache-module-app-mutable-return.fsx" <<'FS'
type Box() =
  let cell = ref 0
  member _.Peek() = cell.Value
let make = fun () -> Box()
let shared = make ()
FS
printf 'let handlers: Map<string, int ref -> int> = Map.empty\n' > "$scratch/cache-module-map-fn-ref.fsx"
printf 'let nextId =\n  let n = ref 0L\n  fun () -> n.Value <- n.Value + 1L; n.Value\n' > "$scratch/cache-module-closure-ref.fsx"
printf 'let private nextRunId = ref 0L\n' > "$scratch/cache-module-nextrunid.fsx"
printf 'module ScopeContext =\n  let private nextScopeId = ref 0L\n' > "$scratch/cache-module-nextscopeid.fsx"
printf 'let rows = ref 0\n' > "$scratch/cache-module-ref-scalar.fsx"
printf 'let mutable counter = 0\nlet bump () = counter <- counter + 1\n' > "$scratch/cache-module-mutable-scalar.fsx"
printf 'let counter = Some (ref 0)\nlet peek () = match counter with Some cell -> cell.Value | None -> 0\n' > "$scratch/cache-module-ref-option.fsx"
printf '#r "%s"\nopen Fidelity.PSG\nlet shared = NativeLiteral.ByteArray [| 0uy |]\n' "$psg_dll" > "$scratch/cache-module-psg-bytearray.fsx"
printf '#r "%s"\nopen Fidelity.PSG\nlet shared = NativeLiteral.Int 0L\n' "$psg_dll" > "$scratch/cache-module-psg-int-clean.fsx"
cat > "$scratch/cache-module-interface-upcast.fsx" <<'FS'
type ICounter = abstract Next: unit -> int
type Counter() =
  let cell = ref 0
  interface ICounter with member _.Next() = cell.Value <- cell.Value + 1; cell.Value
let shared : ICounter = Counter() :> ICounter
FS
cat > "$scratch/cache-module-derived-class-ref.fsx" <<'FS'
type BaseCounter() =
  let cell = ref 0
  member _.Peek() = cell.Value
type DerivedCounter() =
  inherit BaseCounter()
let shared = DerivedCounter()
FS
printf 'let runs = MailboxProcessor<int>.Start(fun inbox -> let rec loop () = async { let! _ = inbox.Receive() in return! loop () } in loop ())\n' > "$scratch/cache-module-mailbox.fsx"
printf 'let bus = Event<int>()\n' > "$scratch/cache-module-event.fsx"
printf 'type Factory<\x27a> = { Make: unit -> \x27a }\nlet shared : Factory<int ref> = { Make = fun () -> ref 0 }\n' > "$scratch/cache-module-factory-ref.fsx"
printf 'type Factory = { Make: unit -> int }\nlet shared : Factory = { Make = let n = ref 0 in fun () -> n.Value <- n.Value + 1; n.Value }\n' > "$scratch/cache-module-record-closure-ref.fsx"
cat > "$scratch/cache-module-object-expr-ref.fsx" <<'FS'
type ICounter = abstract Next: unit -> int
let shared : ICounter = let n = ref 0 in { new ICounter with member _.Next() = n.Value <- n.Value + 1; n.Value }
FS
cat > "$scratch/cache-module-nested-wrap-ref.fsx" <<'FS'
type Wrap<'a> = { Value: 'a }
let make () : Wrap<Wrap<int ref>> = { Value = { Value = ref 0 } }
let shared = make ()
FS
printf 'let accumulator keys =\n  let total = ref 0\n  for key in keys do total.Value <- total.Value + 1\n  total.Value\n' > "$scratch/local-ref-accumulator.fsx"
printf 'let thunk = lazy 1\nlet ready = thunk.IsValueCreated\n' > "$scratch/lazy-isvaluecreated.fsx"
printf 'type LazyLike = { IsValueCreated: bool }\nlet ready = { IsValueCreated = false }.IsValueCreated\n' > "$scratch/lazy-lookalike.fsx"
printf 'let pair = System.Threading.Tasks.ConcurrentExclusiveSchedulerPair()\n' > "$scratch/ambient-scheduler.fsx"
printf '[<System.ThreadStaticAttribute>]\nlet counter = 0\n' > "$scratch/ambient-threadstatic.fsx"
mkdir -p "$scratch/src/Alex/Controls"
printf 'let pure (xs: int list) = List.sum xs\n' > "$scratch/src/Alex/Controls/Axc011Immutable.fsx"
printf 'let bump () =\n  let mutable total = 0\n  total <- total + 1\n' > "$scratch/src/Alex/Controls/Axc011Mutable.fsx"
printf 'let collect xs =\n  let rows = ResizeArray<int>()\n  for x in xs do ignore (rows.Add x)\n  rows\n' > "$scratch/src/Alex/Controls/Axc011ResizeArray.fsx"
printf 'let make () = System.Collections.Generic.Dictionary<string, int>()\n' > "$scratch/src/Alex/Controls/Axc011Dictionary.fsx"
printf 'let make () = System.Collections.Generic.HashSet<int>()\n' > "$scratch/src/Alex/Controls/Axc011HashSet.fsx"
printf 'let make () = System.Collections.Generic.Queue<int>()\n' > "$scratch/src/Alex/Controls/Axc011Queue.fsx"
printf 'let make () = System.Collections.Generic.Stack<int>()\n' > "$scratch/src/Alex/Controls/Axc011Stack.fsx"
printf 'let make () = System.Collections.Queue()\n' > "$scratch/src/Alex/Controls/Axc011QueueNonGeneric.fsx"
printf 'let make () = System.Collections.Stack()\n' > "$scratch/src/Alex/Controls/Axc011StackNonGeneric.fsx"
printf 'let run () =\n  let mutable a = 1\n  let mutable b = 2\n  a + b\n' > "$scratch/src/Alex/Controls/Axc011Pinned.fsx"
printf 'let run () =\n  let mutable a = 1\n  let mutable b = 2\n  let mutable c = 3\n  a + b + c\n' > "$scratch/src/Alex/Controls/Axc011Growth.fsx"
printf 'let run () =\n  let mutable a = 1\n  a\n' > "$scratch/src/Alex/Controls/Axc011Shrink1.fsx"
printf 'let run () = 1\n' > "$scratch/src/Alex/Controls/Axc011Shrink0.fsx"
cat > "$scratch/src/Alex/Controls/Axc011SevenSites.fsx" <<'FS'
let plain () = let mutable visible = 10 in visible
let anonymous () = {| Value = (let mutable inAnonymous = 20 in inAnonymous) |}
type Row = { Value: int }
let record () = { Value = (let mutable inRecord = 30 in inRecord) }
let copy () = { (let mutable inCopy = { Value = 40 } in inCopy) with Value = 50 }
let matching () = async {
  match! async { let mutable inMatched = 60 in return inMatched } with
  | found -> let mutable inClause = 70 in return found + inClause
}
let shadowed () = let mutable n = 80 in (let mutable n = 81 in n)
let tupleSite () = let mutable (a, b) = (1, 2) in a + b
let wildSite () = let mutable _ = 1 in 0
exception CustomEx of int with
  member _.Compute() = let mutable inExn = 99 in inExn
FS
cat > "$scratch/src/Alex/Controls/Axc011ExceptionMember.fsx" <<'FS'
exception CustomEx of int with
  member _.Compute() = let mutable inExn = 99 in inExn
FS
cat > "$scratch/src/Alex/Controls/Axc011ExceptionMemberClean.fsx" <<'FS'
exception CustomEx of int with
  member _.Compute() = let inExn = 99 in inExn
FS
printf 'let tally (xs: ResizeArray<int>) = Seq.length xs\n' > "$scratch/src/Alex/Controls/Axc011ResizeArrayAnnotation.fsx"
cat > "$scratch/src/Alex/Controls/Axc011DictionaryLookalike.fsx" <<'FS'
namespace System.Collections.Generic
type Dictionary<'K, 'V> = Empty | Entry of 'K * 'V
module Use =
  let empty : Dictionary<string, int> = Empty
FS
cat > "$scratch/src/Alex/Controls/Axc011ClassAndObjectExpr.fsx" <<'FS'
type IBox = abstract Value: unit -> int
type Counter() =
  let mutable count = 0
  member _.Inc() = count <- count + 1; count
let makeObj () = { new IBox with member _.Value() = let mutable local = 1 in local <- local + 1; local }
FS
printf 'let run () = task { return 1 }\n' > "$scratch/task.fsx"
printf 'let builder = task\nlet run () = builder { return 1 }\n' > "$scratch/task-alias.fsx"
printf 'let task = 1\nlet run () = task + 1\n' > "$scratch/task-lookalike.fsx"
printf 'type P = int -> int\nlet call (p: P) = p 1\n' > "$scratch/abbreviation.fsx"
printf 'type Builder = System.Text.StringBuilder\nlet create () = Builder()\n' > "$scratch/bcl-alias.fsx"
printf 'let value = box 1\n' > "$scratch/box.fsx"
printf 'let widen = box\nlet value = widen 1\n' > "$scratch/box-alias.fsx"
printf 'let value = Microsoft.FSharp.Core.Operators.box 1\n' > "$scratch/box-qualified.fsx"
printf 'let box x = x + 1\nlet value = box 1\n' > "$scratch/box-lookalike.fsx"
printf 'let value = ("x" :> obj)\n' > "$scratch/upcast.fsx"
printf 'let consume (value: obj) = ()\nlet result = consume 1\n' > "$scratch/implicit-argument.fsx"
printf 'type Row = { Value: obj }\nlet row = { Value = 1 }\n' > "$scratch/implicit-field.fsx"
printf 'let values: obj list = [1; 2]\n' > "$scratch/implicit-list.fsx"
printf 'let identity (x: obj) = x\n' > "$scratch/object-identity.fsx"
printf 'type Alias = obj\nlet identity (value: obj) = value\n' > "$scratch/obj-declaration.fsx"
printf 'let values: obj list = []\n' > "$scratch/obj-list-type.fsx"
printf 'type obj = int\nlet identity (value: obj) = value\n' > "$scratch/obj-lookalike.fsx"
printf 'let identity (value: int) : int option = Some (value + 1)\nlet text: string = "ok"\n' > "$scratch/obj-primitives.fsx"
printf 'let read = System.IO.File.ReadAllText\n' > "$scratch/file-reference.fsx"
printf 'let make () = new System.IO.FileStream("x", System.IO.FileMode.Open)\n' > "$scratch/file-stream.fsx"
printf 'let make (stream: System.IO.Stream) = new System.IO.StreamReader(stream)\n' > "$scratch/stream-reader.fsx"
printf 'let traverse (xs: int list) = xs |> List.map (fun x -> Some (x + 1))\nlet text = "null is text"\n' > "$scratch/pure.fsx"
printf 'let render x = sprintf "%%d" x\nlet consume xs = for x in xs do ignore x\n' > "$scratch/generic-pure.fsx"
printf 'let consume (message: string) = message\nlet render (number: int) (reason: string) = consume $"Literal {number}: {reason}"\n' > "$scratch/interpolation-pure.fsx"
printf 'let consume (value: obj) = ()\nlet render (number: int) = consume $"Literal {number}"\n' > "$scratch/interpolation-obj.fsx"
printf 'let same (x: string) (y: string) = LanguagePrimitives.PhysicalEquality x y\n' > "$scratch/physical-equality.fsx"
printf 'let same = LanguagePrimitives.PhysicalEquality\nlet value = same "a" "b"\n' > "$scratch/physical-equality-alias.fsx"
printf 'let PhysicalEquality (x: int) (y: int) = x = y\nlet value = PhysicalEquality 1 1\n' > "$scratch/physical-equality-lookalike.fsx"
printf 'let render (x: int) = sprintf "%%A" x\n' > "$scratch/reflection-format.fsx"
printf 'let render (x: int) = sprintf "%%+A" x\n' > "$scratch/reflection-format-plus.fsx"
printf 'let render (x: int) = $"value: %%A{x}"\n' > "$scratch/reflection-format-interpolated.fsx"
printf 'let bad () : int = failwith "error"\n' > "$scratch/exception-failwith.fsx"
printf 'let bad (x: int) : int = invalidArg "x" "error"\n' > "$scratch/exception-invalidarg.fsx"
printf 'let bad () = try 1 with _ -> 0\n' > "$scratch/exception-trywith.fsx"
for alias in Foreign ObjectAlias ObjectNominal Chain Builders Handler Pair Both Boxed Arr Text Names Lookup Function PurePair Optional Generic NestedObj NestedForeign Anonymous AnonymousObj Distance Ints UnitFunction Nat Resizable LazyValue Sequence LocalAlias ExceptionType BigInteger DecimalValue; do
  type_name=$alias
  case "$alias" in Boxed|Generic) type_name="$alias<int>" ;; esac
  printf '#r "%s"\nlet x (v: AliasFixture.%s) = v\n' "$alias_dll" "$type_name" > "$scratch/alias-$alias.fsx"
done
printf 'let invalid =\n' > "$scratch/invalid.fsx"
cat > "$scratch/nested-null.fsx" <<'FS'
type Record = { Value: int }

type Builder() =
  member _.Bind(value, continuation) = continuation value
  member _.Return(value) = value

let computation = Builder()
let initial = { Value = 1 }
let field = {| Value = (null: string) |}
let copy = { (let _ = (null: string) in initial) with Value = 2 }

let matched =
  computation {
    match! (let _ = (null: string) in Some 3) with
    | Some value -> return value
    | None -> return 0
  }

FS
sed 's/(null: string)/""/g' "$scratch/nested-null.fsx" > "$scratch/nested-clean.fsx"
sed 's/| Some value -> return value/| Some value -> return (try value with _ -> 0)/' "$scratch/nested-clean.fsx" > "$scratch/nested-trywith.fsx"

cat > "$scratch/integer-literals.fsx" <<'FS'
let values: bigint list = [0I; 1I; -1I; 18446744073709551615I]
let compare x = x > 0I
let plain () = let mutable visible = 10I in visible
let anonymous () = {| Value = (let mutable inAnonymous = 20I in inAnonymous) |}
type Row = { Value: bigint }
let record () = { Value = (let mutable inRecord = 30I in inRecord) }
let copy () = { (let mutable inCopy = { Value = 40I } in inCopy) with Value = 50I }
let matching () = async {
    match! async { let mutable inMatched = 60I in return inMatched } with
    | found -> let mutable inClause = 70I in return found + inClause
}
let shadowed () = let mutable n = 80I in (let mutable n = 81I in n)
let nativeWidths = 3n, 4un
FS
printf 'let value = 0I\nopen System\n' > "$scratch/integer-literal-open.fsx"
cat > "$scratch/integer-literal-constructor.fsx" <<'FS'
let value = 0I
let n = System.Numerics.BigInteger(1)
let signed (x: System.IntPtr) = x
let unsigned (x: System.UIntPtr) = x
FS
printf 'let value = 0I\nlet n = System.Numerics.BigInteger.Parse("1")\n' > "$scratch/integer-literal-parse.fsx"
printf 'module NumericLiteralI =\n  let FromZero () = System.Numerics.BigInteger.Zero\nlet value = 0I\n' > "$scratch/integer-literal-custom.fsx"

run_case() {
  local name=$1 expected=$2 positions=${3:-} object_positions=${4:-} reason count rc=0 analyzer='Alex pure-core baseline'
  if [[ -n ${ALEX_ANALYZER_ONLY:-} && "$name" != "$ALEX_ANALYZER_ONLY" ]]; then return 0; fi
  executed=$((executed + 1))
  cases+=("$name")
  case "$name" in src/Alex/*) analyzer='Alex pure-core baseline' ;; forward|revision|semantic-node|breadcrumb|impostor|missing-contract|stale-contract|nominal-*|other-name-field|published-width|published-string|Dialects/*|Elements/*|Patterns/*|Traversal/*|Witnesses/*|XParsec/*|Generation) analyzer='Alex published boundary' ;; esac
  (cd "$tool_dir" && dotnet fsharp-analyzers --script "$scratch/$name.fsx" --analyzers-path "$analyzers" --include-analyzers "$analyzer" --fail-on-type-errors) > "$scratch/$name.log" 2>&1 || rc=$?
  case "$expected" in
    clean|known-miss|policy-pending) [[ $rc -eq 0 ]] && ! grep -Eq 'AX[AC][0-9]+' "$scratch/$name.log" ;;
    AXC009)
      local identity=$object_positions required=0
      for position in $positions; do
        grep -Fq "$scratch/$name.fsx($position): Error AXC009 : Alex production code must not use reflection APIs: $identity." "$scratch/$name.log" || { printf 'FAIL %s AXC009 identity at %s (log %s)\n' "$name" "$position" "$scratch/$name.log" >&2; return 1; }
        required=$((required + 1))
        if [[ $identity == System.Reflection.* ]]; then
          grep -Fq "$scratch/$name.fsx($position): Error AXC002 : Alex production code must not depend on .NET library APIs:" "$scratch/$name.log" || { printf 'FAIL %s AXC002 identity at %s\n' "$name" "$position" >&2; return 1; }
          required=$((required + 1))
        fi
      done
      count=$(grep -Ec 'Error AX[AC][0-9]+' "$scratch/$name.log" || true)
      [[ $rc -ne 0 && $count -eq $required ]]
      ;;
    AXC010)
      local identity=$object_positions required=0
      for position in $positions; do
        grep -Fq "$scratch/$name.fsx($position): Error AXC010 : Alex production code must not hold ConditionalWeakTable, System.Collections.Concurrent or ThreadLocal state: $identity (assembly " "$scratch/$name.log" || { printf 'FAIL %s AXC010 identity at %s (log %s)\n' "$name" "$position" "$scratch/$name.log" >&2; return 1; }
        grep -Fq "$scratch/$name.fsx($position): Error AXC002 : Alex production code must not depend on .NET library APIs:" "$scratch/$name.log" || { printf 'FAIL %s AXC002 identity at %s\n' "$name" "$position" >&2; return 1; }
        required=$((required + 2))
      done
      count=$(grep -Ec 'Error AX[AC][0-9]+' "$scratch/$name.log" || true)
      [[ $rc -ne 0 && $count -eq $required ]]
      ;;
    AXC010-state)
      local reason=$object_positions required=0
      [[ $rc -ne 0 ]] || { printf 'FAIL %s %s exited clean\n' "$name" "$expected" >&2; return 1; }
      for position in $positions; do
        grep -Fq "$scratch/$name.fsx($position): Error AXC010 : $reason" "$scratch/$name.log" || { printf 'FAIL %s missing AXC010 at %s (log %s)\n' "$name" "$position" "$scratch/$name.log" >&2; return 1; }
        grep -Fq "$scratch/$name.fsx($position): Error AXC002 : Alex production code must not depend on .NET library APIs:" "$scratch/$name.log" || { printf 'FAIL %s missing AXC002 at %s (log %s)\n' "$name" "$position" "$scratch/$name.log" >&2; return 1; }
        required=$((required + 2))
      done
      count=$(grep -Ec 'Error AX[AC][0-9]+' "$scratch/$name.log" || true)
      [[ $count -eq $required ]]
      ;;
    AXC010-static-pair)
      [[ $rc -ne 0 ]] || { printf 'FAIL %s %s exited clean\n' "$name" "$expected" >&2; return 1; }
      count=$(grep -Ec 'Error AX[AC][0-9]+' "$scratch/$name.log" || true)
      [[ $count -eq 2 ]] || { printf 'FAIL %s diagnostic count (exit %s; log %s)\n' "$name" "$rc" "$scratch/$name.log" >&2; return 1; }
      grep -Fq "$scratch/$name.fsx(2,13): Error AXC010 : Alex production code must not hold type-static mutable state or ref cells: type Microsoft.FSharp.Core.unit -> Microsoft.FSharp.Core.int (field 'Counter.next')." "$scratch/$name.log" || { printf 'FAIL %s missing Counter.next at 2,13 (log %s)\n' "$name" "$scratch/$name.log" >&2; return 1; }
      grep -Fq "$scratch/$name.fsx(2,19): Error AXC010 : Alex production code must not hold type-static mutable state or ref cells: type Microsoft.FSharp.Core.unit -> Microsoft.FSharp.Core.unit (field 'Counter.reset')." "$scratch/$name.log" || { printf 'FAIL %s missing Counter.reset at 2,19 (log %s)\n' "$name" "$scratch/$name.log" >&2; return 1; }
      ;;
    AXC011)
      local reason=$object_positions required=0
      [[ $rc -ne 0 ]] || { printf 'FAIL %s %s exited clean\n' "$name" "$expected" >&2; return 1; }
      for position in $positions; do
        grep -Fq "$scratch/$name.fsx($position): Error AXC011 : $reason" "$scratch/$name.log" || { printf 'FAIL %s missing AXC011 at %s (log %s)\n' "$name" "$position" "$scratch/$name.log" >&2; return 1; }
        required=$((required + 1))
      done
      count=$(grep -Ec 'Error AX[AC][0-9]+' "$scratch/$name.log" || true)
      [[ $count -eq $required ]]
      ;;
    AXC011+AXC002)
      local reason=$object_positions required=0
      [[ $rc -ne 0 ]] || { printf 'FAIL %s %s exited clean\n' "$name" "$expected" >&2; return 1; }
      for position in $positions; do
        grep -Fq "$scratch/$name.fsx($position): Error AXC011 : $reason" "$scratch/$name.log" || { printf 'FAIL %s missing AXC011 at %s (log %s)\n' "$name" "$position" "$scratch/$name.log" >&2; return 1; }
        grep -Fq "$scratch/$name.fsx($position): Error AXC002 : Alex production code must not depend on .NET library APIs:" "$scratch/$name.log" || { printf 'FAIL %s missing AXC002 at %s (log %s)\n' "$name" "$position" "$scratch/$name.log" >&2; return 1; }
        required=$((required + 2))
      done
      count=$(grep -Ec 'Error AX[AC][0-9]+' "$scratch/$name.log" || true)
      [[ $count -eq $required ]]
      ;;
    type-error) [[ $rc -ne 0 ]] && grep -Fq 'did not type check and --fail-on-type-errors was passed' "$scratch/$name.log" ;;
    AXA003+AXA004)
      count=$(grep -Ec 'Error AX[AC][0-9]+' "$scratch/$name.log" || true)
      [[ $rc -ne 0 && $count -eq 2 ]] || { printf 'FAIL %s diagnostic count (exit %s; log %s)\n' "$name" "$rc" "$scratch/$name.log" >&2; return 1; }
      for pos_code in $positions; do
        pos="${pos_code%%:*}"; code="${pos_code#*:}"
        grep -Fq "$scratch/$name.fsx($pos): Error $code :" "$scratch/$name.log" || { printf 'FAIL %s %s at %s (log %s)\n' "$name" "$code" "$pos" "$scratch/$name.log" >&2; return 1; }
      done
      ;;
    AXA005+AXA000-facts)
      count=$(grep -Ec 'Error AX[AC][0-9]+' "$scratch/$name.log" || true)
      [[ $rc -ne 0 && $count -eq 2 ]] || { printf 'FAIL %s diagnostic count (exit %s; log %s)\n' "$name" "$rc" "$scratch/$name.log" >&2; return 1; }
      grep -Fq "$scratch/$name.fsx(3,44): Error AXA005 : Mutable local 'facts' is forbidden in non-traversal Alex layers." "$scratch/$name.log" || { printf 'FAIL %s AXA005\n' "$name" >&2; return 1; }
      grep -Fq "$scratch/$name.fsx(3,76): Error AXA000 : Cannot establish DeclarationFacts provenance through mutable local 'facts'." "$scratch/$name.log" || { printf 'FAIL %s AXA000\n' "$name" >&2; return 1; }
      ;;
    *)
      case "$expected" in
        AXA001) reason='Alex must not construct or update published PSG records.' ;;
        AXA000) reason='The referenced Fidelity.PSG contract must define Revision, SemanticNode and NominalTypeIdentity.Name.' ;;
        AXA000-mutable) expected=AXA000; reason="Cannot establish nominal predicate provenance through mutable local 'decision'." ;;
        AXA000-mutable-a) expected=AXA000; reason="Cannot establish nominal predicate provenance through mutable local 'a'." ;;
        AXA000-mutable-n) expected=AXA000; reason="Cannot establish nominal predicate provenance through mutable local 'n'." ;;
        AXA000-mutable-opt) expected=AXA000; reason="Cannot establish published-fact option provenance through mutable local 'opt'." ;;
        AXA000-mutable-facts) expected=AXA000; reason="Cannot establish DeclarationFacts provenance through mutable local 'facts'." ;;
        AXA002) reason='Alex must not derive an admission predicate from a nominal declaration name.' ;;
        AXA003-fn) expected=AXA003; reason="Alex must confine Revision.Nodes and Revision.tryNode to Traversal/, XParsec/, or Generation.fs (in 'bad')." ;;
        AXA004-fn) expected=AXA004; reason="Alex must not write recursive SemanticKind or Revision.Nodes catamorphisms outside Traversal/NanopassArchitecture.fs (tryWitnesses) (in 'bad')." ;;
        AXA004-outer-bad) expected=AXA004; reason="Alex must not write recursive SemanticKind or Revision.Nodes catamorphisms outside Traversal/NanopassArchitecture.fs (tryWitnesses) (in 'outer.bad')." ;;
        AXA005-elem) expected=AXA005; reason='Elements must not ' ;;
        AXA005-mutable-x) expected=AXA005; reason="Mutable local 'x' is forbidden in non-traversal Alex layers." ;;
        AXA005-ref) expected=AXA005; reason='Mutable ref cells (ref) are forbidden in non-traversal Alex layers.' ;;
        AXA006) reason='Alex must not extract payloads from BoundaryImport.DeclarationFacts; only key-presence checks (ContainsKey / Map.containsKey) are permitted.' ;;
        AXA007-fn) expected=AXA007; reason="Alex must not collapse None from a published-fact or symbol lookup into a fallback value (in 'bad')." ;;
        AXA005-witness) expected=AXA005; reason="Mutable locals, mutable bindings and ref cells are forbidden in Witnesses/ (in 'bad')." ;;
        AXA008-fn) expected=AXA008; reason="Alex must not call MLIRAccumulator.bind*, completeVoid, forgetVoid, restoreOperands or registerSSAType, or assign an MLIRAccumulator property, outside Traversal/TransferTypes.fs and Traversal/NanopassArchitecture.fs (in 'bad')." ;;
        AXA009-construction) expected=AXA009; reason="Alex must not construct an SSA union case outside Traversal/Values.fs (in 'bad')." ;;
        AXA009-values) expected=AXA009; reason="Alex must take SSA names from getNodeSSA / getNodeSSAs; direct uses of the SSA-producing members of Alex.Traversal.Values are confined to Traversal/Values.fs and XParsec/PSGCombinators.fs (in 'bad')." ;;
        AXA010-fn) expected=AXA010; reason="Alex must not call NanopassArchitecture.visitAllNodes or ScopeContext.root / createChild / addOp / addOps / enterScope / exitScope in Patterns/ or in a Witnesses/ function that is not a pinned scope boundary (in 'bad')." ;;
        AXA010-smt) expected=AXA010; reason="Alex must not call SMTTransfer.operations or SMTTransfer.transfer in Patterns/ or Witnesses/ (in 'bad')." ;;
        AXC001) reason='Alex production code must not use null.' ;;
        AXC002) reason='Alex production code must not depend on .NET library APIs:' ;;
        AXC003) reason='Alex production code must not use task computation expressions.' ;;
        AXC004) reason='Alex production code must not widen a value to obj.' ;;
        AXC005) reason='Alex production code must not declare obj types.' ;;
        AXC006) reason='Alex production code must not use reference identity (PhysicalEquality or ReferenceEquals).' ;;
        AXC007) reason='Alex production code must not use %A reflection formatting.' ;;
        AXC008) reason='Alex production code must not throw or catch CLR exceptions.' ;;
        AXC010-module-map) expected=AXC010; reason="Alex production code must not hold module-level mutable Map or Set state: Microsoft.FSharp.Collections.FSharpMap\`2 (binding '$4')."; object_positions= ;;
        AXC010-module-set) expected=AXC010; reason="Alex production code must not hold module-level mutable Map or Set state: Microsoft.FSharp.Collections.FSharpSet\`1 (binding '$4')."; object_positions= ;;
        AXC010-any) expected=AXC010; reason="Alex production code must not hold module-level mutable state or ref cells: $4"; object_positions= ;;
        AXC010-static) expected=AXC010; reason="Alex production code must not hold type-static mutable state or ref cells: $4"; object_positions= ;;
        *) printf 'Unknown expected diagnostic %s\n' "$expected" >&2; return 1 ;;
      esac
      count=$(grep -Ec 'Error AX[AC][0-9]+' "$scratch/$name.log" || true)
      [[ $rc -ne 0 && $count -eq $(( $(wc -w <<< "$positions") + $(wc -w <<< "$object_positions") )) ]] || { printf 'FAIL %s diagnostic count (exit %s; log %s)\n' "$name" "$rc" "$scratch/$name.log" >&2; return 1; }
      for position in $positions; do
        grep -Fq "$scratch/$name.fsx($position): Error $expected : $reason" "$scratch/$name.log" || { printf 'FAIL %s diagnostic at %s (log %s)\n' "$name" "$position" "$scratch/$name.log" >&2; return 1; }
      done
      for position in $object_positions; do
        grep -Fq "$scratch/$name.fsx($position): Error AXC005 : Alex production code must not declare obj types." "$scratch/$name.log" || { printf 'FAIL %s obj diagnostic at %s (log %s)\n' "$name" "$position" "$scratch/$name.log" >&2; return 1; }
      done
      if [[ $expected == AXC002 ]]; then
        [[ $(grep -Ec 'Error AXC002 : .+ \(assembly .+\)\.' "$scratch/$name.log" || true) -eq $(wc -w <<< "$positions") ]] || { printf 'FAIL %s missing resolved identity\n' "$name" >&2; return 1; }
      fi
      ;;
  esac || { printf 'FAIL %s %s (exit %s; log %s)\n' "$expected" "$name" "$rc" "$scratch/$name.log" >&2; return 1; }
  if [[ $expected == known-miss ]]; then known_misses+=("$name"); printf 'KNOWN-MISS %s\n' "$name"; elif [[ $expected == policy-pending ]]; then policy_pending+=("$name"); printf 'POLICY-PENDING %s\n' "$name"; else printf 'PASS %s\n' "$name"; fi
}

executed=0
cases=()
known_misses=()
policy_pending=()
run_case forward clean
run_case revision AXA001 '2,40'
run_case semantic-node AXA001 '2,44'
run_case breadcrumb clean
run_case impostor clean
run_case missing-contract AXA000 '1,0'
run_case stale-contract AXA000 '1,0'
run_case nominal-direct AXA002 '5,35'
run_case nominal-local AXA002 '5,84'
run_case nominal-message clean
run_case nominal-display clean
run_case nominal-lookalike clean
run_case published-width clean
run_case published-string clean
run_case nominal-impostor clean
run_case nominal-method AXA002 '5,37'
run_case nominal-method-local AXA002 '5,67'
run_case nominal-method-arg AXA002 '5,37'
run_case nominal-method-overload AXA002 '5,37'
run_case nominal-method-not AXA002 '5,37'
run_case nominal-method-and AXA002 '5,42'
run_case nominal-method-mutable AXA000-mutable-n '5,75'
run_case nominal-method-literal clean
run_case nominal-method-published-local clean
run_case nominal-method-message clean
run_case nominal-method-display clean
run_case nominal-method-format known-miss
run_case nominal-method-lookup policy-pending
run_case nominal-method-lookalike known-miss
run_case nominal-module known-miss
run_case other-name-field clean
run_case nominal-two-hop AXA002 '5,90'
run_case nominal-three-hop AXA002 '5,103'
run_case nominal-nested-and AXA002 '5,82'
run_case nominal-nested-if AXA002 '5,82'
run_case nominal-local-match AXA002 '5,131'
run_case nominal-shadow clean
run_case nominal-destructured-width clean
run_case nominal-destructured-name known-miss
run_case nominal-mutable-local AXA000-mutable '5,92'
run_case nominal-helper-local known-miss
run_case nominal-not AXA002 '5,37'
run_case nominal-not-local AXA002 '5,77'
run_case nominal-local-not AXA002 '5,83'
run_case nominal-not-nested AXA002 '5,42'
run_case nominal-not-mutable AXA000-mutable-a '5,85'
run_case nominal-not-lookalike clean
run_case nominal-not-lookup policy-pending
run_case nominal-not-helper clean
run_case nominal-not-message clean
run_case nominal-not-pure clean
# Formatting hides the nominal predicate behind a call; it remains outside this rule.
run_case nominal-not-format known-miss
# The pipe's left operand exposes Name independently of the Not exception.
run_case nominal-not-piped AXA002 '5,37'
run_case nominal-message-local clean
run_case nominal-logged-local clean
run_case nominal-discarded-bool clean
run_case nominal-logged-direct clean
run_case nominal-unused-let clean
run_case nominal-local-function known-miss
run_case nominal-helper-piped known-miss
run_case nominal-display-local clean
run_case nominal-module-value known-miss
run_case nominal-parameter clean
run_case nominal-lookup policy-pending
run_case nominal-lookup-direct policy-pending
run_case pure clean
run_case reflection-fsharp-type AXC009 '1,45 1,17' 'Microsoft.FSharp.Reflection.FSharpType (assembly FSharp.Core)'
run_case reflection-fsharp-alias AXC009 '1,14 2,17' 'Microsoft.FSharp.Reflection.FSharpValue (assembly FSharp.Core)'
run_case reflection-property AXC009 '1,17' 'System.Reflection.PropertyInfo (assembly System.Runtime)'
run_case reflection-method AXC009 '1,17' 'System.Reflection.MethodInfo (assembly System.Runtime)'
run_case reflection-quotation-call-inferred AXC009 '2,35' 'System.Reflection.MethodInfo (assembly netstandard)'
run_case reflection-lookalike clean
run_case cache-cwt AXC010 '2,19' 'System.Runtime.CompilerServices.ConditionalWeakTable`2'
run_case cache-concurrent-alias AXC010 '1,13 2,17' 'System.Collections.Concurrent.ConcurrentDictionary`2'
run_case cache-threadlocal AXC010 '1,10' 'System.Threading.ThreadLocal`1'
run_case cache-lookalike clean
run_case cache-module-mutable-map AXC010-module-map '1,12' cache
run_case cache-module-set-alias AXC010-module-set '3,14' nodes
run_case cache-local-mutable-map clean
run_case cache-module-table clean
run_case cache-module-ref-map AXC010-module-map '1,4' rows
run_case cache-module-ref-set-alias AXC010-module-set '3,8' rows
run_case cache-module-ref-payload-alias AXC010-module-map '2,4' rows
run_case cache-local-ref-map clean
run_case cache-module-ref-lookalike AXC010-any '3,8' "Cache-module-ref-lookalike.Lookalike.FSharpRef\`1 (binding 'rows')."
run_case cache-module-ref-lookalike-immutable clean
run_case cache-module-record-ref AXC010-any '2,4' "Cache-module-record-ref.Holder (binding 'holder')."
run_case cache-module-scope-sequence AXC010-any '2,4' "Cache-module-scope-sequence.ScopeIdSequence (binding 'sequence')."
run_case cache-module-union-ref AXC010-any '2,4' "Cache-module-union-ref.CellBox (binding 'boxed')."
run_case cache-module-tuple-ref AXC010-any '1,4' "type Microsoft.FSharp.Core.int * Microsoft.FSharp.Core.int Microsoft.FSharp.Core.ref (binding 'pair')."
run_case cache-module-list-ref AXC010-any '1,4' "Microsoft.FSharp.Collections.FSharpList\`1 (binding 'cells')."
run_case cache-module-array AXC010-any '1,4' "System.Array (binding 'items')."
run_case cache-module-static-mutable AXC010-static '2,21' "System.Int32 (field 'Counter.count')."
run_case cache-module-static-prop AXC010-static '2,28' "System.Int32 (field 'Counter.Count@')."
run_case cache-module-static-ref AXC010-static '2,13' "Microsoft.FSharp.Core.FSharpRef\`1 (field 'Counter.cell')."
run_case cache-module-static-immutable clean
run_case cache-module-static-closure-ref AXC010-static '2,13' "type Microsoft.FSharp.Core.unit -> Microsoft.FSharp.Core.int64 (field 'Counter.next')."
run_case cache-module-static-prop-closure-ref AXC010-static '3,4' "type Microsoft.FSharp.Core.unit -> Microsoft.FSharp.Core.int64 (field 'Counter.Next@')."
run_case cache-module-static-pure-fn clean
run_case cache-module-static-tuple-closure-ref AXC010-static-pair
run_case cache-module-static-tuple-pure clean
run_case cache-module-static-cctor-objexpr-ref AXC010-static '4,40' "Cache-module-static-cctor-objexpr-ref.ICounter (field 'Counter.Shared@')."
run_case cache-module-static-cctor-objexpr-pure clean
run_case cache-module-static-cctor-id-lambda-ref AXC010-static '3,13' "type Microsoft.FSharp.Core.unit -> Microsoft.FSharp.Core.int (field 'Counter.next')."
run_case cache-module-static-cctor-id-lambda-pure clean
run_case cache-module-inline-app-ref AXC010-any '1,4' "type Microsoft.FSharp.Core.unit -> Microsoft.FSharp.Core.int (binding 'next')."
run_case cache-module-inline-app-pure clean
run_case cache-module-tryfinally-ref AXC010-any '1,4' "type Microsoft.FSharp.Core.unit -> Microsoft.FSharp.Core.int (binding 'next')."
run_case cache-module-tryfinally-pure clean
run_case cache-module-app-mutable-return AXC010-any '5,4' "Cache-module-app-mutable-return.Box (binding 'shared')."
run_case cache-module-map-fn-ref clean
run_case cache-module-closure-ref AXC010-any '1,4' "type Microsoft.FSharp.Core.unit -> Microsoft.FSharp.Core.int64 (binding 'nextId')."
run_case cache-module-nextrunid AXC010-any '1,12' "Microsoft.FSharp.Core.FSharpRef\`1 (binding 'nextRunId')."
run_case cache-module-nextscopeid AXC010-any '2,14' "Microsoft.FSharp.Core.FSharpRef\`1 (binding 'nextScopeId')."
run_case cache-module-ref-scalar AXC010-any '1,4' "Microsoft.FSharp.Core.FSharpRef\`1 (binding 'rows')."
run_case cache-module-mutable-scalar AXC010-any '1,12' "System.Int32 (binding 'counter')."
run_case cache-module-ref-option AXC010-any '1,4' "Microsoft.FSharp.Core.FSharpOption\`1 (binding 'counter')."
run_case cache-module-set-lookalike AXC010-any '3,14' "Cache-module-set-lookalike.Inner.Set\`1 (binding 'nodes')."
run_case cache-module-psg-bytearray AXC010-any '3,4' "Fidelity.PSG.NativeLiteral (binding 'shared')."
run_case cache-module-psg-int-clean clean
run_case cache-module-interface-upcast AXC010-any '5,4' "Cache-module-interface-upcast.ICounter (binding 'shared')."
run_case cache-module-derived-class-ref AXC010-any '6,4' "Cache-module-derived-class-ref.DerivedCounter (binding 'shared')."
run_case cache-module-mailbox AXC010-any '1,4' "Microsoft.FSharp.Control.FSharpMailboxProcessor\`1 (binding 'runs')."
run_case cache-module-event AXC010-any '1,4' "Microsoft.FSharp.Control.FSharpEvent\`1 (binding 'bus')."
run_case cache-module-factory-ref clean
run_case cache-module-record-closure-ref AXC010-any '2,4' "Cache-module-record-closure-ref.Factory (binding 'shared')."
run_case cache-module-object-expr-ref AXC010-any '2,4' "Cache-module-object-expr-ref.ICounter (binding 'shared')."
run_case cache-module-nested-wrap-ref AXC010-any '3,4' "Cache-module-nested-wrap-ref.Wrap\`1 (binding 'shared')."
run_case local-ref-accumulator clean
run_case lazy-isvaluecreated AXC010-state '2,12' 'Alex production code must not observe the creation state of a System.Lazy value: System.Lazy`1 (assembly netstandard).'
run_case lazy-lookalike clean
run_case ambient-scheduler AXC010-state '1,11' 'Alex production code must not hold ambient mutable state: System.Threading.Tasks.ConcurrentExclusiveSchedulerPair (assembly System.Runtime).'
run_case ambient-threadstatic AXC010-state '1,2 1,9' 'Alex production code must not hold ambient mutable state: System.ThreadStaticAttribute (assembly System.Runtime).'
run_case integer-literals clean
run_case integer-literal-open AXC002 '2,5'
run_case integer-literal-constructor AXC002 '2,8 3,15 4,17'
run_case integer-literal-parse AXC002 '2,8 2,24'
run_case integer-literal-custom AXC002 '2,20 2,36'
run_case generic-pure clean
run_case interpolation-pure clean
run_case interpolation-obj AXC004 '2,35' '1,20'
run_case physical-equality AXC006 '1,35'
run_case physical-equality-alias AXC006 '1,11'
run_case physical-equality-lookalike clean
run_case reflection-format AXC007 '1,30'
run_case reflection-format-plus AXC007 '1,30'
run_case reflection-format-interpolated AXC007 '1,22'
run_case exception-failwith AXC008 '1,19'
run_case exception-invalidarg AXC008 '1,25'
run_case exception-trywith AXC008 '1,13'
run_case nested-null AXC001 '9,24 10,23 14,21'
run_case nested-trywith AXC008 '15,28'
run_case nested-clean clean
run_case null AXC001 '1,20'
run_case null-pattern AXC001 '1,37'
run_case system-open AXC002 '1,5'
run_case system-type-open AXC002 '1,10'
run_case task AXC003 '1,13 1,27'
run_case task-alias AXC003 '2,13 2,30'
run_case task-lookalike clean
run_case abbreviation clean
run_case bcl-alias AXC002 '1,15 2,16'
run_case box AXC004 '1,12'
run_case box-alias AXC004 '1,12'
run_case box-qualified AXC004 '1,12'
run_case box-lookalike clean
run_case upcast AXC004 '1,13' '1,20'
run_case implicit-argument AXC004 '2,21' '1,20'
run_case implicit-field AXC004 '2,20' '1,20'
run_case implicit-list AXC004 '1,24 1,27' '1,12'
run_case object-identity AXC005 '1,17'
run_case obj-declaration AXC005 '1,13 2,21'
run_case obj-list-type AXC005 '1,12'
run_case obj-lookalike clean
run_case obj-primitives clean
run_case alias-Foreign AXC002 '2,10'
run_case alias-ObjectAlias AXC005 '2,10'
run_case alias-ObjectNominal AXC005 '2,10'
run_case alias-Chain AXC002 '2,10'
run_case alias-Builders AXC002 '2,10'
run_case alias-Handler AXC005 '2,10'
run_case alias-Pair AXC005 '2,10'
run_case alias-Both AXC002 '2,10' '2,10'
run_case alias-Boxed AXC005 '2,10'
run_case alias-Arr AXC002 '2,10'
run_case alias-Text clean
run_case alias-Names clean
run_case alias-Lookup clean
run_case alias-Function clean
run_case alias-PurePair clean
run_case alias-Optional clean
run_case alias-Generic clean
run_case alias-NestedObj AXC005 '2,10'
run_case alias-NestedForeign AXC002 '2,10'
run_case alias-Anonymous clean
run_case alias-AnonymousObj AXC005 '2,10'
run_case alias-Distance clean
run_case alias-Ints clean
run_case alias-UnitFunction clean
run_case alias-Nat clean
run_case alias-Resizable policy-pending
run_case alias-LazyValue policy-pending
run_case alias-Sequence policy-pending
run_case alias-LocalAlias clean
run_case alias-ExceptionType AXC002 '2,10'
run_case alias-BigInteger policy-pending
run_case alias-DecimalValue policy-pending
run_case file-reference AXC002 '1,21 1,11'
run_case file-stream AXC002 '1,18 1,54 1,44'
run_case stream-reader AXC002 '1,18 1,42'
run_case invalid type-error
mkdir -p "$scratch/Dialects/Core" "$scratch/Patterns" "$scratch/Traversal" "$scratch/XParsec" "$scratch/Elements" "$scratch/Witnesses"
printf '#r "%s"\nopen Fidelity.PSG\nlet bad (g: Revision) (id: NodeId) = g.Nodes.TryFind id\n' "$psg_dll" > "$scratch/Dialects/Core/axel-nodes.fsx"
printf '#r "%s"\nopen Fidelity.PSG\nlet bad (g: Revision) (id: NodeId) = Revision.tryNode id g\n' "$psg_dll" > "$scratch/Patterns/axel-trynode.fsx"
printf '#r "%s"\nopen Fidelity.PSG\nlet bad (r: Revision) = { r with Header = r.Header }\n' "$psg_dll" > "$scratch/Dialects/Core/axel-revision-with.fsx"
printf '#r "%s"\nopen Fidelity.PSG\nlet ok (g: Revision) (id: NodeId) = g.Nodes.TryFind id, Revision.tryNode id g\n' "$psg_dll" > "$scratch/Traversal/axel-trynode-ok.fsx"
printf '#r "%s"\nopen Fidelity.PSG\nlet ok (g: Revision) (id: NodeId) = g.Nodes.TryFind id, Revision.tryNode id g\n' "$psg_dll" > "$scratch/XParsec/axel-trynode-ok.fsx"
printf '#r "%s"\nopen Fidelity.PSG\nlet ok (g: Revision) (id: NodeId) = g.Nodes.TryFind id, Revision.tryNode id g\n' "$psg_dll" > "$scratch/Generation.fsx"
printf '#r "%s"\nopen Fidelity.PSG\nlet rec bad (kind: SemanticKind) = match kind with SemanticKind.Literal n -> n | SemanticKind.Binding _ -> bad kind\n' "$psg_dll" > "$scratch/Dialects/Core/axel-cata-kind.fsx"
printf '#r "%s"\nopen Fidelity.PSG\nlet outer (g: Revision) (id: NodeId) =\n  let rec bad i = match g.Nodes.TryFind i with Some _ -> bad i | None -> Result.Error "stop"\n  bad id\n' "$psg_dll" > "$scratch/Traversal/axel-cata-local-nodes.fsx"
printf '#r "%s"\nopen Fidelity.PSG\nlet rec exprOrigin (g: Revision) (id: NodeId) =\n  match Revision.tryNode id g with\n  | Some n -> match n.Kind with SemanticKind.Literal v -> Result.Ok v | SemanticKind.Binding _ -> exprOrigin g id\n  | None -> Result.Error "missing"\n' "$psg_dll" > "$scratch/Dialects/Core/axel-expr-origin.fsx"
printf '#r "%s"\n#r "%s"\nopen Fidelity.PSG\nopen Alex.Traversal.TransferTypes\nlet rec tryWitnesses (kind: SemanticKind) = match kind with SemanticKind.Literal n -> n | SemanticKind.Binding _ -> tryWitnesses kind\nlet ok (id: NodeId) (ssa: Alex.Dialects.Core.Types.SSA) (acc: MLIRAccumulator) =\n  MLIRAccumulator.bindNode id ssa "i64" acc\n  acc.SSATypes <- Map.empty\n' "$psg_dll" "$alex_dll" > "$scratch/Traversal/NanopassArchitecture.fsx"
printf '#r "%s"\nopen Fidelity.PSG\nlet ok (kind: SemanticKind) = match kind with SemanticKind.Literal n -> n | SemanticKind.Binding _ -> 0\n' "$psg_dll" > "$scratch/Dialects/Core/axel-nonrec-kind.fsx"
printf '#r "%s"\ntype Bad = Fidelity.PSG.SemanticNode\n' "$psg_dll" > "$scratch/Elements/axel-elem-node.fsx"
printf '#r "%s"\n#r "%s"\nlet bad s = Alex.Traversal.PSGZipper.focus s\n' "$psg_dll" "$alex_dll" > "$scratch/Elements/axel-elem-zipper.fsx"
printf '#r "%s"\n#r "%s"\nlet bad () = Alex.CodeGeneration.TypeMapping.mapInt ()\n' "$psg_dll" "$alex_dll" > "$scratch/Elements/axel-elem-typemapping.fsx"
printf '#r "%s"\n#r "%s"\nlet bad id = Alex.CodeGeneration.CallableSymbols.symbolFor id\n' "$psg_dll" "$alex_dll" > "$scratch/Elements/axel-elem-callablesymbols.fsx"
printf '#r "%s"\n#r "%s"\nlet bad (s: Alex.XParsec.PSGCombinators.PSGParserState) = s.Graph\n' "$psg_dll" "$alex_dll" > "$scratch/Elements/axel-elem-parserstate-graph.fsx"
printf '#r "%s"\n#r "%s"\nlet bad (s: Alex.XParsec.PSGCombinators.PSGParserState) = s.Zipper\n' "$psg_dll" "$alex_dll" > "$scratch/Elements/axel-elem-parserstate-zipper.fsx"
printf '#r "%s"\nopen Fidelity.PSG\nlet ok (a: BoundaryImport) (b: IntrinsicWriteImport) (c: SpatialModuleWitness) (d: BoundaryScalar) = a, b, c, d\n' "$psg_dll" > "$scratch/Elements/axel-elem-allowed.fsx"
printf '#r "%s"\nlet bad () = let mutable x = 0 in x <- 1; x\n' "$psg_dll" > "$scratch/Patterns/axel-mutable.fsx"
printf '#r "%s"\nlet bad () = let c = ref 0 in c.Value\n' "$psg_dll" > "$scratch/Dialects/axel-ref.fsx"
printf '#r "%s"\ntype R = { A: int; B: string }\nlet ok (xs: R list) = xs |> List.fold (fun s r -> s + r.A) 0\n' "$psg_dll" > "$scratch/Patterns/axel-pure-fold-ok.fsx"
printf '#r "%s"\nlet ok () = let mutable x = 0 in x <- 1; x\n' "$psg_dll" > "$scratch/Traversal/axel-mutable-ok.fsx"
printf '#r "%s"\nopen Fidelity.PSG\nlet bad (imp: BoundaryImport) = imp.DeclarationFacts.TryFind "x"\n' "$psg_dll" > "$scratch/Patterns/axel-facts-tryfind.fsx"
printf '#r "%s"\nopen Fidelity.PSG\nlet getFacts (imp: BoundaryImport) = imp.DeclarationFacts\nlet bad (imp: BoundaryImport) = (getFacts imp).TryFind "x"\n' "$psg_dll" > "$scratch/Patterns/axel-facts-helper.fsx"
printf '#r "%s"\nopen Fidelity.PSG\nlet bad (imp: BoundaryImport) = imp.DeclarationFacts |> Map.tryFind "x"\n' "$psg_dll" > "$scratch/Patterns/axel-facts-maptryfind.fsx"
printf '#r "%s"\nopen Fidelity.PSG\nlet bad (imp: BoundaryImport) = imp.DeclarationFacts["x"]\n' "$psg_dll" > "$scratch/Patterns/axel-facts-item.fsx"
printf '#r "%s"\nopen Fidelity.PSG\nlet bad (imp: BoundaryImport) = imp.DeclarationFacts.Values\n' "$psg_dll" > "$scratch/Patterns/axel-facts-values.fsx"
printf '#r "%s"\nopen Fidelity.PSG\nlet ok (imp: BoundaryImport) = imp.DeclarationFacts.ContainsKey "x" && Map.containsKey "y" imp.DeclarationFacts\n' "$psg_dll" > "$scratch/Patterns/axel-facts-contains-ok.fsx"
printf '#r "%s"\nopen Fidelity.PSG\nlet ok (imp: BoundaryImport) = imp.DeclarationFacts |> Map.containsKey "x"\n' "$psg_dll" > "$scratch/Patterns/axel-facts-pipe-contains-ok.fsx"
printf '#r "%s"\nopen Fidelity.PSG\nlet bad (imp: BoundaryImport) = let mutable facts = imp.DeclarationFacts in facts.ContainsKey "x"\n' "$psg_dll" > "$scratch/Patterns/axel-facts-mutable.fsx"
printf '#r "%s"\nopen Fidelity.PSG\nlet bad (g: Revision) (id: NodeId) (fb: SemanticNode) = Revision.tryNode id g |> Option.defaultValue fb\n' "$psg_dll" > "$scratch/Traversal/axel-fallback-defaultval.fsx"
printf '#r "%s"\nopen Fidelity.PSG\nlet bad (g: Revision) (id: NodeId) = let o = g.Codata.Escapes.TryFind id in Option.defaultWith (fun () -> 0) o\n' "$psg_dll" > "$scratch/Traversal/axel-fallback-defaultwith.fsx"
printf '#r "%s"\n#r "%s"\nopen Fidelity.PSG\nopen Alex.Traversal.TransferTypes\nlet bad id acc = MLIRAccumulator.recallNode id acc |> Option.orElse (Some ("x", 1))\n' "$psg_dll" "$alex_dll" > "$scratch/Traversal/axel-fallback-orelse.fsx"
printf '#r "%s"\nopen Fidelity.PSG\nlet bad (g: Revision) (id: NodeId) = defaultArg (g.Emission.Entries.TryFind id) "bad"\n' "$psg_dll" > "$scratch/Traversal/axel-fallback-defaultarg.fsx"
printf '#r "%s"\nopen Fidelity.PSG\nlet bad (g: Revision) (id: NodeId) = match Revision.tryNode id g with Some n -> n.Kind | None -> SemanticKind.Literal 0\n' "$psg_dll" > "$scratch/Traversal/axel-fallback-match-val.fsx"
printf '#r "%s"\nopen Fidelity.PSG\nlet bad (g: Revision) (id: NodeId) = match g.Codata.Escapes.TryFind id with Some _ -> true | None -> true\n' "$psg_dll" > "$scratch/Traversal/axel-fallback-match-true.fsx"
printf '#r "%s"\nopen Fidelity.PSG\nlet bad (g: Revision) (id: NodeId) = g.Codata.Escapes.TryFind id |> Option.map (fun _ -> true) |> Option.defaultValue false\n' "$psg_dll" > "$scratch/Traversal/axel-fallback-defaultval-false.fsx"
printf '#r "%s"\nopen Fidelity.PSG\nlet bad (g: Revision) (id: NodeId) = g.Codata.Escapes.TryFind id |> Option.forall (fun x -> x > 0)\n' "$psg_dll" > "$scratch/Traversal/axel-fallback-forall.fsx"
printf '#r "%s"\nopen Fidelity.PSG\nlet bad (g: Revision) (id: NodeId) = let r = g.Emission.Entries.TryFind id in if r.IsSome then r.Value else "bad"\n' "$psg_dll" > "$scratch/Traversal/axel-fallback-issome.fsx"
printf '#r "%s"\nopen Fidelity.PSG\nlet bad (g: Revision) (id: NodeId) (fb: SemanticNode) = let mutable opt = Revision.tryNode id g in opt |> Option.defaultValue fb\n' "$psg_dll" > "$scratch/Traversal/axel-fallback-mutable.fsx"
printf '#r "%s"\n#r "%s"\nopen Fidelity.PSG\nopen Alex.Traversal.TransferTypes\nlet bad (g: Revision) (id: NodeId) = match Revision.tryNode id g with Some _ -> WitnessOutput.error "ok" | None -> WitnessOutput.skip\n' "$psg_dll" "$alex_dll" > "$scratch/Traversal/axel-fallback-skip.fsx"
printf '#r "%s"\nopen Fidelity.PSG\nlet bad (g: Revision) (id: NodeId) (fb: bool) = match g.Codata.Escapes.TryFind id with Some x -> x > 0 | None -> fb\n' "$psg_dll" > "$scratch/Traversal/axel-fallback-match-bool-var.fsx"
printf '#r "%s"\nopen Fidelity.PSG\nlet bad (g: Revision) (id: NodeId) = match g.Codata.Escapes.TryFind id with Some x -> x > 0 | None -> not false\n' "$psg_dll" > "$scratch/Traversal/axel-fallback-not-false.fsx"
printf '#r "%s"\n#r "%s"\nopen Fidelity.PSG\nopen Alex.Traversal.TransferTypes\nlet bad (g: Revision) (id: NodeId) = match Revision.tryNode id g with Some _ -> (1, WitnessOutput.skip) | None -> (0, WitnessOutput.error "x")\n' "$psg_dll" "$alex_dll" > "$scratch/Traversal/axel-fallback-tuple-refusal.fsx"
printf '#r "%s"\n#r "%s"\nopen Fidelity.PSG\nopen Alex.Traversal.TransferTypes\nlet bad (g: Revision) (id: NodeId) = match g.Codata.Escapes.TryFind id with Some x -> x | None -> WitnessOutput.error "x" |> ignore; 0\n' "$psg_dll" "$alex_dll" > "$scratch/Traversal/axel-fallback-seq-refusal.fsx"
printf '#r "%s"\nopen Fidelity.PSG\nlet bad (g: Revision) (id: NodeId) (fb: SemanticNode) = Revision.tryNode id g |> Option.map Result.Ok |> Option.orElse (Some (Result.Ok fb)) |> Option.defaultWith (fun () -> Result.Error "x")\n' "$psg_dll" > "$scratch/Traversal/axel-fallback-orelse-chained.fsx"
printf '#r "%s"\nopen Fidelity.PSG\nlet bad (g: Revision) (id: NodeId) = match g.Codata.Escapes.TryFind id with Some x -> x | None -> failwith "missing"\n' "$psg_dll" > "$scratch/Traversal/axel-fallback-failwith.fsx"
printf '#r "%s"\n#r "%s"\nopen Fidelity.PSG\nopen Alex.Traversal.TransferTypes\nlet bad (g: Revision) (id: NodeId) (acc: MLIRAccumulator) = match g.Codata.Escapes.TryFind id with Some _ -> () | None -> MLIRAccumulator.addError (Diagnostic.error None None None "x") acc\n' "$psg_dll" "$alex_dll" > "$scratch/Traversal/axel-fallback-adderror.fsx"
printf '#r "%s"\n#r "%s"\nopen Fidelity.PSG\nopen Alex.Traversal.TransferTypes\nlet bad (g: Revision) (id: NodeId) (acc: MLIRAccumulator) = match g.Codata.Escapes.TryFind id with Some x -> x | None -> MLIRAccumulator.addError (Diagnostic.error None None None "x") acc; 0\n' "$psg_dll" "$alex_dll" > "$scratch/Traversal/axel-fallback-seq-adderror.fsx"
printf '#r "%s"\nopen Fidelity.PSG\nlet bad (g: Revision) (id: NodeId) = match g.Codata.Escapes.TryFind id with Some x -> Result.Ok x | None -> match Revision.tryNode id g with Some _ -> Result.Ok 0 | None -> Result.Error "missing"\n' "$psg_dll" > "$scratch/Traversal/axel-fallback-nested-some.fsx"
printf '#r "%s"\nopen Fidelity.PSG\nlet bad (g: Revision) (id: NodeId) (localOpt: SemanticNode option) = localOpt |> Option.orElse (Revision.tryNode id g)\n' "$psg_dll" > "$scratch/Traversal/axel-fallback-orelse-reverse.fsx"
printf '#r "%s"\nopen Fidelity.PSG\nlet bad (g: Revision) (id: NodeId) = g.Codata.Escapes.TryFind id |> Option.toList\n' "$psg_dll" > "$scratch/Traversal/axel-fallback-tolist.fsx"
printf '#r "%s"\nopen Fidelity.PSG\nlet bad (g: Revision) (id: NodeId) = g.Codata.Escapes.TryFind id |> Option.toArray\n' "$psg_dll" > "$scratch/Traversal/axel-fallback-toarray.fsx"
printf '#r "%s"\nopen Fidelity.PSG\nlet bad (g: Revision) (id: NodeId) = g.Codata.Escapes.TryFind id |> Option.fold (fun _ x -> x) 0\n' "$psg_dll" > "$scratch/Traversal/axel-fallback-fold.fsx"
printf '#r "%s"\nopen Fidelity.PSG\nlet bad (g: Revision) (id: NodeId) = g.Codata.Escapes.TryFind id |> Option.count\n' "$psg_dll" > "$scratch/Traversal/axel-fallback-count.fsx"
printf '#r "%s"\nopen Fidelity.PSG\nlet bad (g: Revision) (id: NodeId) = g.Codata.Escapes.TryFind id |> Option.iter ignore\n' "$psg_dll" > "$scratch/Traversal/axel-fallback-iter.fsx"
printf '#r "%s"\nopen Fidelity.PSG\nlet bad (g: Revision) (id: NodeId) = g.Emission.Entries.TryFind id |> Option.toObj\n' "$psg_dll" > "$scratch/Traversal/axel-fallback-toobj.fsx"
printf '#r "%s"\nopen Fidelity.PSG\nlet tryAt (g: Revision) (id: NodeId) = g.Codata.Escapes.TryFind id\nlet bad (g: Revision) (id: NodeId) = tryAt g id |> Option.defaultValue 0\n' "$psg_dll" > "$scratch/Traversal/axel-fallback-helper-ret.fsx"
printf '#r "%s"\nopen Fidelity.PSG\nlet orZero opt = opt |> Option.defaultValue 0\nlet bad (g: Revision) (id: NodeId) = orZero (g.Codata.Escapes.TryFind id)\n' "$psg_dll" > "$scratch/Traversal/axel-fallback-helper-param.fsx"
printf '#r "%s"\n#r "%s"\nopen Fidelity.PSG\nopen Alex.Traversal.TransferTypes\nlet cleanDomainOptional (alignmentOpt: string option) = alignmentOpt |> Option.defaultValue ""\nlet ok (g: Revision) (id: NodeId) (acc: MLIRAccumulator) (optArg: string option) =\n  let _ = cleanDomainOptional optArg\n  let _ = Revision.tryNode id g |> Option.map Result.Ok |> Option.defaultWith (fun () -> Result.Error "missing")\n  let _ = match g.Codata.Escapes.TryFind id with Some n -> Result.Ok n | None -> Result.Error "missing"\n  let _ = match MLIRAccumulator.recallNode id acc with Some _ -> WitnessOutput.error "ok" | None -> WitnessOutput.errorDiag (Diagnostic.error "missing")\n  let _ = match g.Codata.Escapes.TryFind id with Some x -> x > 0 | None -> false\n  let _ = match g.Codata.Escapes.TryFind id with Some _ -> (g.Emission.Entries.TryFind id |> Option.exists (fun s -> s = "ok")) | None -> (g.Emission.Entries.TryFind id |> Option.isSome)\n  Option.isSome (Revision.tryNode id g)\n' "$psg_dll" "$alex_dll" > "$scratch/Traversal/axel-fallback-ok.fsx"
printf '#r "%s"\n#r "%s"\nopen Fidelity.PSG\nopen Alex.Traversal.TransferTypes\nlet bad (id: NodeId) (ssa: Alex.Dialects.Core.Types.SSA) (acc: MLIRAccumulator) = MLIRAccumulator.bindNode id ssa "i64" acc\n' "$psg_dll" "$alex_dll" > "$scratch/Patterns/axel-bind-node.fsx"
printf '#r "%s"\n#r "%s"\nopen Fidelity.PSG\nopen Alex.Traversal.TransferTypes\nlet bad (id: NodeId) (ssa: Alex.Dialects.Core.Types.SSA) = MLIRAccumulator.bindNode id ssa "i64"\n' "$psg_dll" "$alex_dll" > "$scratch/Patterns/axel-bind-node-partial.fsx"
printf '#r "%s"\n#r "%s"\nopen Alex.Traversal.TransferTypes\nlet bad (acc: MLIRAccumulator) = acc.SSATypes <- Map.empty\n' "$psg_dll" "$alex_dll" > "$scratch/Patterns/axel-accumulator-assign.fsx"
printf '#r "%s"\n#r "%s"\nlet bad (acc: Alex.Traversal.TransferTypes.MLIRAccumulator) = acc.SSATypes <- Map.empty\n' "$psg_dll" "$alex_dll" > "$scratch/Elements/axel-accumulator-assign.fsx"
printf '#r "%s"\n#r "%s"\nopen Fidelity.PSG\nopen Alex.Traversal.TransferTypes\nlet bad (id: NodeId) (ssa: Alex.Dialects.Core.Types.SSA) (acc: MLIRAccumulator) = MLIRAccumulator.bindNode id ssa "i64" acc\n' "$psg_dll" "$alex_dll" > "$scratch/Witnesses/axel-bind-node.fsx"
printf '#r "%s"\n#r "%s"\nopen Fidelity.PSG\nopen Alex.Traversal.TransferTypes\nlet bad (id: NodeId) (ssa: Alex.Dialects.Core.Types.SSA) (acc: MLIRAccumulator) =\n  MLIRAccumulator.bindNode id ssa "i64" acc\n  acc.SSATypes <- Map.empty\n' "$psg_dll" "$alex_dll" > "$scratch/Traversal/axel-bind-node.fsx"
printf '#r "%s"\n#r "%s"\nopen Fidelity.PSG\nopen Alex.Traversal.TransferTypes\nlet ok (id: NodeId) (ssa: Alex.Dialects.Core.Types.SSA) (acc: MLIRAccumulator) =\n  MLIRAccumulator.bindNode id ssa "i64" acc\n  MLIRAccumulator.forgetVoid id acc\n  MLIRAccumulator.completeVoid id 0 acc\n  MLIRAccumulator.restoreOperands Map.empty acc\n  MLIRAccumulator.registerSSAType ssa "i64" acc\n  acc.SSATypes <- Map.empty\n' "$psg_dll" "$alex_dll" > "$scratch/Traversal/TransferTypes.fsx"
printf '#r "%s"\n#r "%s"\nopen Fidelity.PSG\nopen Alex.Traversal.TransferTypes\nlet bad (id: NodeId) (ssa: Alex.Dialects.Core.Types.SSA) (acc: MLIRAccumulator) =\n  MLIRAccumulator.forgetVoid id acc\n  MLIRAccumulator.completeVoid id 0 acc\n  MLIRAccumulator.restoreOperands Map.empty acc\n  MLIRAccumulator.registerSSAType ssa "i64" acc\n' "$psg_dll" "$alex_dll" > "$scratch/Patterns/axel-accumulator-helpers.fsx"
printf '#r "%s"\n#r "%s"\nopen Fidelity.PSG\nopen Alex.Traversal.TransferTypes\nlet bad (id: NodeId) (ssa: Alex.Dialects.Core.Types.SSA) (acc: MLIRAccumulator) = MLIRAccumulator.bindNode id ssa "i64" acc\n' "$psg_dll" "$alex_dll" > "$scratch/Dialects/axel-bind-node.fsx"
printf '#r "%s"\nlet bad () = let mutable x = 0 in x <- 1; x\n' "$psg_dll" > "$scratch/Witnesses/axel-mutable-witness.fsx"
printf '#r "%s"\nlet bad () = let c = ref 0 in c.Value\n' "$psg_dll" > "$scratch/Witnesses/axel-ref-witness.fsx"
printf '#r "%s"\n#r "%s"\nopen Fidelity.PSG\nlet bad (id: NodeId) = Alex.Traversal.Values.value id 0, Alex.Traversal.Values.values id, Alex.Traversal.Values.continuationValue id 0 0\n' "$psg_dll" "$alex_dll" > "$scratch/Patterns/axel-values-direct.fsx"
printf '#r "%s"\n#r "%s"\nopen Fidelity.PSG\nlet bad (ids: NodeId list) = ids |> List.map Alex.Traversal.Values.values\n' "$psg_dll" "$alex_dll" > "$scratch/Patterns/axel-values-first-class.fsx"
printf '#r "%s"\n#r "%s"\nopen Fidelity.PSG\nlet bad (id: NodeId) = Alex.Traversal.Values.value id 0\n' "$psg_dll" "$alex_dll" > "$scratch/Traversal/axel-values-direct.fsx"
printf '#r "%s"\n#r "%s"\nopen Alex.Dialects.Core.Types\nlet bad () = SSA.V (1, 0), SSA.Arg 0\n' "$psg_dll" "$alex_dll" > "$scratch/Patterns/axel-ssa-union.fsx"
printf '#r "%s"\n#r "%s"\nopen Fidelity.PSG\nopen Alex.Dialects.Core.Types\nlet ok (id: NodeId) = SSA.V (1, 0), SSA.Arg 0, Alex.Traversal.Values.value id 0, Alex.Traversal.Values.prologueValue id 0, Alex.Traversal.Values.resultOf id, Alex.Traversal.Values.undefined\n' "$psg_dll" "$alex_dll" > "$scratch/Traversal/Values.fsx"
printf '#r "%s"\n#r "%s"\nopen Fidelity.PSG\nlet ok (id: NodeId) = Alex.Traversal.Values.value id 0, Alex.Traversal.Values.values id, Alex.Traversal.Values.continuationValue id 0 0, Alex.Traversal.Values.valuesOf id, Alex.Traversal.Values.resultOf id\n' "$psg_dll" "$alex_dll" > "$scratch/XParsec/PSGCombinators.fsx"
printf '#r "%s"\n#r "%s"\nopen Fidelity.PSG\nopen Alex.Traversal\nlet bad (id: NodeId) =\n  [ Values.meetValue id 0\n    Values.returnMeetValue id\n    Values.unitReturnValue id\n    Values.callableCode id\n    Values.callableAlternative id 0\n    Values.aggregateComponent id id 0 0\n    Values.arrayElementIndex id 0\n    Values.prologueValue id 0\n    Values.hardwareValue id 0\n    Values.solverValue 0\n    Values.undefined ],\n  Values.valuesOf id, Values.resultOf id\n' "$psg_dll" "$alex_dll" > "$scratch/Patterns/axel-values-members.fsx"
printf '#r "%s"\n#r "%s"\nopen Fidelity.PSG\nlet bad (n: SemanticNode) = Alex.Traversal.NanopassArchitecture.visitAllNodes ignore n\n' "$psg_dll" "$alex_dll" > "$scratch/Patterns/axel-visit-all.fsx"
printf '#r "%s"\n#r "%s"\nlet bad (depth: int) = Alex.Traversal.ScopeContext.exitScope (Alex.Traversal.ScopeContext.enterScope depth)\n' "$psg_dll" "$alex_dll" > "$scratch/Patterns/axel-scope-transition.fsx"
printf '#r "%s"\n#r "%s"\nopen Alex.Traversal.ScopeContext\nlet bad (ops: string list) =\n  let child = ScopeContext.createChild (ScopeContext.root ()) BlockLevel\n  ScopeContext.addOps ops (ScopeContext.addOp "op" child)\n' "$psg_dll" "$alex_dll" > "$scratch/Patterns/axel-scope-context.fsx"
printf '#r "%s"\n#r "%s"\nopen Alex.Traversal.ScopeContext\nlet bad (parent: ScopeContext) = ScopeContext.createChild parent BlockLevel\n' "$psg_dll" "$alex_dll" > "$scratch/Witnesses/axel-scope-context.fsx"
printf '#r "%s"\n#r "%s"\nlet bad (obligations: string list) = Alex.Traversal.SMTTransfer.operations obligations, Alex.Traversal.SMTTransfer.transfer obligations\n' "$psg_dll" "$alex_dll" > "$scratch/Witnesses/axel-smt-transfer.fsx"
printf '#r "%s"\n#r "%s"\nopen Fidelity.PSG\nlet bad (n: SemanticNode) = Alex.Traversal.NanopassArchitecture.visitAllNodes ignore n\n' "$psg_dll" "$alex_dll" > "$scratch/Witnesses/axel-visit-all.fsx"
printf '#r "%s"\n#r "%s"\nopen Fidelity.PSG\nlet ok (n: SemanticNode) (depth: int) (obligations: string list) =\n  Alex.Traversal.NanopassArchitecture.visitAllNodes ignore n\n  Alex.Traversal.ScopeContext.exitScope (Alex.Traversal.ScopeContext.enterScope depth), Alex.Traversal.SMTTransfer.operations obligations, Alex.Traversal.SMTTransfer.transfer obligations, Alex.Traversal.ScopeContext.ScopeContext.addOps obligations (Alex.Traversal.ScopeContext.ScopeContext.root ())\n' "$psg_dll" "$alex_dll" > "$scratch/Traversal/axel-visit-all-ok.fsx"
printf '#r "%s"\n#r "%s"\nopen Fidelity.PSG\nlet ok (id: NodeId) = Alex.XParsec.PSGCombinators.getNodeSSA id, Alex.XParsec.PSGCombinators.getNodeSSAs id\n' "$psg_dll" "$alex_dll" > "$scratch/Patterns/axel-clean-getnodessa.fsx"
run_case Dialects/Core/axel-nodes AXA003-fn '3,37'
run_case Patterns/axel-trynode AXA003-fn '3,37'
run_case Dialects/Core/axel-revision-with AXA001 '3,24'
run_case Traversal/axel-trynode-ok clean
run_case XParsec/axel-trynode-ok clean
run_case Generation clean
run_case Dialects/Core/axel-cata-kind AXA004-fn '3,8'
run_case Dialects/Core/axel-expr-origin AXA003+AXA004 '4,8:AXA003 3,8:AXA004'
run_case Traversal/axel-cata-local-nodes AXA004-outer-bad '4,10'
run_case Traversal/NanopassArchitecture clean
run_case Dialects/Core/axel-nonrec-kind clean
run_case Elements/axel-elem-node AXA005-elem '2,11'
run_case Elements/axel-elem-zipper AXA005-elem '3,27 3,12 3,4'
run_case Elements/axel-elem-typemapping AXA005-elem '3,33 3,13'
run_case Elements/axel-elem-callablesymbols AXA005-elem '3,8 3,33 3,13 3,59 3,4'
run_case Elements/axel-elem-parserstate-graph AXA005-elem '3,58 3,4'
run_case Elements/axel-elem-parserstate-zipper AXA005-elem '3,58'
run_case Elements/axel-elem-allowed clean
run_case Patterns/axel-mutable AXA005-mutable-x '2,25'
run_case Dialects/axel-ref AXA005-ref '2,21'
run_case Patterns/axel-pure-fold-ok clean
run_case Traversal/axel-mutable-ok clean
run_case Patterns/axel-facts-tryfind AXA006 '3,32'
run_case Patterns/axel-facts-helper AXA006 '4,32'
run_case Patterns/axel-facts-maptryfind AXA006 '3,32 3,56'
run_case Patterns/axel-facts-item AXA006 '3,32'
run_case Patterns/axel-facts-values AXA006 '3,32'
run_case Patterns/axel-facts-contains-ok clean
run_case Patterns/axel-facts-pipe-contains-ok clean
run_case Patterns/axel-facts-mutable AXA005+AXA000-facts
run_case Traversal/axel-fallback-defaultval AXA007-fn '3,81'
run_case Traversal/axel-fallback-defaultwith AXA007-fn '3,76'
run_case Traversal/axel-fallback-orelse AXA007-fn '5,54'
run_case Traversal/axel-fallback-defaultarg AXA007-fn '3,37'
run_case Traversal/axel-fallback-match-val AXA007-fn '3,97'
run_case Traversal/axel-fallback-match-true AXA007-fn '3,101'
run_case Traversal/axel-fallback-defaultval-false AXA007-fn '3,98'
run_case Traversal/axel-fallback-forall AXA007-fn '3,68'
run_case Traversal/axel-fallback-issome AXA007-fn '3,108'
run_case Traversal/axel-fallback-mutable AXA000-mutable-opt '3,106'
run_case Traversal/axel-fallback-skip AXA007-fn '5,115'
run_case Traversal/axel-fallback-match-bool-var AXA007-fn '3,113'
run_case Traversal/axel-fallback-not-false AXA007-fn '3,102'
run_case Traversal/axel-fallback-tuple-refusal AXA007-fn '5,115'
run_case Traversal/axel-fallback-seq-refusal AXA007-fn '5,98'
run_case Traversal/axel-fallback-orelse-chained AXA007-fn '3,105'
run_case Traversal/axel-fallback-failwith AXA007-fn '3,98'
run_case Traversal/axel-fallback-adderror AXA007-fn '5,122'
run_case Traversal/axel-fallback-seq-adderror AXA007-fn '5,121'
run_case Traversal/axel-fallback-nested-some AXA007-fn '3,114'
run_case Traversal/axel-fallback-orelse-reverse AXA007-fn '3,81'
run_case Traversal/axel-fallback-tolist AXA007-fn '3,68'
run_case Traversal/axel-fallback-toarray AXA007-fn '3,68'
run_case Traversal/axel-fallback-fold AXA007-fn '3,68'
run_case Traversal/axel-fallback-count AXA007-fn '3,68'
run_case Traversal/axel-fallback-iter AXA007-fn '3,68'
run_case Traversal/axel-fallback-toobj AXA007-fn '3,70'
run_case Traversal/axel-fallback-helper-ret AXA007-fn '4,51'
run_case Traversal/axel-fallback-helper-param AXA007-fn '4,37'
run_case Traversal/axel-fallback-ok clean
run_case Patterns/axel-bind-node AXA008-fn '5,82'
run_case Patterns/axel-bind-node-partial AXA008-fn '5,59'
run_case Patterns/axel-accumulator-assign AXA008-fn '4,33'
run_case Elements/axel-accumulator-assign AXA008-fn '3,62'
run_case Witnesses/axel-bind-node AXA008-fn '5,82'
run_case Traversal/axel-bind-node AXA008-fn '6,2 7,2'
run_case Traversal/TransferTypes clean
run_case Patterns/axel-accumulator-helpers AXA008-fn '6,2 7,2 8,2 9,2'
run_case Dialects/axel-bind-node AXA008-fn '5,82'
run_case Witnesses/axel-mutable-witness AXA005-witness '2,25'
run_case Witnesses/axel-ref-witness AXA005-witness '2,21'
run_case Patterns/axel-values-direct AXA009-values '4,23 4,57 4,90'
run_case Patterns/axel-values-first-class AXA009-values '4,45'
run_case Traversal/axel-values-direct AXA009-values '4,23'
run_case Patterns/axel-ssa-union AXA009-construction '4,13 4,27'
run_case Traversal/Values clean
run_case XParsec/PSGCombinators clean
run_case Patterns/axel-values-members AXA009-values '6,4 7,4 8,4 9,4 10,4 11,4 12,4 13,4 14,4 15,4 16,4 17,2 17,22'
run_case Patterns/axel-visit-all AXA010-fn '4,28'
run_case Patterns/axel-scope-transition AXA010-fn '3,23 3,62'
run_case Patterns/axel-scope-context AXA010-fn '5,14 5,40 6,2 6,27'
run_case Witnesses/axel-scope-context AXA010-fn '4,33'
run_case Witnesses/axel-smt-transfer AXA010-smt '3,37 3,88'
run_case Witnesses/axel-visit-all AXA010-fn '4,28'
run_case Traversal/axel-visit-all-ok clean
run_case Patterns/axel-clean-getnodessa clean
run_case src/Alex/Controls/Axc011Immutable clean
run_case src/Alex/Controls/Axc011Mutable AXC011 '2,2' "Alex must not introduce legacy mutable state: let mutable in 'Controls/Axc011Mutable.fsx' is outside the checked-in ratchet."
run_case src/Alex/Controls/Axc011ResizeArray AXC011+AXC002 '2,13 3,25' "Alex must not introduce legacy mutable state: System.Collections.Generic.List\`1 in 'Controls/Axc011ResizeArray.fsx' is outside the checked-in ratchet."
run_case src/Alex/Controls/Axc011Dictionary AXC011+AXC002 '1,14' "Alex must not introduce legacy mutable state: System.Collections.Generic.Dictionary\`2 in 'Controls/Axc011Dictionary.fsx' is outside the checked-in ratchet."
run_case src/Alex/Controls/Axc011HashSet AXC011+AXC002 '1,14' "Alex must not introduce legacy mutable state: System.Collections.Generic.HashSet\`1 in 'Controls/Axc011HashSet.fsx' is outside the checked-in ratchet."
run_case src/Alex/Controls/Axc011Queue AXC011+AXC002 '1,14' "Alex must not introduce legacy mutable state: System.Collections.Generic.Queue\`1 in 'Controls/Axc011Queue.fsx' is outside the checked-in ratchet."
run_case src/Alex/Controls/Axc011Stack AXC011+AXC002 '1,14' "Alex must not introduce legacy mutable state: System.Collections.Generic.Stack\`1 in 'Controls/Axc011Stack.fsx' is outside the checked-in ratchet."
run_case src/Alex/Controls/Axc011QueueNonGeneric AXC011+AXC002 '1,14' "Alex must not introduce legacy mutable state: System.Collections.Queue in 'Controls/Axc011QueueNonGeneric.fsx' is outside the checked-in ratchet."
run_case src/Alex/Controls/Axc011StackNonGeneric AXC011+AXC002 '1,14' "Alex must not introduce legacy mutable state: System.Collections.Stack in 'Controls/Axc011StackNonGeneric.fsx' is outside the checked-in ratchet."
run_case src/Alex/Controls/Axc011Pinned clean
run_case src/Alex/Controls/Axc011Growth AXC011 '4,2' "Alex must not grow the legacy mutable ratchet: let mutable in 'Controls/Axc011Growth.fsx' has 3 sites, exceeding the checked-in cap 2."
run_case src/Alex/Controls/Axc011Shrink1 AXC011 '1,0' "Alex must shrink the legacy mutable ratchet: let mutable in 'Controls/Axc011Shrink1.fsx' pins 2 site(s) but actual count is 1; tighten downward."
run_case src/Alex/Controls/Axc011Shrink0 AXC011 '1,0' "Alex must shrink the legacy mutable ratchet: let mutable in 'Controls/Axc011Shrink0.fsx' pins 2 site(s) but actual count is 0; tighten downward."
run_case src/Alex/Controls/Axc011SevenSites AXC011 '1,15 2,31 4,27 5,17 7,17 8,13 10,18 10,41 11,19 12,18 14,23' "Alex must not introduce legacy mutable state: let mutable in 'Controls/Axc011SevenSites.fsx' is outside the checked-in ratchet."
run_case src/Alex/Controls/Axc011ExceptionMember AXC011 '2,23' "Alex must not introduce legacy mutable state: let mutable in 'Controls/Axc011ExceptionMember.fsx' is outside the checked-in ratchet."
run_case src/Alex/Controls/Axc011ExceptionMemberClean clean
run_case src/Alex/Controls/Axc011ResizeArrayAnnotation AXC011 '1,15' "Alex must not introduce legacy mutable state: System.Collections.Generic.List\`1 in 'Controls/Axc011ResizeArrayAnnotation.fsx' is outside the checked-in ratchet."
run_case src/Alex/Controls/Axc011DictionaryLookalike AXC002 '1,10'
run_case src/Alex/Controls/Axc011ClassAndObjectExpr AXC011 '3,2 5,52' "Alex must not introduce legacy mutable state: let mutable in 'Controls/Axc011ClassAndObjectExpr.fsx' is outside the checked-in ratchet."
[[ $executed -gt 0 ]] || { printf 'No truth case matched.\n' >&2; exit 1; }
if [[ -z ${ALEX_ANALYZER_ONLY:-} ]]; then
  [[ $executed -eq 316 ]] || { printf 'Expected 316 registered cases, ran %s.\n' "$executed" >&2; exit 1; }
  printf '{"executed":%s,"cases":[' "$executed" > "$scratch/truth.json"
  separator=''
  for case_name in "${cases[@]}"; do printf '%s"%s"' "$separator" "$case_name" >> "$scratch/truth.json"; separator=','; done
  printf '],"known_miss":[' >> "$scratch/truth.json"
  separator=''
  for case_name in "${known_misses[@]}"; do printf '%s"%s"' "$separator" "$case_name" >> "$scratch/truth.json"; separator=','; done
  printf '],"policy_pending":[' >> "$scratch/truth.json"
  separator=''
  for case_name in "${policy_pending[@]}"; do printf '%s"%s"' "$separator" "$case_name" >> "$scratch/truth.json"; separator=','; done
  printf '],"sdk":"%s","analyzer_cli":"0.41.0"}\n' "$(dotnet --version)" >> "$scratch/truth.json"
  sha256sum "$analyzers/Alex.Analyzers.dll" "$tool_dir/Analyzer.fs" "$tool_dir/tests/run.sh" "$tool_dir/.config/dotnet-tools.json" "$psg_dll" "$impostor_dll" "$alex_dll" "$stale_dll" "$tool_dir/tests/ContractFixture/Contract.fs" "$tool_dir/tests/ContractFixture/ContractFixture.fsproj" "$tool_dir/tests/ImpostorFixture/ImpostorFixture.fsproj" "$tool_dir/tests/AlexFixture/Ensure.fs" "$tool_dir/tests/AlexFixture/AlexFixture.fsproj" "$tool_dir/tests/AlexFixture/packages.lock.json" "$tool_dir/tests/StaleContract/Contract.fs" "$tool_dir/tests/StaleContract/StaleContract.fsproj" "$tool_dir/tests/InProject/InProject.fsproj" "$tool_dir/tests/InProject/Ensure.fs" "$tool_dir/tests/InProject/Cases.fs" "$tool_dir/tests/InProject/Dialects/Cases.fs" "$tool_dir/tests/InProject/Elements/Cases.fs" "$tool_dir/tests/InProject/Elements/CleanCases.fs" "$tool_dir/tests/InProject/Patterns/Cases.fs" "$tool_dir/tests/InProject/Witnesses/Cases.fs" "$tool_dir/tests/InProject/Traversal/Values.fs" "$tool_dir/tests/project-control.sh" "$repo_dir/artifacts/alex-analyzers-tests/inproject-control/truth.sha256" "$tool_dir/analyze-alex.sh" "$tool_dir/check-project.sh" "$tool_dir/ProjectInputs.fsx" "$tool_dir/VerifyProjectLog.fsx" "$tool_dir/Alex.Analyzers.fsproj" "$tool_dir/Directory.Packages.props" "$tool_dir/packages.lock.json" "$tool_dir/NuGet.Config" "$scratch/truth.json" > "$scratch/truth.sha256"
  sha256sum "$alias_dll" "$tool_dir/tests/AliasFixture/Aliases.fs" "$tool_dir/tests/AliasFixture/AliasFixture.fsproj" "$tool_dir/tests/AliasFixture/packages.lock.json" "$tool_dir/tests/DependencyControls.fsx" >> "$scratch/truth.sha256"
  cp "$scratch/truth.sha256" "${ALEX_ANALYZER_TRUTH_RECEIPT_OUT:-$repo_dir/artifacts/alex-analyzers-tests/latest-truth.sha256}"
  grep -Fv '/truth.json' "$scratch/truth.sha256" > "$scratch/truth-missing-json.sha256"
  tamper_status=0
  ALEX_ANALYZER_TRUTH_RECEIPT="$scratch/truth-missing-json.sha256" bash "$tool_dir/check-project.sh" alex-boundary > "$scratch/truth-missing-json.log" 2>&1 || tamper_status=$?
  [[ $tamper_status -ne 0 ]] && grep -Fxq 'Truth receipt does not bind truth.json.' "$scratch/truth-missing-json.log" || { printf 'check-project.sh failed to refuse truth receipt without truth.json.\n' >&2; exit 1; }
  printf 'PASS truth-receipt-missing-json refusal\n'
  printf 'Truth receipt: %s\n' "$scratch/truth.sha256"
fi
printf 'Evidence: %s\n' "$scratch"
