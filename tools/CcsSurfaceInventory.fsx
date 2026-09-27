#r "nuget: FSharp.Compiler.Service, 43.10.101"
open System
open System.IO
open FSharp.Compiler.CodeAnalysis
open FSharp.Compiler.Symbols

let here = __SOURCE_DIRECTORY__
let bin = "/home/hhh/repos/Composer/src/bin/Debug/net10.0"
let fixRef (a: string) =
    if a.StartsWith "-r:" && a.Contains "/scratchpad/" then "-r:" + Path.Combine(bin, Path.GetFileName(a.Substring 3))
    else a
let absSource (a: string) =
    if a.EndsWith ".fs" && not (a.StartsWith "-") && not (Path.IsPathRooted a) then Path.Combine("/home/hhh/repos/Composer/src", a) else a
let args =
    File.ReadAllLines(Path.Combine(here, "fsc-args.txt"))
    |> Array.filter (fun a -> a <> "" && not (a.StartsWith "-o:"))
    |> Array.map (fixRef >> absSource)
let checker = FSharpChecker.Create()
let options = checker.GetProjectOptionsFromCommandLineArgs("/home/hhh/repos/Composer/src/Composer.fsproj", args)
let results = checker.ParseAndCheckProject options |> Async.RunSynchronously
let errors = results.Diagnostics |> Array.filter (fun d -> d.Severity = FSharp.Compiler.Diagnostics.FSharpDiagnosticSeverity.Error)
eprintfn "diagnostics: %d errors of %d" errors.Length results.Diagnostics.Length
errors |> Array.truncate 5 |> Array.iter (fun d -> eprintfn "%s(%d): %s" d.FileName d.StartLine d.Message)

let kindOf (s: FSharpSymbol) =
    match s with
    | :? FSharpUnionCase -> "case"
    | :? FSharpField -> "field"
    | :? FSharpEntity as e ->
        if e.IsFSharpModule then "module" elif e.IsNamespace then "namespace"
        elif e.IsFSharpUnion then "union" elif e.IsFSharpRecord then "record"
        elif e.IsFSharpAbbreviation then "abbrev" else "type"
    | :? FSharpMemberOrFunctionOrValue as v ->
        if v.IsMember || v.IsProperty then "member"
        elif v.FullType.IsFunctionType then "function" else "value"
    | :? FSharpActivePatternCase -> "activepattern"
    | :? FSharpGenericParameter -> "typar"
    | _ -> s.GetType().Name
let ownerOf (s: FSharpSymbol) =
    try
        match s with
        | :? FSharpUnionCase as c -> c.ReturnType.TypeDefinition.FullName
        | :? FSharpField as f -> (match f.DeclaringEntity with Some e -> e.FullName | None -> "")
        | :? FSharpEntity as e -> (match e.DeclaringEntity with Some d -> d.FullName | None -> defaultArg e.Namespace "")
        | :? FSharpMemberOrFunctionOrValue as v -> (match v.DeclaringEntity with Some e -> e.FullName | None -> "")
        | :? FSharpActivePatternCase as a -> (match a.Group.DeclaringEntity with Some e -> e.FullName | None -> "")
        | _ -> ""
    with _ -> ""
let root = "/home/hhh/repos/Composer/src/"
let rows =
    results.GetAllUsesOfAllSymbols()
    |> Seq.filter (fun u -> u.FileName.StartsWith root)
    |> Seq.choose (fun u ->
        let asm = try u.Symbol.Assembly.SimpleName with _ -> ""
        if asm = "Clef.Compiler.Service" || asm = "BAREWire" then
            let area = u.FileName.Substring(root.Length)
            Some (String.Join("\t", [| asm; area; string u.Range.StartLine; kindOf u.Symbol; ownerOf u.Symbol; u.Symbol.DisplayName |]))
        else None)
    |> Seq.distinct
    |> Seq.toArray
File.WriteAllLines(Path.Combine(here, "uses.tsv"), rows)
eprintfn "rows: %d" rows.Length
