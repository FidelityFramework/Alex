open System
open System.IO

let arguments = fsi.CommandLineArgs |> Array.skip 1
if arguments.Length < 3 || (if arguments[2] = "clef-provenance" then arguments.Length <> 4 else arguments.Length <> 3) then
  failwith "Expected source list, CLI log and analyzer mode, plus a visited-file output for scoped provenance."
let expected = File.ReadAllLines(arguments[0]) |> Set.ofArray
let lines = File.ReadAllLines(arguments[1])
let marker = "Running analyzers for "
let visited =
  lines
  |> Array.choose (fun line ->
    let index = line.IndexOf(marker, StringComparison.Ordinal)
    if index < 0 then None else Some (line.Substring(index + marker.Length).Trim()))
  |> Set.ofArray
// The scoped provenance verifier compares the selected and reported AXD000 files by
// device and inode, including hosts where FCS uses another spelling of a mount.
if arguments[2] = "clef-provenance" then
  if expected.IsEmpty || visited.Count <> expected.Count then failwith "Analyzer source coverage count mismatch."
  File.WriteAllLines(arguments[3], visited)
elif visited <> expected then
  failwithf "Analyzer source coverage mismatch: missing=%A unexpected=%A" (Set.difference expected visited) (Set.difference visited expected)
let required =
  match arguments[2] with
  | "alex" -> ["Clef production baseline"; "Alex published boundary"; "Alex dependency context"]
  | "alex-boundary" -> ["Alex published boundary"]
  | "clef" -> ["Clef production baseline"]
  | "clef-provenance" -> ["Alex dependency context"]
  | _ -> failwith "Unknown analyzer mode."
for name in required do
  if lines |> Array.exists (fun line -> line.Contains("Including " + name + " from ", StringComparison.Ordinal)) |> not then
    failwithf "Analyzer entry point was not loaded: %s" name
if lines |> Array.exists (fun line -> line.Contains("messages for this file are missing", StringComparison.Ordinal)) then
  failwith "An analyzer failed before producing its file diagnostics."
printfn "Validated %d evaluated source files and %d analyzer entry points." expected.Count required.Length
