open System
open System.IO
open System.Text.Json.Nodes
open System.Diagnostics
open System.Reflection
open System.Xml.Linq
open System.Security.Cryptography

let canonical path =
  let start = ProcessStartInfo("realpath")
  start.ArgumentList.Add("-e")
  start.ArgumentList.Add("--")
  start.ArgumentList.Add(path)
  start.RedirectStandardOutput <- true
  start.RedirectStandardError <- true
  use command = Process.Start(start)
  if isNull command then failwith "cannot start realpath"
  let result = command.StandardOutput.ReadToEnd().Trim()
  let error = command.StandardError.ReadToEnd()
  command.WaitForExit()
  if command.ExitCode <> 0 || String.IsNullOrWhiteSpace result then failwith ("cannot resolve path " + path + ": " + error.Trim())
  result

let tool = canonical (Path.Combine(__SOURCE_DIRECTORY__, ".."))
let root = canonical (Path.Combine(tool, "../.."))
let scratch = Path.Combine(root, "artifacts/alex-analyzers-tests/dependency-control")
Directory.CreateDirectory(scratch) |> ignore
let obj entries =
  let result = JsonObject()
  for key, value in entries do result.Add(key, value)
  result :> JsonNode
let str (value: string) = JsonValue.Create(value) :> JsonNode
let arr values =
  let result = JsonArray()
  for value in values do result.Add(value)
  result :> JsonNode
let save path (node: JsonNode) = File.WriteAllText(path, node.ToJsonString())
let file (path: string) =
  Directory.CreateDirectory(Path.GetDirectoryName path) |> ignore
  File.WriteAllText(path, "fixture")
  path
let fixtureDll = Path.Combine(tool, "tests/AlexFixture/bin/Debug/net10.0/Alex.dll")
let copiedDll (path: string) =
  Directory.CreateDirectory(Path.GetDirectoryName path) |> ignore
  File.Copy(fixtureDll, path, true)
  path
let target name = Path.Combine(scratch, name, "bin", "Alex.dll")
let targetRef name = Path.Combine(scratch, name, "ref", "Alex.dll")
let project name =
  let path = file (Path.Combine(scratch, name, name + ".fsproj"))
  copiedDll (target name) |> ignore
  copiedDll (targetRef name) |> ignore
  let escape value = System.Security.SecurityElement.Escape(value)
  File.WriteAllText(path, sprintf "<Project><PropertyGroup><TargetPath>%s</TargetPath><TargetRefPath>%s</TargetRefPath><AssemblyName>Alex</AssemblyName></PropertyGroup></Project>" (escape (target name)) (escape (targetRef name)))
  path
let rootProject, contract, library, foreign = project "App", project "Contract", project "Library", project "Foreign"
let packageRoot = Path.Combine(scratch, "packages")
let packageDir (name: string) = Path.Combine(packageRoot, name.ToLowerInvariant(), "1")
let packageMarker name = Path.Combine(packageDir name, name.ToLowerInvariant() + ".nupkg.sha512")
let packageAsset name = Path.Combine(packageDir name, "lib", name + ".dll")
for name in [ "FSharp.Core"; "XParsec" ] do
  copiedDll (packageAsset name) |> ignore
  file (packageMarker name) |> ignore
  File.WriteAllText(Path.Combine(packageDir name, ".nupkg.metadata"), "{\"contentHash\":\"fixture-content\"}")
let fsharp, xparsec = packageMarker "FSharp.Core", packageMarker "XParsec"
let spec (path: string) packages projects =
  let output = Path.Combine(Path.GetDirectoryName(path), "obj")
  Directory.CreateDirectory(output) |> ignore
  let refs = projects |> List.map (fun p -> p, obj [ ("projectPath", str p) ]) |> obj
  let dependencies = packages |> List.map (fun (name, version) -> name, obj [ "target", str "Package"; "version", str version ]) |> obj
  let restore = obj [ "projectPath", str path; "outputPath", str output; "frameworks", obj [ ("net10.0", obj [ ("projectReferences", refs) ]) ] ]
  obj [ "version", str "1.0.0"; "restore", restore; "frameworks", obj [ ("net10.0", obj [ "dependencies", dependencies; "frameworkReferences", obj [ ("Microsoft.NETCore.App", obj []) ] ]) ] ]
let rootSpec = spec rootProject [ "FSharp.Core", "1"; "XParsec", "1" ] [ contract ]
let contractSpec = spec contract [ ("FSharp.Core", "1") ] [ library ]
let librarySpec = spec library [ ("FSharp.Core", "1") ] []
let foreignSpec = spec foreign [ ("FSharp.Core", "1") ] []
let projectItems = [ rootProject, rootSpec; contract, contractSpec; library, librarySpec; foreign, foreignSpec ]
let asset (path: string) (projectSpec: JsonNode) packageNames =
  let output = Path.Combine(Path.GetDirectoryName(path), "obj")
  let libraries = packageNames |> List.map (fun name ->
    let relative = "lib/" + name + ".dll"
    let marker = name.ToLowerInvariant() + ".nupkg.sha512"
    name + "/1", obj [ "type", str "package"; "path", str (name.ToLowerInvariant() + "/1"); "sha512", str "fixture-content"; "files", arr [ str relative; str marker; str ".nupkg.metadata" ] ]) |> obj
  let targets = packageNames |> List.map (fun name -> name + "/1", obj [ ("compile", obj [ ("lib/" + name + ".dll", obj []) ]) ]) |> obj
  save (Path.Combine(output, "project.assets.json")) (obj [ "project", projectSpec.DeepClone(); "libraries", libraries; "targets", obj [ ("net10.0", targets) ]; "packageFolders", obj [ (packageRoot, obj []) ] ])
  let expected = packageNames |> List.map (fun name -> if name = "FSharp.Core" then str fsharp else str xparsec)
  save (Path.Combine(output, "project.nuget.cache")) (obj [ "success", JsonValue.Create(true) :> JsonNode; "projectFilePath", str path; "expectedPackageFiles", arr expected ])
asset rootProject rootSpec [ "FSharp.Core"; "XParsec" ]
asset contract contractSpec [ "FSharp.Core" ]
asset library librarySpec [ "FSharp.Core" ]
asset foreign foreignSpec [ "FSharp.Core" ]
let graph = obj [ ("projects", projectItems |> List.map (fun (path, value) -> path, value.DeepClone()) |> obj) ]
let graphPath = Path.Combine(scratch, "graph.json")
save graphPath graph
let reference name source owner package framework =
  let path = file (Path.Combine(scratch, "references", name + ".dll"))
  obj [ "Identity", str path; "ReferenceSourceTarget", str source; "MSBuildSourceProjectFile", str owner; "NuGetPackageId", str package; "NuGetPackageVersion", str "1"; "FrameworkReferenceName", str framework ]
let projectRow name path = obj [ "Identity", str (target name); "ReferenceAssembly", str (targetRef name); "ReferenceSourceTarget", str "ProjectReference"; "MSBuildSourceProjectFile", str path; "HasSingleTargetFramework", str "true"; "NuGetPackageId", str name ]
let packageRow name = obj [ "Identity", str (packageAsset name); "ReferenceSourceTarget", str "ResolveAssemblyReference"; "NuGetPackageId", str name; "NuGetPackageVersion", str "1"; "PathInPackage", str ("lib/" + name + ".dll") ]
let host = Environment.ProcessPath
if String.IsNullOrWhiteSpace host then failwith "No executing dotnet host."
let sdkVersion =
  let versionCommand = ProcessStartInfo(host)
  versionCommand.ArgumentList.Add("--version")
  versionCommand.RedirectStandardOutput <- true
  use versionProcess = Process.Start(versionCommand)
  let value = versionProcess.StandardOutput.ReadToEnd().Trim()
  versionProcess.WaitForExit()
  if versionProcess.ExitCode <> 0 || String.IsNullOrWhiteSpace value then failwith "Cannot identify executing SDK."
  value
let hostRoot = Path.GetDirectoryName(host)
let sdkProps = XDocument.Load(Path.Combine(hostRoot, "sdk", sdkVersion, "Microsoft.NETCoreSdk.BundledVersions.props"))
let attr (name: string) (value: string) = XAttribute(XName.Get name, value)
let xmlAttribute name (element: XElement) = let value = element.Attribute(XName.Get name) in if isNull value then "" else value.Value
let sdkEntry =
  sdkProps.Descendants(XName.Get "KnownFrameworkReference")
  |> Seq.filter (fun item -> xmlAttribute "Include" item = "Microsoft.NETCore.App" && xmlAttribute "TargetFramework" item = "net10.0")
  |> Seq.exactlyOne
let packName, packVersion = xmlAttribute "TargetingPackName" sdkEntry, xmlAttribute "TargetingPackVersion" sdkEntry
let pack = Path.Combine(hostRoot, "packs", packName, packVersion)
let packDll = Path.Combine(pack, "ref/net10.0/System.Runtime.dll")
if not (File.Exists packDll) then failwith "SDK framework test asset is missing."
let frameworkRow = obj [ "Identity", str packDll; "ReferenceSourceTarget", str "ResolveAssemblyReference"; "FrameworkReferenceName", str "Microsoft.NETCore.App"; "NuGetPackageId", str packName; "NuGetPackageVersion", str packVersion ]
let packRow = obj [ "Identity", str "Microsoft.NETCore.App"; "NuGetPackageId", str packName; "NuGetPackageVersion", str packVersion; "TargetFramework", str "net10.0"; "Path", str pack; "PackageDirectory", str pack ]
let rows = [ projectRow "Contract" contract; projectRow "Library" library; packageRow "FSharp.Core"; packageRow "XParsec"; frameworkRow ]
let propertyPaths = Path.Combine(Path.GetDirectoryName(contract), "..", "Contract", "Contract.fsproj") + ";" + library + ";"
let refs = obj [ "Properties", obj [ "AlexBoundaryPermitted", str propertyPaths; "AlexBoundaryAlsoPermitted", str ""; "AlexPermittedPackages", str "FSharp.Core;XParsec"; "PsgContractProject", str contract; "PsgContractLibrary", str library; "Configuration", str "Debug"; "Platform", str "AnyCPU"; "NetCoreRoot", str hostRoot; "MSBuildExtensionsPath", str (Path.Combine(hostRoot, "sdk", sdkVersion)); "NetCoreTargetingPackRoot", str (Path.Combine(hostRoot, "packs")); "NETCoreSdkVersion", str sdkVersion ]; "Items", obj [ "ReferencePath", rows |> List.map (fun value -> value.DeepClone()) |> arr; "ResolvedTargetingPack", arr [ packRow ] ] ]
let referencesPath = Path.Combine(scratch, "references.json")
let selected = Environment.GetEnvironmentVariable("DEPENDENCY_CONTROL_ONLY")
let mutable executed = 0
let runFor projectPath name (candidateGraph: JsonNode) (candidateRefs: JsonNode) expected =
  if String.IsNullOrEmpty selected || selected = name then
    executed <- executed + 1
    save graphPath candidateGraph
    save referencesPath candidateRefs
    let start = ProcessStartInfo(host)
    for argument in [ "fsi"; Path.Combine(tool, "ProjectInputs.fsx"); "--dependencies"; projectPath; graphPath; referencesPath; Path.Combine(scratch, name + ".manifest") ] do start.ArgumentList.Add(argument)
    start.RedirectStandardOutput <- true
    start.RedirectStandardError <- true
    use command = Process.Start(start)
    let stdout = command.StandardOutput.ReadToEnd()
    let stderr = command.StandardError.ReadToEnd()
    command.WaitForExit()
    let output = stdout + stderr
    File.WriteAllText(Path.Combine(scratch, name + ".log"), output)
    let ok = if expected = "PASS" || expected = "KNOWN-MISS" then command.ExitCode = 0 && output.Contains("Dependency closure verified") else command.ExitCode <> 0 && output.Contains(expected)
    if not ok then failwithf "Dependency control %s failed (exit %d): %s" name command.ExitCode output
    printfn "%s dependency %s" (if expected = "KNOWN-MISS" then "KNOWN-MISS" else "PASS") name
let run name candidateGraph candidateRefs expected = runFor rootProject name candidateGraph candidateRefs expected
let clone (value: JsonNode) = value.DeepClone()
let runSdk name path (expected: string) =
  if String.IsNullOrEmpty selected || selected = name then
    executed <- executed + 1
    let start = ProcessStartInfo(host)
    for argument in [ "fsi"; Path.Combine(tool, "ProjectInputs.fsx"); "--check-sdk"; path; "Microsoft.NETCore.App"; "net10.0" ] do start.ArgumentList.Add(argument)
    start.RedirectStandardOutput <- true
    start.RedirectStandardError <- true
    use command = Process.Start(start)
    let output = command.StandardOutput.ReadToEnd() + command.StandardError.ReadToEnd()
    command.WaitForExit()
    File.WriteAllText(Path.Combine(scratch, name + ".log"), output)
    if command.ExitCode = 0 || not (output.Contains expected) then failwithf "Dependency control %s failed (exit %d): %s" name command.ExitCode output
    printfn "PASS dependency %s" name
let runComparison name mode before after (expected: string) =
  if String.IsNullOrEmpty selected || selected = name then
    executed <- executed + 1
    let start = ProcessStartInfo(host)
    for argument in [ "fsi"; Path.Combine(tool, "ProjectInputs.fsx"); mode; before; after ] do start.ArgumentList.Add(argument)
    start.RedirectStandardOutput <- true
    start.RedirectStandardError <- true
    use command = Process.Start(start)
    let output = command.StandardOutput.ReadToEnd() + command.StandardError.ReadToEnd()
    command.WaitForExit()
    File.WriteAllText(Path.Combine(scratch, name + ".log"), output)
    if command.ExitCode = 0 || not (output.Contains expected) then failwithf "Dependency control %s failed (exit %d): %s" name command.ExitCode output
    printfn "PASS dependency %s" name
let graphDifferent = Path.Combine(scratch, "graph-different.json")
save graphDifferent (obj [ "projects", obj [] ])
runComparison "graph-environment" "--compare-graph" graphPath graphDifferent "restore graph depends on environment"
if String.IsNullOrEmpty selected || selected = "response-file" then
  executed <- executed + 1
  let directory = Path.Combine(scratch, "response-file")
  Directory.CreateDirectory(directory) |> ignore
  let path = Path.Combine(directory, "Fixture.proj")
  File.WriteAllText(path, "<Project><PropertyGroup><FixtureValue>original</FixtureValue></PropertyGroup></Project>")
  let response = Path.Combine(directory, "Directory.Build.rsp")
  File.WriteAllText(response, "-property:FixtureValue=injected\n")
  let evaluate noResponse =
    let start = ProcessStartInfo(host)
    for argument in ([ "msbuild" ] @ (if noResponse then [ "-noAutoResponse" ] else []) @ [ path; "-getProperty:FixtureValue" ]) do start.ArgumentList.Add(argument)
    start.RedirectStandardOutput <- true
    start.RedirectStandardError <- true
    use command = Process.Start(start)
    let output = command.StandardOutput.ReadToEnd().Trim()
    let error = command.StandardError.ReadToEnd()
    command.WaitForExit()
    if command.ExitCode <> 0 then failwithf "Response fixture failed: %s" error
    output
  try
    let injected, protectedValue = evaluate false, evaluate true
    File.WriteAllText(Path.Combine(scratch, "response-file.log"), sprintf "unprotected=%s\nprotected=%s\n" injected protectedValue)
    if injected <> "injected" || protectedValue <> "original" then failwithf "Response fixture did not discriminate: %s / %s" injected protectedValue
    printfn "PASS dependency response-file"
  finally
    File.Delete response
let sdkFixture = Path.Combine(scratch, "sdk-fixture.props")
let sdkItem condition = "<KnownFrameworkReference Include=\"Microsoft.NETCore.App\" TargetFramework=\"net10.0\" TargetingPackName=\"Microsoft.NETCore.App.Ref\" TargetingPackVersion=\"1\"" + condition + " />"
File.WriteAllText(sdkFixture, "<Project><ItemGroup>" + sdkItem "" + sdkItem "" + "</ItemGroup></Project>")
runSdk "ambiguous-sdk" sdkFixture "missing or ambiguous bundled framework:"
File.WriteAllText(sdkFixture, "<Project><ItemGroup>" + sdkItem " Condition=\"false\"" + "</ItemGroup></Project>")
runSdk "conditional-sdk" sdkFixture "conditional bundled framework:"
File.WriteAllText(sdkFixture, "<Project><ItemGroup Condition=\"false\">" + sdkItem "" + "</ItemGroup></Project>")
runSdk "conditional-sdk-group" sdkFixture "conditional bundled framework:"
File.WriteAllText(sdkFixture, "<Project><Choose><When Condition=\"true\"><ItemGroup>" + sdkItem "" + "</ItemGroup></When></Choose></Project>")
runSdk "nested-sdk-condition" sdkFixture "conditional bundled framework:"
runSdk "missing-sdk" (Path.Combine(scratch, "missing-sdk.props")) "missing SDK bundled versions"
let normalRefsPath = Path.Combine(scratch, "normal-refs.json")
let changedRefsPath = Path.Combine(scratch, "changed-refs.json")
let changedRefs = refs.DeepClone()
changedRefs.["Properties"].["PsgContractProject"] <- str foreign
save normalRefsPath refs
save changedRefsPath changedRefs
runComparison "environment-owner-override" "--compare-references" normalRefsPath changedRefsPath "evaluation depends on environment"
let changedRows = refs.DeepClone()
changedRows.["Items"].["ReferencePath"].[2].["PathInPackage"] <- str "lib/different.dll"
save changedRefsPath changedRows
runComparison "environment-reference-override" "--compare-references" normalRefsPath changedRefsPath "resolved references depend on environment"
run "valid" graph refs "PASS"
let wrongHost = clone refs
wrongHost.["Properties"].["NetCoreRoot"] <- str scratch
run "evaluation-host-mismatch" graph wrongHost "evaluation host differs from validator host"
let wrongSdk = clone refs
wrongSdk.["Properties"].["NETCoreSdkVersion"] <- str "0.0.0"
run "executing-sdk-mismatch" graph wrongSdk "executing SDK mismatch:"
let wrongConfiguration = clone refs
wrongConfiguration.["Properties"].["Configuration"] <- str "Release"
run "loader-configuration" graph wrongConfiguration "unsupported analyzer loader configuration"
let missing = clone refs
(missing["Properties"]).AsObject().Remove("AlexPermittedPackages") |> ignore
run "missing-set" graph missing "missing field AlexPermittedPackages"
let package = clone refs
package["Properties"]["AlexPermittedPackages"] <- str "FSharp.Core"
run "unapproved-package" graph package "package not permitted: XParsec/1"
let denied = clone refs
denied["Properties"]["AlexBoundaryPermitted"] <- str contract
run "unapproved-project" graph denied ("project not permitted: " + library)
let hint = clone refs
(hint["Items"]["ReferencePath"]).AsArray().Add(reference "Hint" "" "" "" "")
run "hint-path" graph hint "unclassifiable reference:"
let spoofed = clone refs
let spoofedPackage = reference "SpoofedPackage" "ResolveAssemblyReference" "" "FSharp.Core" ""
spoofedPackage["PathInPackage"] <- str "lib/FSharp.Core.dll"
(spoofed["Items"]["ReferencePath"]).AsArray().Add(spoofedPackage)
run "spoofed-package" graph spoofed "unverified package asset:"
let spoofedFramework = clone refs
let frameworkImpostor = frameworkRow.DeepClone()
let frameworkImpostorPath = Path.Combine(scratch, "references", "SpoofedFramework.dll")
File.Copy(packDll, frameworkImpostorPath, true)
frameworkImpostor["Identity"] <- str frameworkImpostorPath
(spoofedFramework["Items"]["ReferencePath"]).AsArray().Add(frameworkImpostor)
run "spoofed-framework" graph spoofedFramework "unverified framework asset:"
let injected = clone refs
let injectedPack = Path.Combine(scratch, "injected-pack")
let injectedDll = copiedDll (Path.Combine(injectedPack, "ref/net10.0/Alex.dll"))
let injectedIdentity = AssemblyName.GetAssemblyName(injectedDll)
let injectedList = Path.Combine(injectedPack, "data/FrameworkList.xml")
Directory.CreateDirectory(Path.GetDirectoryName injectedList) |> ignore
let injectedEntry = XElement(XName.Get "File", attr "Type" "Managed", attr "Path" "ref/net10.0/Alex.dll", attr "AssemblyName" injectedIdentity.Name, attr "AssemblyVersion" (string injectedIdentity.Version), attr "PublicKeyToken" (injectedIdentity.GetPublicKeyToken() |> Convert.ToHexString))
XDocument(XElement(XName.Get "FileList", attr "FrameworkName" "Microsoft.NETCore.App", injectedEntry)).Save(injectedList)
injected.["Items"].["ResolvedTargetingPack"].[0].["Path"] <- str injectedPack
injected.["Items"].["ResolvedTargetingPack"].[0].["PackageDirectory"] <- str injectedPack
injected.["Items"].["ReferencePath"].[4].["Identity"] <- str injectedDll
run "injected-pack" graph injected "targeting pack not host-designated:"
let mismatchedPackDirectory = clone refs
mismatchedPackDirectory.["Items"].["ResolvedTargetingPack"].[0].["PackageDirectory"] <- str scratch
run "pack-directory-mismatch" graph mismatchedPackDirectory "targeting pack path mismatch:"
let overriddenVersion = clone refs
overriddenVersion.["Items"].["ResolvedTargetingPack"].[0].["NuGetPackageVersion"] <- str "999.0"
overriddenVersion.["Items"].["ReferencePath"].[4].["NuGetPackageVersion"] <- str "999.0"
run "overridden-pack-version" graph overriddenVersion "targeting pack version differs from bundled:"
let widened = clone refs
widened.["Properties"].["AlexBoundaryAlsoPermitted"] <- str foreign
run "widened-permitted-set" graph widened "additional permitted projects are unsupported in this profile"
if String.IsNullOrEmpty selected || selected = "msbuild-target-pack" || selected = "msbuild-static-pack" then
  let sdkFixture name targetTime =
    let directory = Path.Combine(scratch, name)
    Directory.CreateDirectory(directory) |> ignore
    let emptyFeed = Path.Combine(directory, "empty-feed")
    Directory.CreateDirectory(emptyFeed) |> ignore
    let escaped value = System.Security.SecurityElement.Escape(value)
    let item = sprintf "<ResolvedTargetingPack Include=\"Microsoft.NETCore.App\"><NuGetPackageId>%s</NuGetPackageId><NuGetPackageVersion>999.0</NuGetPackageVersion><TargetFramework>net10.0</TargetFramework><Path>%s</Path><PackageDirectory>%s</PackageDirectory></ResolvedTargetingPack>" packName (escaped injectedPack) (escaped injectedPack)
    let reference = sprintf "<Reference Include=\"Injected\"><HintPath>%s</HintPath><FrameworkReferenceName>Microsoft.NETCore.App</FrameworkReferenceName><NuGetPackageId>%s</NuGetPackageId><NuGetPackageVersion>999.0</NuGetPackageVersion></Reference>" (escaped injectedDll) packName
    let injection = if targetTime then "<Target Name=\"ReplacePack\" BeforeTargets=\"ResolveReferences\"><ItemGroup><ResolvedTargetingPack Remove=\"Microsoft.NETCore.App\" />" + item + "</ItemGroup></Target>" else "<ItemGroup>" + item + "</ItemGroup>"
    let path = Path.Combine(directory, "Probe.csproj")
    File.WriteAllText(path, "<Project Sdk=\"Microsoft.NET.Sdk\"><PropertyGroup><TargetFramework>net10.0</TargetFramework></PropertyGroup><ItemGroup>" + reference + "</ItemGroup>" + injection + "</Project>")
    let execute arguments =
      let start = ProcessStartInfo(host)
      for argument in arguments do start.ArgumentList.Add(argument)
      start.RedirectStandardOutput <- true
      start.RedirectStandardError <- true
      use command = Process.Start(start)
      let output = command.StandardOutput.ReadToEnd() + command.StandardError.ReadToEnd()
      command.WaitForExit()
      command.ExitCode, output
    let restoreStatus, restoreOutput = execute [ "restore"; path; "--source"; emptyFeed ]
    if restoreStatus <> 0 then failwithf "Scratch SDK restore failed: %s" restoreOutput
    let status, output = execute [ "msbuild"; path; "-target:ResolveReferences"; "-getItem:ResolvedTargetingPack,ReferencePath" ]
    File.WriteAllText(Path.Combine(directory, "resolved.log"), output)
    status, output
  if String.IsNullOrEmpty selected || selected = "msbuild-static-pack" then
    executed <- executed + 1
    let status, output = sdkFixture "static-pack" false
    if status = 0 || not (output.Contains "MSB4018") || not (output.Contains "same key") then failwithf "Static injected-pack SDK refusal changed (exit %d): %s" status output
    printfn "PASS dependency msbuild-static-pack\n"
  if String.IsNullOrEmpty selected || selected = "msbuild-target-pack" then
    let status, output = sdkFixture "target-pack" true
    if status <> 0 then failwithf "Target injected-pack fixture failed (exit %d): %s" status output
    let actual = JsonNode.Parse(output)
    let findRow (itemName: string) (predicate: JsonNode -> bool) =
      actual.["Items"].[itemName].AsArray()
      |> Seq.filter predicate
      |> Seq.exactlyOne
      |> fun value -> value.DeepClone()
    let injectedPackRow = findRow "ResolvedTargetingPack" (fun value -> value.["Identity"].GetValue<string>() = "Microsoft.NETCore.App" && value.["NuGetPackageVersion"].GetValue<string>() = "999.0")
    let injectedReference = findRow "ReferencePath" (fun value -> not (isNull value.["OriginalItemSpec"]) && value.["OriginalItemSpec"].GetValue<string>() = "Injected")
    let actualInjection = clone refs
    (actualInjection.["Items"].["ResolvedTargetingPack"]).AsArray().Add(injectedPackRow)
    (actualInjection.["Items"].["ReferencePath"]).AsArray().Add(injectedReference)
    run "msbuild-target-pack" graph actualInjection "targeting pack version differs from bundled:"
let spoofedProject = clone refs
let projectImpostor = (projectRow "Contract" contract).DeepClone()
projectImpostor["Identity"] <- str (target "Foreign")
(spoofedProject["Items"]["ReferencePath"]).AsArray().Add(projectImpostor)
run "spoofed-project" graph spoofedProject "project output identity mismatch:"
let unknownTarget = clone refs
(unknownTarget.["Items"].["ReferencePath"].AsArray().[0]).AsObject().Remove("HasSingleTargetFramework") |> ignore
run "missing-target-shape" graph unknownTarget "missing HasSingleTargetFramework:"
let multiTarget = clone refs
multiTarget.["Items"].["ReferencePath"].[0].["HasSingleTargetFramework"] <- str "false"
run "multi-target" graph multiTarget "unsupported multi-target project reference:"
let metadata = Path.Combine(packageDir "FSharp.Core", ".nupkg.metadata")
File.WriteAllText(metadata, "{\"contentHash\":\"different\"}")
run "content-hash" graph refs "package content hash mismatch:"
File.WriteAllText(metadata, "{\"contentHash\":\"fixture-content\"}")
File.Delete(metadata)
run "missing-metadata" graph refs "missing package metadata:"
File.WriteAllText(metadata, "{\"contentHash\":\"fixture-content\"}")
File.Delete(fsharp)
run "missing-marker" graph refs "missing restored package file:"
file fsharp |> ignore
let cachePath = Path.Combine(Path.GetDirectoryName(rootProject), "obj/project.nuget.cache")
let cache = JsonNode.Parse(File.ReadAllText cachePath)
cache["expectedPackageFiles"] <- arr [ str xparsec ]
save cachePath cache
run "marker-not-cached" graph refs "restore marker not in cache:"
asset rootProject rootSpec [ "FSharp.Core"; "XParsec" ]
let assetsPath = Path.Combine(Path.GetDirectoryName(rootProject), "obj/project.assets.json")
let duplicateHash = JsonNode.Parse(File.ReadAllText assetsPath)
(duplicateHash.["libraries"].["FSharp.Core/1"].["files"]).AsArray().Add(str "other.nupkg.sha512")
save assetsPath duplicateHash
run "ambiguous-hash" graph refs "missing or ambiguous package hash:"
asset rootProject rootSpec [ "FSharp.Core"; "XParsec" ]
let alternateAsset = Path.Combine(packageDir "FSharp.Core", "lib/alternate/FSharp.Core.dll")
copiedDll alternateAsset |> ignore
let alternate = JsonNode.Parse(File.ReadAllText assetsPath)
(alternate.["libraries"].["FSharp.Core/1"].["files"]).AsArray().Add(str "lib/alternate/FSharp.Core.dll")
save assetsPath alternate
let alternateRefs = clone refs
let alternativeRow = alternateRefs.["Items"].["ReferencePath"].AsArray().[2]
alternativeRow["Identity"] <- str alternateAsset
alternativeRow["PathInPackage"] <- str "lib/alternate/FSharp.Core.dll"
run "unselected-compile-asset" graph alternateRefs "unverified package asset:"
asset rootProject rootSpec [ "FSharp.Core"; "XParsec" ]
let otherDll = Path.Combine(tool, "tests/ImpostorFixture/bin/Debug/net10.0/Unrelated.Contract.dll")
let digest path =
  use stream = File.OpenRead(path)
  SHA256.HashData(stream) |> Convert.ToHexString
let originalPackageDigest = digest (packageAsset "FSharp.Core")
File.Copy(otherDll, packageAsset "FSharp.Core", true)
run "package-dll-content" graph refs "KNOWN-MISS"
if String.IsNullOrEmpty selected || selected = "package-dll-content" then
  let changedDigest = digest (packageAsset "FSharp.Core")
  let manifest = File.ReadAllText(Path.Combine(scratch, "package-dll-content.manifest"))
  if changedDigest = originalPackageDigest || not (manifest.Contains changedDigest) then failwith "Changed package DLL bytes were not recorded."
File.Copy(fixtureDll, packageAsset "FSharp.Core", true)
let extraFramework = clone graph
extraFramework.["projects"].[rootProject].["frameworks"].["net10.0"].["frameworkReferences"].["Microsoft.AspNetCore.App"] <- obj []
asset rootProject (extraFramework.["projects"].[rootProject]) [ "FSharp.Core"; "XParsec" ]
run "extra-framework" extraFramework refs ("framework reference not permitted: " + rootProject)
asset rootProject rootSpec [ "FSharp.Core"; "XParsec" ]
let stale = clone graph
stale.["projects"].[rootProject].["version"] <- str "2.0.0"
run "stale-graph" stale refs ("stale restore graph: " + rootProject)
if String.IsNullOrEmpty selected || selected = "stale-project" || selected = "real-extra-framework" || selected = "preprocess-changed" then
  let path = Path.Combine(scratch, "RealGraph", "RealGraph.csproj")
  Directory.CreateDirectory(Path.GetDirectoryName path) |> ignore
  let writeProject extra = File.WriteAllText(path, "<Project Sdk=\"Microsoft.NET.Sdk\"><PropertyGroup><TargetFramework>net10.0</TargetFramework></PropertyGroup>" + extra + "</Project>")
  let generate destination =
    let start = ProcessStartInfo(host)
    for argument in [ "msbuild"; path; "-target:GenerateRestoreGraphFile"; "-property:RestoreGraphOutputPath=" + destination ] do start.ArgumentList.Add(argument)
    start.RedirectStandardOutput <- true
    start.RedirectStandardError <- true
    use command = Process.Start(start)
    let output = command.StandardOutput.ReadToEnd() + command.StandardError.ReadToEnd()
    command.WaitForExit()
    if command.ExitCode <> 0 then failwithf "Restore graph fixture failed: %s" output
    JsonNode.Parse(File.ReadAllText destination)
  writeProject ""
  let oldGraph = generate (Path.Combine(scratch, "old-real.graph.json"))
  let oldSpec = oldGraph.["projects"].[path]
  let output = oldSpec.["restore"].["outputPath"].GetValue<string>()
  Directory.CreateDirectory(output) |> ignore
  save (Path.Combine(output, "project.assets.json")) (obj [ "project", oldSpec.DeepClone(); "libraries", obj [] ])
  writeProject "<ItemGroup><PackageReference Include=\"Synthetic.Dependency\" Version=\"1.0.0\" /></ItemGroup>"
  let newGraph = generate (Path.Combine(scratch, "new-real.graph.json"))
  runFor path "stale-project" newGraph refs ("stale restore graph: " + path)
  writeProject "<ItemGroup><FrameworkReference Include=\"Microsoft.AspNetCore.App\" /></ItemGroup>"
  let frameworkGraph = generate (Path.Combine(scratch, "framework-real.graph.json"))
  let frameworkSpec = frameworkGraph.["projects"].[path]
  save (Path.Combine(output, "project.assets.json")) (obj [ "project", frameworkSpec.DeepClone(); "libraries", obj [] ])
  save (Path.Combine(output, "project.nuget.cache")) (obj [ "success", JsonValue.Create(true) :> JsonNode; "projectFilePath", str path; "expectedPackageFiles", arr [] ])
  runFor path "real-extra-framework" frameworkGraph refs ("framework reference not permitted: " + path)
  let localProps = Path.Combine(Path.GetDirectoryName path, "Directory.Build.local.props")
  let writeProps value = File.WriteAllText(localProps, "<Project><PropertyGroup><FixtureValue>" + value + "</FixtureValue></PropertyGroup></Project>")
  let generatePreprocess destination =
    let start = ProcessStartInfo(host)
    for argument in [ "msbuild"; path; "-property:Configuration=Debug"; "-property:Platform=AnyCPU"; "-preprocess:" + destination ] do start.ArgumentList.Add(argument)
    start.RedirectStandardOutput <- true
    start.RedirectStandardError <- true
    use command = Process.Start(start)
    let output = command.StandardOutput.ReadToEnd() + command.StandardError.ReadToEnd()
    command.WaitForExit()
    if command.ExitCode <> 0 then failwithf "Preprocess fixture failed: %s" output
  writeProject "<Import Project=\"Directory.Build.local.props\" />"
  let before, after = Path.Combine(scratch, "import-before.xml"), Path.Combine(scratch, "import-after.xml")
  writeProps "before"
  generatePreprocess before
  writeProps "after"
  generatePreprocess after
  runComparison "preprocess-changed" "--compare-preprocess" before after "preprocess changed during evaluation"
let collision = clone refs
(collision["Items"]["ReferencePath"]).AsArray().Add(reference "SameContractName" "ProjectReference" foreign "" "")
run "foreign-project" graph collision ("project reference not permitted: " + foreign)
let extraOwnerPackage = clone refs
extraOwnerPackage.["Properties"].["AlexPermittedPackages"] <- str "FSharp.Core;XParsec;Extra"
run "extra-owner-package" graph extraOwnerPackage "root direct packages differ from the owner-declared permitted set"
let inactiveFramework = clone refs
inactiveFramework.["Items"].["ReferencePath"].[4].["FrameworkReferenceName"] <- str "Microsoft.AspNetCore.App"
run "inactive-framework" graph inactiveFramework "inactive framework reference: Microsoft.AspNetCore.App"
let multiFrameworkGraph = clone graph
multiFrameworkGraph.["projects"].[rootProject].["frameworks"].["net9.0"] <- obj []
asset rootProject (multiFrameworkGraph.["projects"].[rootProject]) [ "FSharp.Core"; "XParsec" ]
run "multi-framework" multiFrameworkGraph refs ("unsupported target framework count: " + rootProject)
asset rootProject rootSpec [ "FSharp.Core"; "XParsec" ]
let originalContract = File.ReadAllText contract
try
  File.WriteAllText(contract, originalContract.Replace("<AssemblyName>Alex</AssemblyName>", "<AssemblyName>Other</AssemblyName>"))
  run "project-assembly-mismatch" graph refs ("project assembly identity mismatch: " + contract)
finally
  File.WriteAllText(contract, originalContract)
let originalRoot = File.ReadAllText rootProject
let imported = Path.Combine(Path.GetDirectoryName rootProject, "EnvironmentFixture.props")
let previousFixtureEnvironment = Environment.GetEnvironmentVariable("ALEX_ANALYZER_FIXTURE_IMPORT")
try
  File.WriteAllText(imported, "<Project><PropertyGroup><FixtureImported>true</FixtureImported></PropertyGroup></Project>")
  File.WriteAllText(rootProject, originalRoot.Replace("</Project>", "<Import Project=\"EnvironmentFixture.props\" Condition=\"'$(ALEX_ANALYZER_FIXTURE_IMPORT)' == '1'\" /></Project>"))
  Environment.SetEnvironmentVariable("ALEX_ANALYZER_FIXTURE_IMPORT", "1")
  run "validator-preprocess-environment" graph refs ("preprocess depends on environment: " + rootProject)
finally
  Environment.SetEnvironmentVariable("ALEX_ANALYZER_FIXTURE_IMPORT", previousFixtureEnvironment)
  File.WriteAllText(rootProject, originalRoot)
  File.Delete imported
if String.IsNullOrEmpty selected || selected = "validator-preprocess-changed" then
  let key = SHA256.HashData(System.Text.Encoding.UTF8.GetBytes(rootProject)) |> Convert.ToHexString
  let before = Path.Combine(scratch, "preprocess-" + key + "-before.xml")
  let scrubbed = Path.Combine(scratch, "preprocess-" + key + "-scrubbed.xml")
  let marker = Path.Combine(scratch, "preprocess-change-marker")
  for path in [ before; scrubbed; marker ] do if File.Exists path then File.Delete path
  let fakeBin = Path.Combine(scratch, "preprocess-hook")
  Directory.CreateDirectory(fakeBin) |> ignore
  let executable = Path.Combine(fakeBin, "realpath")
  let quote (value: string) = "'" + value.Replace("'", "'\\''") + "'"
  File.WriteAllText(executable, sprintf "#!/bin/sh\nif [ -f %s ] && [ -f %s ] && [ ! -f %s ]; then\n  printf '%%s' '<Project><PropertyGroup><FixtureImported>changed</FixtureImported></PropertyGroup></Project>' > %s\n  touch %s\nfi\nexec /usr/bin/realpath \"$@\"\n" (quote before) (quote scrubbed) (quote marker) (quote imported) (quote marker))
  // Worker NFSv4 mounts map owner uid while .NET PATH search checks execute permissions for the local process uid.
  File.SetUnixFileMode(executable, UnixFileMode.UserRead ||| UnixFileMode.UserWrite ||| UnixFileMode.UserExecute ||| UnixFileMode.GroupRead ||| UnixFileMode.GroupExecute ||| UnixFileMode.OtherRead ||| UnixFileMode.OtherExecute)
  let oldPath = Environment.GetEnvironmentVariable("PATH")
  try
    File.WriteAllText(imported, "<Project><PropertyGroup><FixtureImported>before</FixtureImported></PropertyGroup></Project>")
    File.WriteAllText(rootProject, originalRoot.Replace("</Project>", "<Import Project=\"EnvironmentFixture.props\" /></Project>"))
    Environment.SetEnvironmentVariable("PATH", fakeBin + ":" + oldPath)
    run "validator-preprocess-changed" graph refs ("preprocess changed during evaluation: " + rootProject)
    if not (File.Exists marker) then failwith "The preprocess-change hook did not run."
  finally
    Environment.SetEnvironmentVariable("PATH", oldPath)
    File.WriteAllText(rootProject, originalRoot)
    File.Delete imported
let cycleGraph = clone graph
cycleGraph.["projects"].[library].["restore"].["frameworks"].["net10.0"].["projectReferences"].[contract] <- obj [ ("projectPath", str contract) ]
asset library (cycleGraph.["projects"].[library]) [ "FSharp.Core" ]
run "project-cycle" cycleGraph refs ("project cycle at " + contract)
asset library librarySpec [ "FSharp.Core" ]
let chainGraph = clone graph
chainGraph.["projects"].[contract].["restore"].["frameworks"].["net10.0"].["projectReferences"].[foreign] <- obj [ ("projectPath", str foreign) ]
let changedContract = chainGraph.["projects"].[contract]
asset contract changedContract [ "FSharp.Core" ]
run "foreign-chain" chainGraph refs ("project not permitted: " + foreign)
if executed = 0 then failwith "No dependency control matched."
