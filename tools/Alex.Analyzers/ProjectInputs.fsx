open System
open System.IO
open System.Text.Json
open System.Text.Json.Nodes
open System.Diagnostics
open System.Security.Cryptography
open System.Reflection
open System.Xml.Linq

let fail reason = failwith ("Dependency evidence incomplete: " + reason)
let readJson path =
  if not (File.Exists path) then fail ("missing " + path)
  JsonNode.Parse(File.ReadAllText path)
let fileDigest path =
  if not (File.Exists path) then fail ("missing evidence file: " + path)
  use stream = File.OpenRead(path)
  SHA256.HashData(stream) |> Convert.ToHexString
let field (name: string) (node: JsonNode) =
  if isNull node || isNull node[name] then fail ("missing field " + name)
  node[name]
let text (node: JsonNode) =
  if isNull node then fail "missing string"
  node.GetValue<string>()
let objectItems (node: JsonNode) =
  match node with
  | :? JsonObject as value -> value |> Seq.map (fun entry -> entry.Key, entry.Value) |> Seq.toList
  | _ -> fail "expected object"
let arrayItems (node: JsonNode) =
  match node with
  | :? JsonArray as value -> value |> Seq.toList
  | _ -> fail "expected array"
let canonical path =
  let start = ProcessStartInfo("realpath")
  start.ArgumentList.Add("-e")
  start.ArgumentList.Add("--")
  start.ArgumentList.Add(path)
  start.RedirectStandardOutput <- true
  start.RedirectStandardError <- true
  use command = Process.Start(start)
  if isNull command then fail "cannot start realpath"
  let result = command.StandardOutput.ReadToEnd().Trim()
  let error = command.StandardError.ReadToEnd()
  command.WaitForExit()
  if command.ExitCode <> 0 || String.IsNullOrWhiteSpace result then fail ("cannot resolve path " + path + ": " + error.Trim())
  result
let setOfProperty name node =
  let values = text (field name node)
  let result = values.Split(';', StringSplitOptions.RemoveEmptyEntries ||| StringSplitOptions.TrimEntries) |> Set.ofArray
  if Set.isEmpty result then fail ("empty permitted set " + name)
  result
let normalizedPackages values = values |> Set.map (fun (value: string) -> value.ToUpperInvariant())
let optionalText (name: string) (node: JsonNode) =
  if isNull node || isNull node[name] then "" else text node[name]
let safeRelative (path: string) =
  not (String.IsNullOrWhiteSpace path) && not (Path.IsPathRooted path) &&
  (path.Replace('\\', '/').Split('/') |> Array.forall (fun part -> part <> ".." && part <> ""))
let bundledFramework (document: XDocument) framework targetFramework =
  let attribute name (element: XElement) =
    let value = element.Attribute(XName.Get(name))
    if isNull value then "" else value.Value
  let entries =
    document.Descendants(XName.Get("KnownFrameworkReference"))
    |> Seq.filter (fun entry -> attribute "Include" entry = framework && attribute "TargetFramework" entry = targetFramework)
    |> Seq.toList
  let entry = match entries with [ value ] -> value | _ -> fail ("missing or ambiguous bundled framework: " + framework)
  if not (String.IsNullOrWhiteSpace (attribute "Condition" entry)) ||
     (entry.Ancestors() |> Seq.exists (fun parent ->
       (parent.Name <> XName.Get("ItemGroup") && parent.Name <> XName.Get("Project")) ||
       not (String.IsNullOrWhiteSpace (attribute "Condition" parent)))) then
    fail ("conditional bundled framework: " + framework)
  let name, version = attribute "TargetingPackName" entry, attribute "TargetingPackVersion" entry
  if not (safeRelative name && safeRelative version) then fail ("invalid bundled targeting pack: " + framework)
  name, version
let compareReferences normalPath scrubbedPath =
  let normal, scrubbed = readJson normalPath, readJson scrubbedPath
  if not (JsonNode.DeepEquals(field "Properties" normal, field "Properties" scrubbed)) then fail "evaluation depends on environment"
  let selectedRows itemName names root =
    field "Items" root |> field itemName |> arrayItems
    |> List.map (fun row -> names |> List.map (fun name -> optionalText name row))
    |> List.sort
  let references = [ "Identity"; "ReferenceAssembly"; "ReferenceSourceTarget"; "MSBuildSourceProjectFile"; "HasSingleTargetFramework"; "FrameworkReferenceName"; "NuGetPackageId"; "NuGetPackageVersion"; "PathInPackage" ]
  let packs = [ "Identity"; "NuGetPackageId"; "NuGetPackageVersion"; "TargetFramework"; "Path"; "PackageDirectory" ]
  if selectedRows "ReferencePath" references normal <> selectedRows "ReferencePath" references scrubbed ||
     selectedRows "ResolvedTargetingPack" packs normal <> selectedRows "ResolvedTargetingPack" packs scrubbed then
    fail "resolved references depend on environment"
let checkOwnerProperties references =
  let properties = field "Properties" references
  if not (String.IsNullOrWhiteSpace (text (field "AlexBoundaryAlsoPermitted" properties))) then fail "additional permitted projects are unsupported in this profile"
let validateDependencies project graphPath referencePath manifestPath =
  let project = canonical project
  let graph = readJson graphPath
  let references = readJson referencePath
  let properties = field "Properties" references
  checkOwnerProperties references
  let allowedProjects = setOfProperty "AlexBoundaryPermitted" properties |> Set.map canonical
  let allowedPackages = setOfProperty "AlexPermittedPackages" properties |> normalizedPackages
  let configuration = text (field "Configuration" properties)
  let platform = text (field "Platform" properties)
  let targetingPackRoot = text (field "NetCoreTargetingPackRoot" properties) |> canonical
  let sdkVersion = text (field "NETCoreSdkVersion" properties)
  if String.IsNullOrWhiteSpace configuration || String.IsNullOrWhiteSpace platform || String.IsNullOrWhiteSpace sdkVersion then fail "missing consumer build properties"
  let host =
    match Environment.ProcessPath |> Option.ofObj with
    | Some path when not (String.IsNullOrWhiteSpace path) -> canonical path
    | _ -> fail "missing executing dotnet host"
  let hostRoot = Path.GetDirectoryName(host)
  let versionStart = ProcessStartInfo(host)
  versionStart.ArgumentList.Add("--version")
  versionStart.RedirectStandardOutput <- true
  versionStart.RedirectStandardError <- true
  use versionCommand = Process.Start(versionStart)
  if isNull versionCommand then fail "cannot identify executing SDK"
  let actualSdk = versionCommand.StandardOutput.ReadToEnd().Trim()
  let versionError = versionCommand.StandardError.ReadToEnd()
  versionCommand.WaitForExit()
  if versionCommand.ExitCode <> 0 || actualSdk <> sdkVersion || not (safeRelative sdkVersion) then fail ("executing SDK mismatch: " + versionError.Trim())
  if configuration <> "Debug" || platform <> "AnyCPU" then fail "unsupported analyzer loader configuration"
  if canonical (text (field "NetCoreRoot" properties)) <> canonical hostRoot ||
     canonical (text (field "MSBuildExtensionsPath" properties)) <> canonical (Path.Combine(hostRoot, "sdk", sdkVersion)) then
    fail "evaluation host differs from validator host"
  let bundledVersions = Path.Combine(hostRoot, "sdk", sdkVersion, "Microsoft.NETCoreSdk.BundledVersions.props")
  if not (File.Exists bundledVersions) then fail "missing SDK bundled versions"
  let sdkDocument = XDocument.Load(bundledVersions)
  let retainedHome = Environment.GetEnvironmentVariable("HOME")
  if String.IsNullOrWhiteSpace retainedHome then fail "missing retained HOME trust input"
  let runMsbuild scrub arguments =
    let start = ProcessStartInfo(host)
    start.ArgumentList.Add("msbuild")
    start.ArgumentList.Add("-noAutoResponse")
    for argument in arguments do start.ArgumentList.Add(argument)
    start.RedirectStandardOutput <- true
    start.RedirectStandardError <- true
    if scrub then
      start.Environment.Clear()
      start.Environment["HOME"] <- retainedHome
      start.Environment["PATH"] <- "/usr/bin:/bin"
      start.Environment["DOTNET_ROOT"] <- hostRoot
      start.Environment["MSBUILDDISABLENODEREUSE"] <- "1"
    use command = Process.Start(start)
    if isNull command then fail "cannot start MSBuild"
    let output = command.StandardOutput.ReadToEnd()
    let error = command.StandardError.ReadToEnd()
    command.WaitForExit()
    if command.ExitCode <> 0 then fail ("MSBuild evaluation failed: " + error.Trim())
    output
  let scratch = Path.GetDirectoryName(Path.GetFullPath manifestPath)
  let preprocess (path: string) label scrub =
    let key = SHA256.HashData(System.Text.Encoding.UTF8.GetBytes(path)) |> Convert.ToHexString
    let output = Path.Combine(scratch, "preprocess-" + key + "-" + label + ".xml")
    runMsbuild scrub [ path; "-property:Configuration=" + configuration; "-property:Platform=" + platform; "-preprocess:" + output ] |> ignore
    if not (File.Exists output) then fail ("missing preprocess output: " + path)
    output, fileDigest output
  let projectEntries = field "projects" graph |> objectItems |> List.map (fun (path, spec) -> canonical path, spec)
  let graphProjects = Map.ofList projectEntries
  if graphProjects.Count <> projectEntries.Length then fail "duplicate canonical projects in restore graph"
  if not (Map.containsKey project graphProjects) then fail "root project absent from restore graph"
  let mutable active = Set.empty
  let mutable visited = Set.empty
  let mutable rootLibraries = Set.empty
  let mutable rootPackages = Set.empty
  let mutable rootAssets: JsonNode = null
  let mutable rootExpectedFiles = Set.empty
  let mutable rootFramework = ""
  let mutable activeFrameworks = Set.empty
  let mutable evidence = []
  for evidencePath in [ host; bundledVersions ] do
    use stream = File.OpenRead(evidencePath)
    evidence <- (Convert.ToHexString(SHA256.HashData(stream)) + "  " + evidencePath) :: evidence
  let mutable projectOutputs: Map<string, string * string * string> = Map.empty
  let mutable frameworkManifests: Map<string, Map<string, XElement>> = Map.empty
  let rec visit path =
    if Set.contains path active then fail ("project cycle at " + path)
    if not (Set.contains path visited) then
      if path <> project && not (Set.contains path allowedProjects) then fail ("project not permitted: " + path)
      let spec = match Map.tryFind path graphProjects with Some value -> value | None -> fail ("project absent from graph: " + path)
      active <- Set.add path active
      let preprocessBefore, beforeHash = preprocess path "before" false
      let preprocessScrubbed, scrubbedHash = preprocess path "scrubbed" true
      if beforeHash <> scrubbedHash then fail ("preprocess depends on environment: " + path)
      let restore = field "restore" spec
      if canonical (text (field "projectPath" restore)) <> path then fail ("project identity mismatch: " + path)
      if path <> project then
        let arguments = [ path; "-property:Configuration=" + configuration; "-property:Platform=" + platform; "-getProperty:TargetPath,TargetRefPath,AssemblyName" ]
        let output = runMsbuild false arguments
        let scrubbedOutput = runMsbuild true arguments
        if not (JsonNode.DeepEquals(JsonNode.Parse(output), JsonNode.Parse(scrubbedOutput))) then fail ("project outputs depend on environment: " + path)
        let evaluated = JsonNode.Parse(output) |> field "Properties"
        let target = text (field "TargetPath" evaluated) |> canonical
        let reference = text (field "TargetRefPath" evaluated) |> canonical
        let assembly = text (field "AssemblyName" evaluated)
        if String.IsNullOrWhiteSpace assembly then fail ("missing referenced assembly identity: " + path)
        projectOutputs <- Map.add path (target, reference, assembly) projectOutputs
        let digest = SHA256.HashData(System.Text.Encoding.UTF8.GetBytes(output)) |> Convert.ToHexString
        evidence <- ("project-evaluation=" + path + ":" + digest) :: evidence
      let output = text (field "outputPath" restore)
      let assetsPath = Path.Combine(output, "project.assets.json")
      let assets = readJson assetsPath
      if not (JsonNode.DeepEquals(spec, field "project" assets)) then fail ("stale restore graph: " + path)
      let cache = readJson (Path.Combine(output, "project.nuget.cache"))
      if not ((field "success" cache).GetValue<bool>()) then fail ("unsuccessful restore cache: " + path)
      if canonical (text (field "projectFilePath" cache)) <> path then fail ("restore cache identity mismatch: " + path)
      let expectedFiles = field "expectedPackageFiles" cache |> arrayItems |> List.map text
      for expected in expectedFiles do
        if not (File.Exists expected) then fail ("missing restored package file: " + expected)
      for evidencePath in [ path; assetsPath; Path.Combine(output, "project.nuget.cache") ] do
        use stream = File.OpenRead(evidencePath)
        let digest = SHA256.HashData(stream) |> Convert.ToHexString
        evidence <- (digest + "  " + evidencePath) :: evidence
      let libraries = field "libraries" assets |> objectItems
      let packages = libraries |> List.choose (fun (identity, item) -> if text (field "type" item) = "package" then Some identity else None)
      if not (List.isEmpty packages) && List.isEmpty expectedFiles then fail ("restore cache has no package evidence: " + path)
      for identity in packages do
        let index = identity.LastIndexOf('/')
        if index <= 0 then fail ("invalid package identity: " + identity)
        let name = identity.Substring(0, index).ToUpperInvariant()
        if not (Set.contains name allowedPackages) then fail ("package not permitted: " + identity)
      let frameworks = field "frameworks" spec |> objectItems
      if List.length frameworks <> 1 then fail ("unsupported target framework count: " + path)
      let _, framework = List.head frameworks
      let frameworksUsed = field "frameworkReferences" framework |> objectItems |> List.map fst |> Set.ofList
      if not (Set.isSubset frameworksUsed (Set.singleton "Microsoft.NETCore.App")) then fail ("framework reference not permitted: " + path)
      activeFrameworks <- Set.union activeFrameworks frameworksUsed
      let direct =
        if isNull framework["dependencies"] then Set.empty
        else field "dependencies" framework |> objectItems |> List.map fst |> Set.ofList |> normalizedPackages
      if not (Set.isSubset direct allowedPackages) then fail ("direct package not permitted: " + path)
      if path = project then
        rootLibraries <- packages |> Set.ofList |> Set.map (fun value -> value.ToUpperInvariant())
        rootPackages <- direct
        rootAssets <- assets
        rootExpectedFiles <- expectedFiles |> List.map canonical |> Set.ofList
        rootFramework <- fst (List.head frameworks)
      let restoreFrameworks = field "frameworks" restore |> objectItems
      if List.length restoreFrameworks <> 1 then fail ("unsupported restore framework count: " + path)
      let _, restoreFramework = List.head restoreFrameworks
      let projectReferences = field "projectReferences" restoreFramework |> objectItems
      for _, reference in projectReferences do
        visit (canonical (text (field "projectPath" reference)))
      let preprocessAfter, afterHash = preprocess path "after" false
      if beforeHash <> afterHash then fail ("preprocess changed during evaluation: " + path)
      evidence <- (beforeHash + "  " + preprocessBefore) :: (scrubbedHash + "  " + preprocessScrubbed) :: (afterHash + "  " + preprocessAfter) :: evidence
      active <- Set.remove path active
      visited <- Set.add path visited
  visit project
  if rootPackages <> allowedPackages then fail "root direct packages differ from the owner-declared permitted set"
  let rows = field "Items" references |> field "ReferencePath" |> arrayItems
  if List.isEmpty rows then fail "empty ReferencePath"
  for row in rows do
    let identity = text (field "Identity" row)
    if String.IsNullOrWhiteSpace identity || not (File.Exists identity) then fail ("missing reference file: " + identity)
    evidence <- (fileDigest identity + "  " + canonical identity) :: evidence
    let source = optionalText "ReferenceSourceTarget" row
    let projectFile = optionalText "MSBuildSourceProjectFile" row
    let framework = optionalText "FrameworkReferenceName" row
    let package = optionalText "NuGetPackageId" row
    if source = "ProjectReference" then
      if String.IsNullOrWhiteSpace projectFile || not (String.IsNullOrWhiteSpace framework) then fail ("unclassifiable project reference: " + identity)
      let owner = canonical projectFile
      if not (Set.contains owner allowedProjects) || not (Set.contains owner visited) then fail ("project reference not permitted: " + owner)
      let singleTarget = optionalText "HasSingleTargetFramework" row
      if String.IsNullOrWhiteSpace singleTarget then fail ("missing HasSingleTargetFramework: " + owner)
      if singleTarget <> "true" then fail ("unsupported multi-target project reference: " + owner)
      let target, reference, assembly = match Map.tryFind owner projectOutputs with Some value -> value | None -> fail ("missing referenced project evaluation: " + owner)
      let referenceAssembly = text (field "ReferenceAssembly" row) |> canonical
      if canonical identity <> target || referenceAssembly <> reference then fail ("project output identity mismatch: " + owner)
      if AssemblyName.GetAssemblyName(identity).Name <> assembly then fail ("project assembly identity mismatch: " + owner)
    elif not (String.IsNullOrWhiteSpace framework) then
      if not (Set.contains framework activeFrameworks) then fail ("inactive framework reference: " + framework)
      let packId = text (field "NuGetPackageId" row)
      let packVersion = text (field "NuGetPackageVersion" row)
      let packs = field "Items" references |> field "ResolvedTargetingPack" |> arrayItems
      let matchingPacks =
        packs |> List.filter (fun pack ->
          optionalText "Identity" pack = framework && optionalText "NuGetPackageId" pack = packId &&
          optionalText "NuGetPackageVersion" pack = packVersion && optionalText "TargetFramework" pack = rootFramework)
      let pack = match matchingPacks with [ value ] -> value | _ -> fail ("missing or ambiguous targeting pack: " + framework)
      let packDigest = SHA256.HashData(System.Text.Encoding.UTF8.GetBytes(pack.ToJsonString())) |> Convert.ToHexString
      evidence <- ("targeting-pack=" + framework + ":" + packDigest) :: evidence
      let bundledName, bundledVersion = bundledFramework sdkDocument framework rootFramework
      if packId <> bundledName || packVersion <> bundledVersion then fail ("targeting pack version differs from bundled: " + framework)
      let packPath = text (field "Path" pack) |> canonical
      if canonical (text (field "PackageDirectory" pack)) <> packPath then fail ("targeting pack path mismatch: " + framework)
      let hostPack = Path.Combine(hostRoot, "packs", bundledName, bundledVersion) |> canonical
      if packPath <> hostPack then fail ("targeting pack not host-designated: " + framework)
      let frameworkList = Path.Combine(packPath, "data", "FrameworkList.xml")
      if not (File.Exists frameworkList) then fail ("missing targeting pack manifest: " + framework)
      let attribute name (element: XElement) =
        let value = element.Attribute(XName.Get(name))
        if isNull value then fail ("missing framework manifest attribute: " + name)
        value.Value
      let entries =
        match Map.tryFind frameworkList frameworkManifests with
        | Some value -> value
        | None ->
          let document = XDocument.Load(frameworkList)
          if isNull document.Root || attribute "FrameworkName" document.Root <> framework then fail ("framework manifest identity mismatch: " + framework)
          let rows =
            document.Root.Elements(XName.Get("File"))
            |> Seq.filter (fun entry -> attribute "Type" entry = "Managed")
            |> Seq.map (fun entry ->
              let relative = attribute "Path" entry
              if not (safeRelative relative) then fail ("invalid framework asset path: " + relative)
              let path = Path.Combine(packPath, relative)
              if not (File.Exists path) then fail ("missing framework asset: " + path)
              canonical path, entry)
            |> Seq.toList
          let value = Map.ofList rows
          if value.Count <> rows.Length then fail ("duplicate framework asset: " + framework)
          use stream = File.OpenRead(frameworkList)
          evidence <- (Convert.ToHexString(SHA256.HashData(stream)) + "  " + frameworkList) :: evidence
          frameworkManifests <- Map.add frameworkList value frameworkManifests
          value
      let entry = match Map.tryFind (canonical identity) entries with Some value -> value | None -> fail ("unverified framework asset: " + identity)
      let actual = AssemblyName.GetAssemblyName(identity)
      let token = actual.GetPublicKeyToken() |> Convert.ToHexString
      if actual.Name <> attribute "AssemblyName" entry || string actual.Version <> attribute "AssemblyVersion" entry ||
         not (String.Equals(token, attribute "PublicKeyToken" entry, StringComparison.OrdinalIgnoreCase)) then
        fail ("framework assembly identity mismatch: " + identity)
    elif source = "ResolveAssemblyReference" && not (String.IsNullOrWhiteSpace package) then
      let version = text (field "NuGetPackageVersion" row)
      let key = (package + "/" + version).ToUpperInvariant()
      if not (Set.contains key rootLibraries) || not (Set.contains (package.ToUpperInvariant()) allowedPackages) then fail ("package reference not permitted: " + key)
      let uniqueEntry label identity entries =
        match entries |> List.filter (fun (name, _) -> String.Equals(name, identity, StringComparison.OrdinalIgnoreCase)) with
        | [ _, value ] -> value
        | _ -> fail ("missing or ambiguous " + label + ": " + identity)
      let library = field "libraries" rootAssets |> objectItems |> uniqueEntry "package library" key
      let target = field "targets" rootAssets |> field rootFramework |> objectItems |> uniqueEntry "package target" key
      let packagePath = text (field "path" library)
      let assetPath = text (field "PathInPackage" row)
      if not (safeRelative packagePath && safeRelative assetPath) then fail ("invalid package asset path: " + key)
      let files = field "files" library |> arrayItems |> List.map text
      let compile = field "compile" target |> objectItems |> List.map fst
      if not (List.contains assetPath files && List.contains assetPath compile) then fail ("unverified package asset: " + identity)
      let hashFiles = files |> List.filter (fun value -> value.EndsWith(".nupkg.sha512", StringComparison.OrdinalIgnoreCase))
      let hashFile = match hashFiles with [ value ] when safeRelative value -> value | _ -> fail ("missing or ambiguous package hash: " + key)
      if not (List.contains ".nupkg.metadata" files) then fail ("missing package metadata declaration: " + key)
      let folders = field "packageFolders" rootAssets |> objectItems |> List.map fst
      let matches =
        folders |> List.choose (fun folder ->
          let asset = Path.Combine(folder, packagePath, assetPath)
          let hash = Path.Combine(folder, packagePath, hashFile)
          let metadata = Path.Combine(folder, packagePath, ".nupkg.metadata")
          if File.Exists asset && canonical asset = canonical identity then Some (hash, metadata) else None)
      match matches with
      | [ hash, metadata ] ->
        if not (File.Exists hash) then fail ("missing restore marker: " + key)
        if not (Set.contains (canonical hash) rootExpectedFiles) then fail ("restore marker not in cache: " + key)
        if not (File.Exists metadata) then fail ("missing package metadata: " + key)
        let contentHash = text (field "contentHash" (readJson metadata))
        if contentHash <> text (field "sha512" library) then fail ("package content hash mismatch: " + key)
        evidence <- ("package-content=" + key + ":" + contentHash) :: ("archive-marker=" + canonical hash) :: evidence
      | _ -> fail ("unverified package asset: " + identity)
    else fail ("unclassifiable reference: " + identity)
  File.WriteAllLines(manifestPath, [ "project=" + project; "projects=" + string visited.Count; "references=" + string rows.Length; "packages=" + String.Join(";", allowedPackages); "configuration=" + configuration; "platform=" + platform; "sdk-version=" + sdkVersion; "targeting-pack-root=" + targetingPackRoot ] @ List.rev evidence)
  printfn "Dependency closure verified: %d projects, %d references." visited.Count rows.Length

let arguments = fsi.CommandLineArgs |> Array.skip 1
match arguments with
| [| "--host" |] ->
  match Environment.ProcessPath |> Option.ofObj with
  | Some path when not (String.IsNullOrWhiteSpace path) -> printfn "%s" (canonical path)
  | _ -> fail "missing executing dotnet host"
| [| "--compare-graph"; normal; scrubbed |] ->
  if not (JsonNode.DeepEquals(readJson normal, readJson scrubbed)) then fail "restore graph depends on environment"
| [| "--compare-references"; normal; scrubbed |] -> compareReferences normal scrubbed
| [| "--check-owner-properties"; path |] -> checkOwnerProperties (readJson path)
| [| "--compare-preprocess"; before; after |] ->
  if fileDigest before <> fileDigest after then fail "preprocess changed during evaluation"
| [| "--check-sdk"; path; framework; targetFramework |] ->
  if not (File.Exists path) then fail "missing SDK bundled versions"
  let name, version = bundledFramework (XDocument.Load(path)) framework targetFramework
  printfn "%s/%s" name version
| [| "--dependencies"; project; graph; references; manifest |] -> validateDependencies project graph references manifest
| [| compileJson; output |] ->
  let document = JsonDocument.Parse(File.ReadAllText compileJson)
  let files =
    document.RootElement.GetProperty("Items").GetProperty("Compile").EnumerateArray()
    |> Seq.map (fun item ->
      match item.GetProperty("FullPath").GetString() |> Option.ofObj with
      | Some path when Path.IsPathFullyQualified(path) && File.Exists(path) -> Path.GetFullPath(path)
      | _ -> failwith "An evaluated Compile item has no existing absolute path.")
    |> Seq.toList
  if files.IsEmpty then failwith "The evaluated project has no Compile items."
  if files.Length <> (files |> List.distinct |> List.length) then failwith "The evaluated project repeats a Compile item."
  File.WriteAllLines(output, files |> List.sort)
| _ -> failwith "Expected evaluated Compile JSON and output path, or --dependencies project graph references manifest."
