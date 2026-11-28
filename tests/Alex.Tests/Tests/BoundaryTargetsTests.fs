module Alex.Tests.BoundaryTargetsTests

open System
open System.Diagnostics
open System.IO
open System.Security
open System.Text.Json
open System.Xml.Linq
open Xunit

let private repoRoot =
    Path.GetFullPath(Path.Combine(__SOURCE_DIRECTORY__, "../../.."))

let private boundaryTargetsPath =
    Path.Combine(repoRoot, "build", "Boundary.targets")

let private taskSourcePath =
    Path.Combine(repoRoot, "build", "Alex.Boundary.Tasks", "ValidateAlexBoundary.cs")

let private taskProjectPath =
    Path.Combine(repoRoot, "build", "Alex.Boundary.Tasks", "Alex.Boundary.Tasks.csproj")

let private runMsbuild (workingDir: string) (projectPath: string) (args: string list) =
    let dotnetHost =
        match Environment.ProcessPath with
        | null | "" -> "dotnet"
        | host when Path.GetFileNameWithoutExtension(host).Equals("dotnet", StringComparison.OrdinalIgnoreCase) -> host
        | _ -> "dotnet"
    let psi = ProcessStartInfo(dotnetHost)
    psi.WorkingDirectory <- workingDir
    psi.UseShellExecute <- false
    psi.RedirectStandardOutput <- true
    psi.RedirectStandardError <- true
    psi.Environment["MSBUILDDISABLENODEREUSE"] <- "1"
    for arg in ("msbuild" :: "-nologo" :: "-noAutoResponse" :: projectPath :: args) do
        psi.ArgumentList.Add(arg)
    use proc = Process.Start(psi)
    Assert.NotNull(proc)
    let stdoutTask = proc.StandardOutput.ReadToEndAsync()
    let stderrTask = proc.StandardError.ReadToEndAsync()
    if not (proc.WaitForExit(60000)) then
        proc.Kill(true)
        proc.WaitForExit(5000) |> ignore
        failwithf "MSBuild timed out for %s" projectPath
    let combined = stdoutTask.GetAwaiter().GetResult() + "\n" + stderrTask.GetAwaiter().GetResult()
    proc.ExitCode, combined

let private withScratch (run: string -> unit) =
    let dir = Path.Combine(Path.GetTempPath(), "alex-boundary-tests-" + Guid.NewGuid().ToString("N"))
    Directory.CreateDirectory(dir) |> ignore
    try
        run dir
    finally
        if Directory.Exists(dir) then
            Directory.Delete(dir, true)

let private writeHarness (targetsPath: string) (harnessDir: string) =
    let dummySource = Path.Combine(harnessDir, "Dummy.fs")
    File.WriteAllText(dummySource, "module Dummy\nlet ok = 1\n")
    let harnessPath = Path.Combine(harnessDir, "Harness.proj")
    let escapedTargets = SecurityElement.Escape(targetsPath)
    let xml =
        sprintf
            """<Project>
  <PropertyGroup>
    <AlexBoundaryScope>library</AlexBoundaryScope>
    <PsgContractProject>$(TestPermittedPrimary)</PsgContractProject>
    <PsgContractLibrary>$(TestPermittedLibrary)</PsgContractLibrary>
  </PropertyGroup>
  <Import Project="%s" />
  <ItemGroup>
    <Compile Include="$(MSBuildThisFileDirectory)Dummy.fs" />
    <ProjectReference Include="$(TestRef)" />
  </ItemGroup>
  <Target Name="CoreCompile" />
</Project>"""
            escapedTargets
    File.WriteAllText(harnessPath, xml)
    harnessPath

let private setupSymlinkTopology (scratch: string) =
    let realRepos = Path.Combine(scratch, "real-repos")
    let nonSiblingAlexRoot = Path.Combine(scratch, "storage-a", "Alex")
    let nonSiblingBareWireRoot = Path.Combine(scratch, "storage-b", "BAREWire")
    let nonSiblingBareWireDir = Path.Combine(nonSiblingBareWireRoot, "src")
    let linkRepos = Path.Combine(scratch, "link-repos")
    let relLinkRepos = Path.Combine(scratch, "rel-link-repos")
    let psgDir = Path.Combine(realRepos, "Fidelity.PSG", "src", "Fidelity.PSG")
    let bareWireDir = Path.Combine(realRepos, "BAREWire", "src")
    let alexDir = Path.Combine(realRepos, "Alex")
    let foreignDir = Path.Combine(realRepos, "Foreign")
    for d in [ psgDir; bareWireDir; alexDir; foreignDir; nonSiblingAlexRoot; nonSiblingBareWireDir; linkRepos; relLinkRepos ] do
        Directory.CreateDirectory(d) |> ignore
    let realPsg = Path.Combine(psgDir, "Fidelity.PSG.fsproj")
    let realBareWire = Path.Combine(bareWireDir, "BAREWire.fsproj")
    let realNonSiblingBareWire = Path.Combine(nonSiblingBareWireDir, "BAREWire.fsproj")
    let realForeign = Path.Combine(foreignDir, "Foreign.fsproj")
    for f in [ realPsg; realBareWire; realNonSiblingBareWire; realForeign ] do
        File.WriteAllText(f, "<Project />")
    Directory.CreateSymbolicLink(Path.Combine(linkRepos, "Fidelity.PSG"), Path.Combine(realRepos, "Fidelity.PSG")) |> ignore
    Directory.CreateSymbolicLink(Path.Combine(linkRepos, "BAREWire"), Path.Combine(realRepos, "BAREWire")) |> ignore
    Directory.CreateSymbolicLink(Path.Combine(linkRepos, "Alex"), alexDir) |> ignore
    Directory.CreateSymbolicLink(Path.Combine(linkRepos, "NonSiblingAlex"), nonSiblingAlexRoot) |> ignore
    Directory.CreateSymbolicLink(Path.Combine(linkRepos, "NonSiblingBAREWire"), nonSiblingBareWireRoot) |> ignore
    Directory.CreateSymbolicLink(Path.Combine(linkRepos, "Foreign"), foreignDir) |> ignore
    Directory.CreateSymbolicLink(Path.Combine(relLinkRepos, "BAREWire"), Path.Combine("..", "real-repos", "BAREWire")) |> ignore
    File.CreateSymbolicLink(Path.Combine(linkRepos, "SpoofBAREWire.fsproj"), realForeign) |> ignore
    let loopA = Path.Combine(linkRepos, "LoopA")
    let loopB = Path.Combine(linkRepos, "LoopB")
    Directory.CreateSymbolicLink(loopA, loopB) |> ignore
    Directory.CreateSymbolicLink(loopB, loopA) |> ignore
    realPsg, realBareWire, realNonSiblingBareWire, realForeign, linkRepos, relLinkRepos, loopA

[<Fact>]
let ``ALEX002 positive controls: CheckAlexBoundary accepts real symlinked repo paths`` () =
    withScratch (fun scratch ->
        let realPsg, realBareWire, realNonSiblingBareWire, _, linkRepos, relLinkRepos, _ = setupSymlinkTopology scratch
        let linkPsg = Path.Combine(linkRepos, "Fidelity.PSG", "src", "Fidelity.PSG", "Fidelity.PSG.fsproj")
        let linkBareWire = Path.Combine(linkRepos, "BAREWire", "src", "BAREWire.fsproj")
        let dotDotBareWire = Path.Combine(linkRepos, "Alex", "..", "BAREWire", "src", "BAREWire.fsproj")
        let nonSiblingDotDotBareWire = Path.Combine(linkRepos, "NonSiblingAlex", "..", "NonSiblingBAREWire", "src", "BAREWire.fsproj")
        let relLinkBareWire = Path.Combine(relLinkRepos, "BAREWire", "src", "BAREWire.fsproj")
        // Verify lexical Path.GetFullPath actually differs on the THREE-style symlink topology.
        Assert.NotEqual<string>(Path.GetFullPath(linkBareWire), Path.GetFullPath(realBareWire))
        let harness = writeHarness boundaryTargetsPath scratch
        let cases =
            [ "three-symlink-permitted-vs-real-ref", linkPsg, linkBareWire, realBareWire
              "real-permitted-vs-symlink-ref", realPsg, realBareWire, linkBareWire
              "dotdot-after-symlink-dir", linkPsg, dotDotBareWire, realBareWire
              "non-sibling-dotdot-after-symlink-dir", linkPsg, nonSiblingDotDotBareWire, realNonSiblingBareWire
              "relative-symlink-dir", linkPsg, relLinkBareWire, realBareWire ]
        for label, permPsg, permLib, refPath in cases do
            let exitCode, output =
                runMsbuild scratch harness
                    [ "-target:CheckAlexBoundary"
                      "-property:TestPermittedPrimary=" + permPsg
                      "-property:TestPermittedLibrary=" + permLib
                      "-property:TestRef=" + refPath ]
            Assert.True((exitCode = 0), sprintf "Expected PASS for %s, got exit %d:\n%s" label exitCode output))

[<Fact>]
let ``ALEX002 design-time controls: DesignTimeBuild enforces ALEX002 and the check stays active under SkipCompilerExecution`` () =
    withScratch (fun scratch ->
        let _, _, _, realForeign, linkRepos, _, _ = setupSymlinkTopology scratch
        let linkPsg = Path.Combine(linkRepos, "Fidelity.PSG", "src", "Fidelity.PSG", "Fidelity.PSG.fsproj")
        let linkBareWire = Path.Combine(linkRepos, "BAREWire", "src", "BAREWire.fsproj")
        let harness = writeHarness boundaryTargetsPath scratch
        let refusalText = "Alex references the published PSG contract and the library the contract references. No other project is permitted."
        // DesignTimeBuild=true WITHOUT SkipCompilerExecution=true still executes CoreCompile and MUST enforce ALEX002.
        let enforcedExit, enforcedOutput =
            runMsbuild scratch harness
                [ "-target:CheckAlexBoundary"
                  "-property:DesignTimeBuild=true"
                  "-property:TestPermittedPrimary=" + linkPsg
                  "-property:TestPermittedLibrary=" + linkBareWire
                  "-property:TestRef=" + realForeign ]
        Assert.True((enforcedExit <> 0), sprintf "Expected DesignTimeBuild=true without SkipCompilerExecution to fail with ALEX002, got exit 0:\n%s" enforcedOutput)
        Assert.Contains("error ALEX002:", enforcedOutput)
        Assert.Contains(refusalText, enforcedOutput)
        // DesignTimeBuild=true WITH SkipCompilerExecution=true: compilation is skipped, but the boundary task
        // assembly already exists, so the check still runs and still refuses the unpermitted reference.
        let skippedExit, skippedOutput =
            runMsbuild scratch harness
                [ "-target:CheckAlexBoundary"
                  "-property:DesignTimeBuild=true"
                  "-property:SkipCompilerExecution=true"
                  "-property:TestPermittedPrimary=" + linkPsg
                  "-property:TestPermittedLibrary=" + linkBareWire
                  "-property:TestRef=" + realForeign ]
        Assert.True((skippedExit <> 0), sprintf "Expected the boundary check to stay active with SkipCompilerExecution=true while the task assembly exists, got exit %d:\n%s" skippedExit skippedOutput)
        Assert.Contains("error ALEX002:", skippedOutput)
        Assert.Contains(refusalText, skippedOutput))

[<Fact>]
let ``ALEX002 exact-reason negative controls: unpermitted direct, symlinked, spoofed, and cyclic paths fail`` () =
    withScratch (fun scratch ->
        let _, realBareWire, _, realForeign, linkRepos, _, loopA = setupSymlinkTopology scratch
        let linkPsg = Path.Combine(linkRepos, "Fidelity.PSG", "src", "Fidelity.PSG", "Fidelity.PSG.fsproj")
        let linkBareWire = Path.Combine(linkRepos, "BAREWire", "src", "BAREWire.fsproj")
        let linkForeign = Path.Combine(linkRepos, "Foreign", "Foreign.fsproj")
        let spoofBareWire = Path.Combine(linkRepos, "SpoofBAREWire.fsproj")
        let cyclicRef = Path.Combine(loopA, "BAREWire.fsproj")
        let harness = writeHarness boundaryTargetsPath scratch
        let refusalText = "Alex references the published PSG contract and the library the contract references. No other project is permitted."
        let unpermittedCases =
            [ "direct-unpermitted", linkPsg, linkBareWire, realForeign
              "symlink-unpermitted", linkPsg, linkBareWire, linkForeign
              "spoofed-name-symlink-to-foreign", linkPsg, realBareWire, spoofBareWire ]
        for label, permPsg, permLib, refPath in unpermittedCases do
            let exitCode, output =
                runMsbuild scratch harness
                    [ "-target:CheckAlexBoundary"
                      "-property:TestPermittedPrimary=" + permPsg
                      "-property:TestPermittedLibrary=" + permLib
                      "-property:TestRef=" + refPath ]
            Assert.True(exitCode <> 0, sprintf "Expected ALEX002 refusal for %s, got exit 0:\n%s" label output)
            Assert.Contains("error ALEX002:", output)
            Assert.Contains(refusalText, output)
        // Cyclic symlink must fail explicitly with ALEX002 canonicalization error (never silently fall back).
        let cyclicExit, cyclicOutput =
            runMsbuild scratch harness
                [ "-target:CheckAlexBoundary"
                  "-property:TestPermittedPrimary=" + linkPsg
                  "-property:TestPermittedLibrary=" + linkBareWire
                  "-property:TestRef=" + cyclicRef ]
        Assert.True(cyclicExit <> 0, sprintf "Expected explicit canonicalization failure for cyclic symlink, got exit 0:\n%s" cyclicOutput)
        Assert.Contains("error ALEX002:", cyclicOutput)
        Assert.Contains("Failed to canonicalize project reference", cyclicOutput))

[<Fact>]
let ``ALEX002 fault-injection control: disabling symlink canonicalization rejects the THREE symlink positive`` () =
    withScratch (fun scratch ->
        let _, realBareWire, _, _, linkRepos, _, _ = setupSymlinkTopology scratch
        let linkPsg = Path.Combine(linkRepos, "Fidelity.PSG", "src", "Fidelity.PSG", "Fidelity.PSG.fsproj")
        let linkBareWire = Path.Combine(linkRepos, "BAREWire", "src", "BAREWire.fsproj")
        // Build a fault-injected copy of the boundary task where TryCanonicalPath is weakened to lexical Path.GetFullPath.
        let faultDir = Path.Combine(scratch, "fault-build")
        let faultTaskDir = Path.Combine(faultDir, "Alex.Boundary.Tasks")
        Directory.CreateDirectory(faultTaskDir) |> ignore
        File.Copy(taskProjectPath, Path.Combine(faultTaskDir, "Alex.Boundary.Tasks.csproj"))
        let originalSource = File.ReadAllText(taskSourcePath)
        let needle = "private static bool TryCanonicalPath(string raw, out string canonical, out string error)"
        let startIndex = originalSource.IndexOf(needle, StringComparison.Ordinal)
        let executeIndex = originalSource.IndexOf("public override bool Execute()", StringComparison.Ordinal)
        Assert.True(startIndex >= 0 && executeIndex > startIndex, "Expected TryCanonicalPath method before Execute()")
        let mutatedSource =
            originalSource.Substring(0, startIndex)
            + "private static bool TryCanonicalPath(string raw, out string canonical, out string error) { canonical = Path.GetFullPath(raw); error = string.Empty; return true; }\n\n        "
            + originalSource.Substring(executeIndex)
        File.WriteAllText(Path.Combine(faultTaskDir, "ValidateAlexBoundary.cs"), mutatedSource)
        let faultTargets = Path.Combine(faultDir, "Boundary.targets")
        File.Copy(boundaryTargetsPath, faultTargets)
        let harness = writeHarness faultTargets scratch
        let exitCode, output =
            runMsbuild scratch harness
                [ "-target:CheckAlexBoundary"
                  "-property:TestPermittedPrimary=" + linkPsg
                  "-property:TestPermittedLibrary=" + linkBareWire
                  "-property:TestRef=" + realBareWire ]
        Assert.True(exitCode <> 0, sprintf "Expected fault-injected lexical task to fail with ALEX002, got exit 0:\n%s" output)
        Assert.Contains("error ALEX002:", output)
        Assert.Contains("Alex references the published PSG contract and the library the contract references. No other project is permitted.", output))

let private taskAssemblyPath =
    Path.Combine(repoRoot, "build", "Alex.Boundary.Tasks", "bin", "Debug", "net10.0", "Alex.Boundary.Tasks.dll")

// Harness that supplies only a source probe: the source scans decide ALEX001, ALEX003 and ALEX004
// from @(Compile), so no project reference is needed for them.
let private writeScanHarness (targetsPath: string) (harnessDir: string) (source: string) =
    File.WriteAllText(Path.Combine(harnessDir, "BoundaryProbe.fs"), source)
    let harnessPath = Path.Combine(harnessDir, "ScanHarness.proj")
    let escapedTargets = SecurityElement.Escape(targetsPath)
    let xml =
        sprintf
            """<Project>
  <PropertyGroup>
    <AlexBoundaryScope>library</AlexBoundaryScope>
  </PropertyGroup>
  <Import Project="%s" />
  <ItemGroup>
    <Compile Include="$(MSBuildThisFileDirectory)BoundaryProbe.fs" />
  </ItemGroup>
  <Target Name="CoreCompile" />
</Project>"""
            escapedTargets
    File.WriteAllText(harnessPath, xml)
    harnessPath

// Compiler-service and LLVM-dialect probe strings are split across literals so this test file
// does not trigger ALEX001 (active in tests scope) or embed raw LLVM emission syntax;
// "--pass-pipeline" is a process marker permitted in tests scope.
let private cleanProbeSource = "module BoundaryProbe\nlet ok = 1\n"

let private violatingProbeSource =
    "module BoundaryProbe\n"
    + "let service = " + "Clef" + "." + "Compiler.emit 1\n"
    + "let pipeline = \"--pass-pipeline\"\n"
    + "let emission = sprintf \"" + "llvm" + ".func\"\n"

// A targets copy whose task assembly path deliberately does not exist, for the guard-necessity control.
let private taskAssemblyAbsentTargets (targetsPath: string) (scratch: string) =
    let needle = "<_AlexBoundaryTaskAssembly>$(MSBuildThisFileDirectory)Alex.Boundary.Tasks/bin/Debug/net10.0/Alex.Boundary.Tasks.dll</_AlexBoundaryTaskAssembly>"
    let text = File.ReadAllText(targetsPath)
    let mutated =
        text.Replace(needle, "<_AlexBoundaryTaskAssembly>" + Path.Combine(scratch, "absent", "Alex.Boundary.Tasks.dll") + "</_AlexBoundaryTaskAssembly>")
    Assert.True(mutated <> text, "Expected to relocate the boundary task assembly path in the fault targets copy.")
    let path = Path.Combine(scratch, "Boundary.absent.targets")
    File.WriteAllText(path, mutated)
    path

let private alex001Reason = "Alex reads a published PSG revision only. This line names the compiler service."
let private alex003Reason = "Prohibited rewrite, process or plugin entry '--pass-pipeline'. Alex witnesses settled facts and emits once."
let private alex004Reason = "LLVM dialect emission belongs to backend realization, never Alex portable output."

[<Fact>]
let ``ALEX001/003/004 source scans stay active under SkipCompilerExecution when the task assembly exists`` () =
    withScratch (fun scratch ->
        Assert.True(File.Exists(taskAssemblyPath), sprintf "Expected the built boundary task assembly at %s before the SkipCompilerExecution scan control." taskAssemblyPath)

        // Positive control: a clean probe passes with compilation skipped.
        let cleanHarness = writeScanHarness boundaryTargetsPath scratch cleanProbeSource
        let cleanExit, cleanOutput =
            runMsbuild scratch cleanHarness
                [ "-target:CheckAlexBoundary"; "-property:SkipCompilerExecution=true" ]
        Assert.True((cleanExit = 0), sprintf "Expected a clean probe to pass with SkipCompilerExecution=true, got exit %d:\n%s" cleanExit cleanOutput)
        for code in [ "ALEX001"; "ALEX003"; "ALEX004" ] do
            Assert.DoesNotContain("error " + code, cleanOutput)

        // Exact-reason negative control: the same scan still catches every source violation.
        let probeHarness = writeScanHarness boundaryTargetsPath scratch violatingProbeSource
        let probeExit, probeOutput =
            runMsbuild scratch probeHarness
                [ "-target:CheckAlexBoundary"; "-property:SkipCompilerExecution=true" ]
        Assert.True(probeExit <> 0, sprintf "Expected the source scan to run and fail with SkipCompilerExecution=true, got exit 0:\n%s" probeOutput)
        Assert.Contains("error ALEX001: " + alex001Reason, probeOutput)
        Assert.Contains("error ALEX003: " + alex003Reason, probeOutput)
        Assert.Contains("error ALEX004: " + alex004Reason, probeOutput)

        // Guard-necessity control: with the skip flag set and no task assembly present the target is skipped,
        // a high-importance message records the skip, and the violation is not checked.
        let absentTargets = taskAssemblyAbsentTargets boundaryTargetsPath scratch
        let absentHarness = writeScanHarness absentTargets scratch violatingProbeSource
        let absentExit, absentOutput =
            runMsbuild scratch absentHarness
                [ "-target:CheckAlexBoundary"; "-property:SkipCompilerExecution=true" ]
        Assert.True((absentExit = 0), sprintf "Expected the scan to be skipped when the task assembly is absent, got exit %d:\n%s" absentExit absentOutput)
        Assert.Contains("Alex boundary check (ALEX001-ALEX004) skipped: SkipCompilerExecution=true and boundary task assembly", absentOutput)
        for code in [ "ALEX001"; "ALEX003"; "ALEX004" ] do
            Assert.DoesNotContain("error " + code, absentOutput))

[<Fact>]
let ``Fault-injection control: the scan executed under SkipCompilerExecution, it did not silently pass`` () =
    withScratch (fun scratch ->
        let faultDir = Path.Combine(scratch, "fault-build")
        let faultTaskDir = Path.Combine(faultDir, "Alex.Boundary.Tasks")
        Directory.CreateDirectory(faultTaskDir) |> ignore
        File.Copy(taskProjectPath, Path.Combine(faultTaskDir, "Alex.Boundary.Tasks.csproj"))
        let originalSource = File.ReadAllText(taskSourcePath)
        let needle = "if (compilerService.IsMatch(line))"
        Assert.True(originalSource.Contains(needle), "Expected the ALEX001 detector in the boundary task source.")
        File.WriteAllText(
            Path.Combine(faultTaskDir, "ValidateAlexBoundary.cs"),
            originalSource.Replace(needle, "if (false && compilerService.IsMatch(line))"))
        let faultTargets = Path.Combine(faultDir, "Boundary.targets")
        File.Copy(boundaryTargetsPath, faultTargets)
        let harness = writeScanHarness faultTargets scratch violatingProbeSource

        // Build the fault-injected task, then run the scan with compilation skipped.
        let buildExit, buildOutput = runMsbuild scratch harness [ "-target:CheckAlexBoundary" ]
        Assert.True(buildExit <> 0, sprintf "Expected the fault-injected scan to fail, got exit 0:\n%s" buildOutput)
        Assert.DoesNotContain("error ALEX001:", buildOutput)
        Assert.Contains("error ALEX003: " + alex003Reason, buildOutput)
        Assert.Contains("error ALEX004: " + alex004Reason, buildOutput)

        let skipExit, skipOutput =
            runMsbuild scratch harness
                [ "-target:CheckAlexBoundary"; "-property:SkipCompilerExecution=true" ]
        Assert.True(skipExit <> 0, sprintf "Expected the scan to run with SkipCompilerExecution=true, got exit 0:\n%s" skipOutput)
        Assert.DoesNotContain("error ALEX001:", skipOutput)
        Assert.Contains("error ALEX003: " + alex003Reason, skipOutput)
        Assert.Contains("error ALEX004: " + alex004Reason, skipOutput))

let private alexProjectPath =
    Path.Combine(repoRoot, "src", "Alex", "Alex.fsproj")

let private alexTestsProjectPath =
    Path.Combine(repoRoot, "tests", "Alex.Tests", "Alex.Tests.fsproj")

let private copyBoundaryBuildTree (destDir: string) =
    let taskDir = Path.Combine(destDir, "Alex.Boundary.Tasks")
    Directory.CreateDirectory(taskDir) |> ignore
    let destTargets = Path.Combine(destDir, "Boundary.targets")
    let destCsproj = Path.Combine(taskDir, "Alex.Boundary.Tasks.csproj")
    let destSource = Path.Combine(taskDir, "ValidateAlexBoundary.cs")
    let destDll = Path.Combine(taskDir, "bin", "Debug", "net10.0", "Alex.Boundary.Tasks.dll")
    File.Copy(boundaryTargetsPath, destTargets)
    File.Copy(taskProjectPath, destCsproj)
    File.Copy(taskSourcePath, destSource)
    destTargets, destCsproj, destSource, destDll

let private splitSemicolon (raw: string) =
    raw.Split(';', StringSplitOptions.RemoveEmptyEntries ||| StringSplitOptions.TrimEntries)

let private attrValue (name: string) (el: XElement) =
    match el.Attribute(XName.Get name) with
    | null -> ""
    | a -> a.Value

[<Fact>]
let ``Nested MSBuild isolation and reentry guard isolate Alex.Boundary.Tasks from outer build properties`` () =
    // Structural XML check on Boundary.targets and Alex.Boundary.Tasks.csproj.
    let targetsDoc = XDocument.Load(boundaryTargetsPath)
    let buildTaskTarget =
        targetsDoc.Descendants()
        |> Seq.filter (fun el -> el.Name.LocalName = "Target" && attrValue "Name" el = "BuildAlexBoundaryTask")
        |> Seq.exactlyOne
    let nestedCalls =
        buildTaskTarget.Elements()
        |> Seq.filter (fun el -> el.Name.LocalName = "MSBuild")
        |> Seq.toList
    Assert.Equal(2, nestedCalls.Length)
    let requiredRemoved =
        [ "OutputPath"; "OutDir"; "BaseOutputPath"; "RuntimeIdentifier"; "TargetFramework"; "SkipCompilerExecution"; "DesignTimeBuild" ]
    for callEl in nestedCalls do
        let removeAttr = callEl.Attribute(XName.Get "RemoveProperties")
        Assert.NotNull(removeAttr)
        let removedSet = splitSemicolon removeAttr.Value |> Set.ofArray
        for prop in requiredRemoved do
            Assert.Contains(prop, removedSet)
        let propsAttr = callEl.Attribute(XName.Get "Properties")
        Assert.NotNull(propsAttr)
        let propsSet = splitSemicolon propsAttr.Value |> Set.ofArray
        Assert.Contains("_SkipAlexBoundaryCheck=true", propsSet)
    let taskDoc = XDocument.Load(taskProjectPath)
    let taskImports =
        taskDoc.Descendants()
        |> Seq.filter (fun el -> el.Name.LocalName = "Import")
        |> Seq.map (fun el -> match el.Attribute(XName.Get "Project") with null -> "" | a -> a.Value)
        |> Seq.toList
    Assert.DoesNotContain(taskImports, fun p -> p.Contains("Boundary.targets", StringComparison.OrdinalIgnoreCase))

    // Behavioral control: hostile outer build properties must not redirect Alex.Boundary.Tasks output
    // or prevent CheckAlexBoundary from loading the isolated task assembly.
    withScratch (fun scratch ->
        let isolatedDir = Path.Combine(scratch, "isolated")
        let targetsCopy, _, _, expectedDll = copyBoundaryBuildTree isolatedDir
        let outerOut = Path.Combine(scratch, "outer-out") + string Path.DirectorySeparatorChar
        let outerBase = Path.Combine(scratch, "outer-obj") + string Path.DirectorySeparatorChar
        let cleanHarness = writeScanHarness targetsCopy scratch cleanProbeSource
        let passExit, passOutput =
            runMsbuild scratch cleanHarness
                [ "-target:CheckAlexBoundary"
                  "-property:OutputPath=" + outerOut
                  "-property:OutDir=" + outerOut
                  "-property:BaseOutputPath=" + outerBase
                  "-property:RuntimeIdentifier=linux-x64"
                  "-property:TargetFramework=net10.0"
                  "-property:DesignTimeBuild=true" ]
        Assert.True((passExit = 0), sprintf "Expected isolated nested build to succeed under hostile outer properties, got exit %d:\n%s" passExit passOutput)
        Assert.True(File.Exists(expectedDll), sprintf "Expected isolated task DLL at %s" expectedDll)
        Assert.False(File.Exists(Path.Combine(outerOut, "Alex.Boundary.Tasks.dll")), "Nested task build leaked into outer OutputPath.")

        // Fault-injection control: removing RemoveProperties allows hostile outer OutputPath/OutDir to hijack
        // the nested task build away from _AlexBoundaryTaskAssembly so CheckAlexBoundary fails to load the task.
        let unisolatedDir = Path.Combine(scratch, "unisolated")
        let unisolatedTargets, _, _, unisolatedDll = copyBoundaryBuildTree unisolatedDir
        let unisolatedText =
            File.ReadAllText(unisolatedTargets)
                .Replace("RemoveProperties=\"OutputPath;OutDir;BaseOutputPath;RuntimeIdentifier;TargetFramework;SkipCompilerExecution;DesignTimeBuild\"", "")
        File.WriteAllText(unisolatedTargets, unisolatedText)
        let faultOut = Path.Combine(scratch, "fault-out") + string Path.DirectorySeparatorChar
        let faultHarness = writeScanHarness unisolatedTargets scratch cleanProbeSource
        let faultExit, faultOutput =
            runMsbuild scratch faultHarness
                [ "-target:CheckAlexBoundary"
                  "-property:OutputPath=" + faultOut
                  "-property:OutDir=" + faultOut ]
        Assert.True(faultExit <> 0, sprintf "Expected unisolated nested build with hostile OutputPath to fail loading task assembly, got exit 0:\n%s" faultOutput)
        Assert.Contains("MSB4062", faultOutput)
        Assert.Contains("Alex.Boundary.Tasks.dll", faultOutput)
        Assert.False(File.Exists(unisolatedDll), "Unisolated build should not have emitted into the canonical task path.")
        Assert.True(File.Exists(Path.Combine(faultOut, "Alex.Boundary.Tasks.dll")), "Expected unisolated nested build to redirect Alex.Boundary.Tasks.dll into hostile OutputPath."))

[<Fact>]
let ``VerifyAlexBoundaryTaskFreshness refuses stale boundary task DLLs under SkipCompilerExecution`` () =
    withScratch (fun scratch ->
        let copyDir = Path.Combine(scratch, "freshness")
        let targetsCopy, csprojCopy, sourceCopy, dllCopy = copyBoundaryBuildTree copyDir
        let cleanHarness = writeScanHarness targetsCopy scratch cleanProbeSource
        // Build fresh task assembly.
        let buildExit, buildOutput = runMsbuild scratch cleanHarness [ "-target:CheckAlexBoundary" ]
        Assert.True((buildExit = 0), sprintf "Expected initial task build to succeed, got exit %d:\n%s" buildExit buildOutput)
        Assert.True(File.Exists(dllCopy), "Expected built task assembly.")
        let originalSourceTime = File.GetLastWriteTimeUtc(sourceCopy)
        let originalCsprojTime = File.GetLastWriteTimeUtc(csprojCopy)
        let dllTime = File.GetLastWriteTimeUtc(dllCopy)

        // Positive control: fresh DLL passes under SkipCompilerExecution=true.
        let freshExit, freshOutput =
            runMsbuild scratch cleanHarness
                [ "-target:CheckAlexBoundary"; "-property:SkipCompilerExecution=true" ]
        Assert.True((freshExit = 0), sprintf "Expected fresh task DLL to pass under SkipCompilerExecution=true, got exit %d:\n%s" freshExit freshOutput)

        // Exact-reason negative control 1: ValidateAlexBoundary.cs newer than DLL is refused.
        File.SetLastWriteTimeUtc(sourceCopy, dllTime.AddSeconds(10.0))
        let staleSourceExit, staleSourceOutput =
            runMsbuild scratch cleanHarness
                [ "-target:CheckAlexBoundary"; "-property:SkipCompilerExecution=true" ]
        Assert.True(staleSourceExit <> 0, sprintf "Expected stale ValidateAlexBoundary.cs to fail, got exit 0:\n%s" staleSourceOutput)
        Assert.Contains("is stale relative to", staleSourceOutput)
        Assert.Contains("ValidateAlexBoundary.cs", staleSourceOutput)
        File.SetLastWriteTimeUtc(sourceCopy, originalSourceTime)

        // Exact-reason negative control 2: Alex.Boundary.Tasks.csproj newer than DLL is refused.
        File.SetLastWriteTimeUtc(csprojCopy, dllTime.AddSeconds(10.0))
        let staleCsprojExit, staleCsprojOutput =
            runMsbuild scratch cleanHarness
                [ "-target:CheckAlexBoundary"; "-property:SkipCompilerExecution=true" ]
        Assert.True(staleCsprojExit <> 0, sprintf "Expected stale Alex.Boundary.Tasks.csproj to fail, got exit 0:\n%s" staleCsprojOutput)
        Assert.Contains("is stale relative to", staleCsprojOutput)
        Assert.Contains("Alex.Boundary.Tasks.csproj", staleCsprojOutput)

        // Fault-injection control: disabling VerifyAlexBoundaryTaskFreshness allows the stale DLL to pass silently.
        let disabledTargets = Path.Combine(copyDir, "Boundary.nofresh.targets")
        let mutatedDoc = XDocument.Load(targetsCopy)
        for t in mutatedDoc.Descendants() |> Seq.filter (fun el -> el.Name.LocalName = "Target" && attrValue "Name" el = "VerifyAlexBoundaryTaskFreshness") do
            t.SetAttributeValue(XName.Get "Condition", "false")
        mutatedDoc.Save(disabledTargets)
        let faultHarness = writeScanHarness disabledTargets scratch cleanProbeSource
        let faultExit, faultOutput =
            runMsbuild scratch faultHarness
                [ "-target:CheckAlexBoundary"; "-property:SkipCompilerExecution=true" ]
        Assert.True((faultExit = 0), sprintf "Expected disabled freshness check to silently accept stale DLL, got exit %d:\n%s" faultExit faultOutput)
        File.SetLastWriteTimeUtc(csprojCopy, originalCsprojTime))

[<Fact>]
let ``CoreCompile design-time hook enforces boundary and reverted-condition fault lets violations escape`` () =
    // Real-project CoreCompile check on src/Alex/Alex.fsproj with DesignTimeBuild=true + SkipCompilerExecution=true.
    let realExit, realOutput =
        runMsbuild repoRoot alexProjectPath
            [ "-target:CoreCompile"
              "-property:DesignTimeBuild=true"
              "-property:SkipCompilerExecution=true" ]
    Assert.True((realExit = 0), sprintf "Expected real src/Alex/Alex.fsproj design-time CoreCompile to pass, got exit %d:\n%s" realExit realOutput)

    withScratch (fun scratch ->
        let _, _, _, realForeign, linkRepos, _, _ = setupSymlinkTopology scratch
        let linkPsg = Path.Combine(linkRepos, "Fidelity.PSG", "src", "Fidelity.PSG", "Fidelity.PSG.fsproj")
        let linkBareWire = Path.Combine(linkRepos, "BAREWire", "src", "BAREWire.fsproj")
        let violatingHarness = writeScanHarness boundaryTargetsPath scratch violatingProbeSource

        // Exact-reason negative control through -target:CoreCompile with both design-time properties set.
        let negExit, negOutput =
            runMsbuild scratch violatingHarness
                [ "-target:CoreCompile"
                  "-property:DesignTimeBuild=true"
                  "-property:SkipCompilerExecution=true" ]
        Assert.True(negExit <> 0, sprintf "Expected CoreCompile with DesignTimeBuild+SkipCompilerExecution to refuse violations, got exit 0:\n%s" negOutput)
        Assert.Contains("error ALEX001: " + alex001Reason, negOutput)
        Assert.Contains("error ALEX003: " + alex003Reason, negOutput)
        Assert.Contains("error ALEX004: " + alex004Reason, negOutput)

        let refHarness = writeHarness boundaryTargetsPath scratch
        let refNegExit, refNegOutput =
            runMsbuild scratch refHarness
                [ "-target:CoreCompile"
                  "-property:DesignTimeBuild=true"
                  "-property:SkipCompilerExecution=true"
                  "-property:TestPermittedPrimary=" + linkPsg
                  "-property:TestPermittedLibrary=" + linkBareWire
                  "-property:TestRef=" + realForeign ]
        Assert.True(refNegExit <> 0, sprintf "Expected CoreCompile design-time check to refuse unpermitted ProjectReference, got exit 0:\n%s" refNegOutput)
        Assert.Contains("error ALEX002:", refNegOutput)

        // Fault-injection control: in the same self-contained build directory (with a real built
        // Alex.Boundary.Tasks.dll beside the targets file), first confirm the unmutated targets file
        // refuses the violation under CoreCompile + DesignTimeBuild=true + SkipCompilerExecution=true,
        // then mutate ONLY CheckAlexBoundary's Condition to '$(SkipCompilerExecution)' != 'true'
        // (removing Or Exists('$(_AlexBoundaryTaskAssembly)')) and prove the exact same violation escapes.
        let fiDir = Path.Combine(scratch, "reverted-check")
        let fiTargets, _, _, fiDll = copyBoundaryBuildTree fiDir
        let fiCleanHarness = writeScanHarness fiTargets scratch cleanProbeSource
        let fiBuildExit, fiBuildOutput = runMsbuild scratch fiCleanHarness [ "-target:CheckAlexBoundary" ]
        Assert.True((fiBuildExit = 0), sprintf "Expected baseline build in reverted-check dir to succeed, got exit %d:\n%s" fiBuildExit fiBuildOutput)
        Assert.True(File.Exists(fiDll), sprintf "Expected built task DLL beside targets at %s" fiDll)
        let fiOriginalHarness = writeScanHarness fiTargets scratch violatingProbeSource
        let fiBaselineExit, fiBaselineOutput =
            runMsbuild scratch fiOriginalHarness
                [ "-target:CoreCompile"
                  "-property:DesignTimeBuild=true"
                  "-property:SkipCompilerExecution=true" ]
        Assert.True(fiBaselineExit <> 0, sprintf "Expected unmutated targets in reverted-check dir to refuse violations, got exit 0:\n%s" fiBaselineOutput)
        Assert.Contains("error ALEX001: " + alex001Reason, fiBaselineOutput)
        Assert.Contains("error ALEX003: " + alex003Reason, fiBaselineOutput)
        Assert.Contains("error ALEX004: " + alex004Reason, fiBaselineOutput)

        let revertedTargets = Path.Combine(fiDir, "Boundary.reverted.targets")
        let doc = XDocument.Load(fiTargets)
        let checkTarget =
            doc.Descendants()
            |> Seq.filter (fun el -> el.Name.LocalName = "Target" && attrValue "Name" el = "CheckAlexBoundary")
            |> Seq.exactlyOne
        checkTarget.SetAttributeValue(XName.Get "Condition", "'$(SkipCompilerExecution)' != 'true'")
        doc.Save(revertedTargets)
        let revertedHarness = writeScanHarness revertedTargets scratch violatingProbeSource
        let faultExit, faultOutput =
            runMsbuild scratch revertedHarness
                [ "-target:CoreCompile"
                  "-property:DesignTimeBuild=true"
                  "-property:SkipCompilerExecution=true" ]
        Assert.True((faultExit = 0), sprintf "Expected reverted CheckAlexBoundary condition to let violation escape CoreCompile, got exit %d:\n%s" faultExit faultOutput)
        for code in [ "ALEX001"; "ALEX002"; "ALEX003"; "ALEX004" ] do
            Assert.DoesNotContain("error " + code, faultOutput))

let private evaluateProperties (workingDir: string) (projectPath: string) (props: string list) (overrides: string list) =
    let exitCode, output =
        runMsbuild workingDir projectPath
            (("-getProperty:" + String.concat "," props) :: overrides)
    Assert.True((exitCode = 0), sprintf "Property evaluation failed for %s (exit %d):\n%s" projectPath exitCode output)
    use doc = JsonDocument.Parse(output)
    let propObj = doc.RootElement.GetProperty("Properties")
    props
    |> List.map (fun p -> p, propObj.GetProperty(p).GetString())
    |> Map.ofList

[<Fact>]
let ``TreatAsLocalProperty hardens Alex.fsproj and Alex.Tests.fsproj against CLI property overrides`` () =
    let hardenedProps =
        [ "AlexBoundaryScope"
          "AlexBoundaryAlsoPermitted"
          "AlexBoundaryPermitted"
          "PsgContractProject"
          "PsgContractLibrary"
          "_AlexBoundaryTaskProject"
          "_AlexBoundaryTaskAssembly"
          "_AlexBoundaryTaskSource"
          "_SkipAlexBoundaryCheck"
          "WarningsAsErrors" ]
    let hostileOverrides =
        [ "-property:AlexBoundaryScope=tests"
          "-property:AlexBoundaryAlsoPermitted=/evil/Extra.fsproj"
          "-property:AlexBoundaryPermitted=/evil/Only.fsproj"
          "-property:PsgContractProject=/evil/Psg.fsproj"
          "-property:PsgContractLibrary=/evil/Lib.fsproj"
          "-property:_AlexBoundaryTaskProject=/evil/Task.csproj"
          "-property:_AlexBoundaryTaskAssembly=/evil/Task.dll"
          "-property:_AlexBoundaryTaskSource=/evil/Task.cs"
          "-property:_SkipAlexBoundaryCheck=true"
          "-property:WarningsAsErrors=" ]

    // Positive + negative control on src/Alex/Alex.fsproj (evaluation-only -getProperty, no Restore).
    let alexNormal = evaluateProperties repoRoot alexProjectPath hardenedProps []
    let alexHostile = evaluateProperties repoRoot alexProjectPath hardenedProps hostileOverrides
    Assert.Equal("library", alexHostile["AlexBoundaryScope"])
    Assert.Equal("", alexHostile["AlexBoundaryAlsoPermitted"])
    Assert.Equal("", alexHostile["_SkipAlexBoundaryCheck"])
    Assert.Equal(alexNormal["PsgContractProject"], alexHostile["PsgContractProject"])
    Assert.Equal(alexNormal["PsgContractLibrary"], alexHostile["PsgContractLibrary"])
    Assert.Equal(alexNormal["AlexBoundaryPermitted"], alexHostile["AlexBoundaryPermitted"])
    Assert.Equal(alexNormal["_AlexBoundaryTaskProject"], alexHostile["_AlexBoundaryTaskProject"])
    Assert.Equal(alexNormal["_AlexBoundaryTaskAssembly"], alexHostile["_AlexBoundaryTaskAssembly"])
    Assert.Equal(alexNormal["_AlexBoundaryTaskSource"], alexHostile["_AlexBoundaryTaskSource"])
    let alexWarnings = splitSemicolon alexHostile["WarningsAsErrors"] |> Set.ofArray
    Assert.Contains("FS0025", alexWarnings)
    Assert.Contains("FS0026", alexWarnings)

    // Positive + negative control on tests/Alex.Tests/Alex.Tests.fsproj (all 10 hardened properties).
    let testsHostileOverrides =
        "-property:AlexBoundaryScope=library" :: (hostileOverrides |> List.tail)
    let testsNormal = evaluateProperties repoRoot alexTestsProjectPath hardenedProps []
    let testsHostile = evaluateProperties repoRoot alexTestsProjectPath hardenedProps testsHostileOverrides
    Assert.Equal("tests", testsHostile["AlexBoundaryScope"])
    Assert.Equal(testsNormal["AlexBoundaryAlsoPermitted"], testsHostile["AlexBoundaryAlsoPermitted"])
    Assert.Equal("", testsHostile["_SkipAlexBoundaryCheck"])
    Assert.Equal(testsNormal["PsgContractProject"], testsHostile["PsgContractProject"])
    Assert.Equal(testsNormal["PsgContractLibrary"], testsHostile["PsgContractLibrary"])
    Assert.Equal(testsNormal["AlexBoundaryPermitted"], testsHostile["AlexBoundaryPermitted"])
    Assert.Equal(testsNormal["_AlexBoundaryTaskProject"], testsHostile["_AlexBoundaryTaskProject"])
    Assert.Equal(testsNormal["_AlexBoundaryTaskAssembly"], testsHostile["_AlexBoundaryTaskAssembly"])
    Assert.Equal(testsNormal["_AlexBoundaryTaskSource"], testsHostile["_AlexBoundaryTaskSource"])

    // Fault-injection control: stripping TreatAsLocalProperty from a scratch copy of Alex.fsproj
    // (with the exact same Directory.Build.props beside it) proves CLI global overrides hijack those
    // properties without TreatAsLocalProperty.
    withScratch (fun scratch ->
        File.Copy(Path.Combine(repoRoot, "Directory.Build.props"), Path.Combine(scratch, "Directory.Build.props"))
        let doc = XDocument.Load(alexProjectPath)
        doc.Root.SetAttributeValue(XName.Get "TreatAsLocalProperty", null)
        // Rewrite relative Boundary.targets import to absolute path for scratch location.
        for imp in doc.Descendants() |> Seq.filter (fun el -> el.Name.LocalName = "Import") do
            if attrValue "Project" imp = "../../build/Boundary.targets" then
                imp.SetAttributeValue(XName.Get "Project", boundaryTargetsPath)
        let unhardenedProj = Path.Combine(scratch, "Alex.unhardened.fsproj")
        doc.Save(unhardenedProj)
        let hijacked = evaluateProperties scratch unhardenedProj hardenedProps hostileOverrides
        Assert.Equal("tests", hijacked["AlexBoundaryScope"])
        Assert.Equal("/evil/Extra.fsproj", hijacked["AlexBoundaryAlsoPermitted"])
        Assert.Equal("true", hijacked["_SkipAlexBoundaryCheck"])
        Assert.Equal("/evil/Psg.fsproj", hijacked["PsgContractProject"])
        Assert.Equal("/evil/Task.dll", hijacked["_AlexBoundaryTaskAssembly"])
        Assert.Equal("", hijacked["WarningsAsErrors"]))
