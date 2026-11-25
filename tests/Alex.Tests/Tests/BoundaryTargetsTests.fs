module Alex.Tests.BoundaryTargetsTests

open System
open System.Diagnostics
open System.IO
open System.Security
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
let ``ALEX002 design-time controls: DesignTimeBuild enforces ALEX002 unless SkipCompilerExecution is true`` () =
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
        // DesignTimeBuild=true WITH SkipCompilerExecution=true skips compilation and CheckAlexBoundary cleanly.
        let skippedExit, skippedOutput =
            runMsbuild scratch harness
                [ "-target:CheckAlexBoundary"
                  "-property:DesignTimeBuild=true"
                  "-property:SkipCompilerExecution=true"
                  "-property:TestPermittedPrimary=" + linkPsg
                  "-property:TestPermittedLibrary=" + linkBareWire
                  "-property:TestRef=" + realForeign ]
        Assert.True((skippedExit = 0), sprintf "Expected DesignTimeBuild=true with SkipCompilerExecution=true to skip cleanly, got exit %d:\n%s" skippedExit skippedOutput)
        Assert.DoesNotContain("ALEX002", skippedOutput))

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
