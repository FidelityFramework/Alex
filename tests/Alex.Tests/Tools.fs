/// The MLIR verifier, run over text serialized from Alex operations.
module Alex.Tests.Tools

open System.Diagnostics
open Xunit

/// Runs the real tool. A missing tool fails the test.
let mlirOpt arguments input =
    let start = ProcessStartInfo("mlir-opt", UseShellExecute = false,
                                RedirectStandardInput = true,
                                RedirectStandardOutput = true,
                                RedirectStandardError = true)
    for argument in arguments do start.ArgumentList.Add argument
    use child = new Process(StartInfo = start)
    if not (child.Start()) then failwith "Cannot start mlir-opt"
    let stdout, stderr = child.StandardOutput.ReadToEndAsync(), child.StandardError.ReadToEndAsync()
    child.StandardInput.Write(input: string)
    child.StandardInput.Close()
    if not (child.WaitForExit 20000) then
        child.Kill(true)
        child.WaitForExit()
        failwith "mlir-opt component verification timed out"
    let output, errors = stdout.GetAwaiter().GetResult(), stderr.GetAwaiter().GetResult()
    Assert.True(child.ExitCode = 0, $"mlir-opt exited {child.ExitCode}:\n{errors}\nInput:\n{input}")
    output
