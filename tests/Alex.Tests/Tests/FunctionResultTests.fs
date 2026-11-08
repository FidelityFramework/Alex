module Alex.Tests.FunctionResultTests

open Xunit
open Alex.Dialects.Core.Types
open Alex.Traversal.TransferTypes
open Alex.Tests.Build
open Alex.Tests.ArrayRead

let private integer = TInt(IntWidth 32)
let private environment = TMemRef integer
let private callback = TFunc([environment; integer], [integer])
let private results = [callback; environment]
let private value ssa ty : Val = { SSA = ssa; Type = ty }
let private f operation = MLIROp.FuncOp operation

/// The graph supplies only the parser occurrence. These inputs are already
/// physical components; this gate does not invent a source callable carrier.
let private definition pointerBits name parameters body (returned: Val list) =
    let position = (arrayRead true).Position
    let pattern = Alex.Patterns.ClosurePatterns.pFunctionDefResults FuncVisibility.Public name parameters None
                      (List.map _.Type returned) body returned
    match matchAt pattern position pointerBits (MLIRAccumulator.empty ()) with
    | Result.Ok (operation, _) -> operation
    | Result.Error reason -> failwith reason

[<Theory>]
[<InlineData(32)>]
[<InlineData(64)>]
let ``separate code and environment returns survive direct and indirect calls`` pointerBits =
    let env, argument = value (Arg 0) environment, value (Arg 1) integer
    let zero, loaded, sum = V(800, 0), V(800, 1), V(800, 2)
    let implementation = definition pointerBits "apply_environment" [env.SSA, env.Type; argument.SSA, argument.Type]
                             [MLIROp.IndexOp(IndexOp.IndexConst(zero, 0L))
                              MLIROp.MemRefOp(MemRefOp.Load(loaded, env.SSA, [zero], integer, environment))
                              MLIROp.ArithOp(ArithOp.AddI(sum, loaded, argument.SSA, integer))]
                             [value sum integer]
    let code = value (V(801, 0)) callback
    let factory = definition pointerBits "make_callable" [env.SSA, env.Type]
                      [f (FuncOp.FuncConstant(code.SSA, "apply_environment", callback))] [code; env]
    // A single function-typed result exercises the nested arrow's parentheses.
    let codeIdentity = definition pointerBits "code_identity" [Arg 0, callback] [] [value (Arg 0) callback]
    let directCode, directEnv = value (V(802, 0)) callback, value (V(802, 1)) environment
    let indirectCode, indirectEnv = value (V(802, 2)) callback, value (V(802, 3)) environment
    let factoryType = TFunc([environment], results)
    let factoryCode = value (V(802, 4)) factoryType
    let first, second, total = value (V(802, 5)) integer, value (V(802, 6)) integer, value (V(802, 7)) integer
    let body =
        [f (FuncOp.FuncCall([directCode; directEnv], "make_callable", [env]))
         f (FuncOp.FuncCallIndirect([first], directCode.SSA, [directEnv; argument]))
         f (FuncOp.FuncConstant(factoryCode.SSA, "make_callable", factoryType))
         f (FuncOp.FuncCallIndirect([indirectCode; indirectEnv], factoryCode.SSA, [env]))
         f (FuncOp.FuncCallIndirect([second], indirectCode.SSA, [indirectEnv; argument]))
         MLIROp.ArithOp(ArithOp.AddI(total.SSA, first.SSA, second.SSA, integer))]
    let consumer = definition pointerBits "consume_callable_results" [env.SSA, env.Type; argument.SSA, argument.Type] body [total]
    let operations = [implementation; factory; codeIdentity; consumer]
    let source = Alex.Dialects.Core.Serialize.moduleToString (Ok pointerBits) "function_results" operations
    Assert.Contains("func.call @make_callable", source)
    Assert.Contains("call_indirect", source)
    Assert.Contains("return", source)

[<Fact>]
let ``module declaration preserves result lists in nounwind calls`` () =
    let declaration = f (FuncOp.FuncDecl("foreign_callable", [environment], results, FuncVisibility.Private, []))
    let returned = [value (V(803, 0)) callback; value (V(803, 1)) environment]
    let wrapper = MLIROp.NoUnwindFunction(FuncOp.FuncDef("forward_callable", [Arg 0, environment], results,
                      [f (FuncOp.FuncCall(returned, "foreign_callable", [value (Arg 0) environment])); f (FuncOp.Return returned)], FuncVisibility.Public))
    let collected = [declaration; wrapper]
    Assert.Equal(declaration, collected.Head)
    let text = Alex.Dialects.Core.Serialize.moduleToString (Ok 64) "nounwind_results" collected
    Assert.Contains("@foreign_callable", text)

[<Fact>]
let ``function code SSA has no implicit packed storage size`` () =
    let error = Assert.Throws<System.Exception>(fun () -> mlirTypeSizeWith (Ok 64) callback |> ignore)
    Assert.Contains("no admitted data-storage layout", error.Message)

[<Theory>]
[<InlineData(false)>]
[<InlineData(true)>]
let ``function definition pattern rejects missing or reordered mandatory result components`` reorder =
    let position = (arrayRead true).Position
    let supplied = if reorder then [value (V(804, 0)) environment; value (V(804, 1)) callback] else []
    let pattern = Alex.Patterns.ClosurePatterns.pFunctionDefResults FuncVisibility.Public "required_results" [] None results [] supplied
    match matchAt pattern position 64 (MLIRAccumulator.empty ()) with
    | Result.Error message -> Assert.Contains("mismatched result components", message)
    | Result.Ok _ -> failwith "pFunctionDefResults accepted missing or reordered result components"

[<Fact>]
let ``indirect application pattern rejects conflicting callable result signature`` () =
    let position = (arrayRead true).Position
    let code = value (V(804, 2)) (TFunc([environment], results))
    let pattern = Alex.Patterns.ApplicationPatterns.pIndirectApplication position.Focus.Id code [value (Arg 0) environment] integer
    match matchAt pattern position 64 (MLIRAccumulator.empty ()) with
    | Result.Error message -> Assert.Contains("Callable invocation operands disagree with its witnessed physical signature", message)
    | Result.Ok _ -> failwith "pIndirectApplication accepted a conflicting callable result signature"

[<Fact>]
let ``void scalar call cannot silently create a result`` () =
    let position = (arrayRead true).Position
    let pattern = Alex.Patterns.ApplicationPatterns.pDirectCall position.Focus.Id "void_effect" [] TVoid None
    match matchAt pattern position 64 (MLIRAccumulator.empty ()) with
    | Result.Error message -> Assert.Contains("void function call cannot define an SSA result", message)
    | Result.Ok _ -> failwith "A scalar call created a void SSA"

[<Fact>]
let ``nounwind wrapping preserves storage correspondence validation`` () =
    let graph = (arrayRead true).Graph
    let operation = MLIROp.NoUnwindFunction(FuncOp.FuncDef("bad_pool", [], [],
                        [MLIROp.GlobalBytePool("unexpected_pool", [0uy], 1, []); f (FuncOp.Return [])], FuncVisibility.Public))
    match Alex.Traversal.StaticStorageValidation.validate graph [operation] with
    | Result.Error message -> Assert.Contains("without a settled BAREWire plan", message)
    | Result.Ok _ -> failwith "A nounwind wrapper hid an unplanned byte pool"
