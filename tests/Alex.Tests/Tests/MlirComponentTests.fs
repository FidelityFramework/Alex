module Alex.Tests.MlirComponentTests

open System
open Xunit
open Alex.Tests.ArrayRead
open Alex.Dialects.Core.Types
open Alex.Dialects.Core.Serialize

[<Theory>]
[<InlineData(true, 32)>]
[<InlineData(false, 32)>]
[<InlineData(true, 64)>]
[<InlineData(false, 64)>]
let ``pattern output serializes the index read`` (unsigned: bool) (pointerBits: int) =
    let text = readModule (arrayRead unsigned) pointerBits
    Assert.Contains("func.func @read_index", text)
    Assert.DoesNotContain("TODO", text)

[<Theory>]
[<InlineData(32)>]
[<InlineData(64)>]
let ``opaque static frame copy serializes as one copy without field loads`` (pointerBits: int) =
    let storage = TMemRefStatic(136, TInt(IntWidth 8))
    let copy = MLIROp.MemRefOp(MemRefOp.Copy(Arg 0, Arg 1, storage, storage))
    let definition =
        MLIROp.FuncOp(FuncOp.FuncDef("copy_frame", [Arg 0, storage; Arg 1, storage], [],
            [copy; MLIROp.FuncOp(FuncOp.Return [])], FuncVisibility.Public))
    let text = moduleToString (Ok pointerBits) "opaque_copy_component" [definition]
    Assert.Contains("memref.copy", text)
    Assert.DoesNotContain("memref.load", text)
    Assert.DoesNotContain("memref.store", text)

[<Theory>]
[<InlineData(32, 8, 1)>]
[<InlineData(64, 32, 4)>]
let ``dynamic stack allocation serializes its descriptor element and alignment`` pointerBits elementBits alignment =
    let element = TInt(IntWidth elementBits)
    let storage = V(700,0)
    let zero, extent = V(700,1), V(700,2)
    let definition = MLIROp.FuncOp(FuncOp.FuncDef("allocation_extent",[Arg 0,TIndex;Arg 1,element],[TIndex],
        [ MLIROp.MemRefOp(MemRefOp.AllocaDynamic(storage,Arg 0,element,alignment))
          MLIROp.IndexOp(IndexOp.IndexConst(zero,0L))
          MLIROp.MemRefOp(MemRefOp.Store(Arg 1,storage,[zero],element,TMemRef element))
          MLIROp.MemRefOp(MemRefOp.Dim(extent,storage,zero,TMemRef element))
          MLIROp.FuncOp(FuncOp.Return[{ SSA = extent; Type = TIndex }]) ],FuncVisibility.Public))
    let text = moduleToString (Ok pointerBits) "source_array_storage" [definition]
    Assert.Contains($"memref<?xi{elementBits}>",text)
    Assert.Contains($"alignment = {alignment}",text)
