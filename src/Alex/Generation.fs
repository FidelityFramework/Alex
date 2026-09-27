/// Generation: the public entry of Alex.
///
///   published PSG revision  ->  witnessed MLIR operations, their portable text,
///                               and the correspondence between each emitted
///                               definition and the occurrence it was witnessed at
///
/// Nothing about the program is computed here. Every fact the witnesses read is in
/// the revision. A fact the revision lacks is reported as missing from the revision.
///
/// Alex opens no file and writes none. What it produces beside the module is returned
/// as named text; the host, or a sink the host owns, decides what is kept and where.
module Alex.Generation

open Fidelity.PSG
open Alex.Dialects.Core.Types
open Alex.Dialects.Core.Serialize
open Alex.Traversal.TransferTypes
open Alex.Traversal.MLIRTransfer
open Alex.Target
open Alex.Correspondence

/// What a host supplies for one witnessing of one revision.
type Request = {
    Revision: Revision
    Target: TargetPlatform
    /// Libraries the project declares, beside those the revision requires.
    LinkedLibraries: Set<string>
}

/// One named text produced beside the witnessed module.
type Artifact = {
    Name: string
    Text: string
}

/// The proof obligations the revision carries and their passive transcription.
type ProofTranscription = {
    Obligations: ObligationInfo list
    Operations: MLIROp list
    Text: string
}

/// Everything one witnessing produces.
[<NoEquality; NoComparison>]
type Witnessed = {
    Scope: SemanticScope
    Operations: MLIROp list
    Definitions: EmittedDefinition list
    /// The portable serialization of exactly `Operations`.
    Text: string
    /// `None` where the target expects an unnamed module.
    ModuleName: string option
    PointerBits: Result<int, string>
    WritableStorage: (string * ProgramStorageEntry) list
    Proof: ProofTranscription
    /// Pin constraints, where the target is a fabric and the revision declares pins.
    Constraints: Artifact option
    /// Libraries the revision requires, joined with those the project declares.
    Links: Set<string>
}

/// A refusal, with the operations witnessed before it. They are evidence for
/// diagnosis; a host that keeps them renders them with `serialize`, off its pipeline.
type Refusal = {
    Reason: string
    Witnessed: MLIROp list
    ModuleName: string option
    PointerBits: Result<int, string>
}

/// The portable text of a module of operations.
let serialize (pointerBits: Result<int, string>) (moduleName: string option) (operations: MLIROp list) : string =
    match moduleName with
    | None -> sprintf "module {\n%s\n}" (opsToString pointerBits operations "  ")
    | Some name -> moduleToString pointerBits name operations

let private witness (request: Request) : Result<Witnessed, Refusal> =
    let revision = request.Revision
    let arch : Architecture = { Register = revision.Platform.Register; Pointer = revision.Platform.Pointer }
    let coeffects : TransferCoeffects = {
        Platform = { TargetArch = arch; LinkedLibraries = request.LinkedLibraries }
        TargetPlatform = request.Target
    }
    let moduleName = if request.Target = TargetPlatform.NPU then None else Some "main"
    let refuse reason operations =
        { Reason = reason; Witnessed = operations; ModuleName = moduleName; PointerBits = arch.Pointer }

    // The current whole-revision traversal. This is not a source invalidation
    // or partition decision.
    match revision.DeclarationRoots with
    | [] -> Result.Error (refuse "No declaration roots found in the PSG revision" [])
    | (entryId, _) :: _ ->
        match transferWithCorrespondence revision entryId coeffects with
        | Result.Error refusal -> Result.Error (refuse refusal.Reason refusal.Witnessed)
        | Result.Ok (operations, scope, definitions) ->
            // Preserve exactly what the witnesses produced. This boundary never
            // repairs, drops or rewrites witnessed MLIR.
            let storage =
                Alex.Traversal.StaticStorageValidation.validate revision operations
                |> Result.bind (fun () -> Alex.Traversal.StaticStorageValidation.validateWritable arch revision operations)
            // Pin constraints are a parallel residual of the pin facts the
            // revision carries. A design that declares no pins has none.
            let constraints =
                match request.Target, revision.Codata.Pins with
                | TargetPlatform.FPGA, Some mapping ->
                    Alex.Traversal.XDCTransfer.transfer mapping
                    |> Result.map (fun xdc -> Some { Name = "constraints.xdc"; Text = xdc })
                | _ -> Result.Ok None
            match storage, constraints with
            | Result.Error reason, _ | _, Result.Error reason -> Result.Error (refuse reason operations)
            | Result.Ok writableStorage, Result.Ok constraints ->
                Result.Ok
                    { Scope = scope
                      Operations = operations
                      Definitions = definitions
                      Text = serialize arch.Pointer moduleName operations
                      ModuleName = moduleName
                      PointerBits = arch.Pointer
                      WritableStorage = writableStorage
                      Proof = { Obligations = revision.Obligations
                                Operations = Alex.Traversal.SMTTransfer.operations revision.Obligations
                                Text = Alex.Traversal.SMTTransfer.transfer revision.Obligations }
                      Constraints = constraints
                      Links = Set.union revision.Emission.Boundary.Links request.LinkedLibraries }

/// Witness one revision. A core's leg reads the declared Register and Pointer widths at
/// every boundary and layout site. A revision that declares neither cannot start it and
/// is refused here, before any witness runs, with the producer's own diagnostic.
/// The fabric leg reads neither.
let generate (request: Request) : Result<Witnessed, Refusal> =
    let undeclared =
        match request.Target with
        | TargetPlatform.FPGA -> None
        | _ ->
            match request.Revision.Platform.Register, request.Revision.Platform.Pointer with
            | Result.Error message, _ | _, Result.Error message -> Some message
            | Result.Ok _, Result.Ok _ -> None
    match undeclared with
    | Some message ->
        Result.Error { Reason = message; Witnessed = []; ModuleName = None; PointerBits = request.Revision.Platform.Pointer }
    | None -> witness request
