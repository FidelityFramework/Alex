module Bozzetto.AlexAnalyzers

open FSharp.Analyzers.SDK
open FSharp.Analyzers.SDK.TASTCollecting
open FSharp.Analyzers.SDK.ASTCollecting
open FSharp.Compiler.Syntax
open FSharp.Compiler.Symbols
open FSharp.Compiler.Symbols.FSharpExprPatterns
open FSharp.Compiler.Text

type private AliasDependency =
  | ObjectDependency
  | BclDependency of FSharpEntity

let private analyzeShared (context: CliContext) = async {
  let diagnostics = ResizeArray<Message>()
  match context.TypedTree with
  | None ->
    let position = Position.mkPos 1 0
    diagnostics.Add {
      Type = "Alex analysis incomplete"
      Message = "The typed tree is unavailable; Alex boundary analysis cannot run."
      Code = "AXA000"
      Severity = Severity.Error
      Range = Range.mkRange context.FileName position position
      Fixes = []
    }
  | Some tree ->
    let classifyEntity (entity: FSharpEntity) =
      let assembly = entity.Assembly.SimpleName
      if entity.IsFSharpAbbreviation then
        Ok false
      else
        match entity.TryFullName with
        | None when assembly = "FSharp.Core" -> Ok false
        | None -> Error (sprintf "Cannot establish the qualified identity of entity '%s' in assembly '%s'." entity.DisplayName assembly)
        | Some name ->
          let bclName =
            name = "System" || name.StartsWith("System.") ||
            (name.StartsWith("Microsoft.") && not (name.StartsWith("Microsoft.FSharp.")))
          let bclAssembly =
            assembly = "mscorlib" || assembly = "netstandard" ||
            assembly.StartsWith("System.") || assembly.StartsWith("Microsoft.")
          Ok (bclName && bclAssembly)
    let rejectBcl range (entity: FSharpEntity) =
      diagnostics.Add {
        Type = "Clef production boundary"
        Message = sprintf "Clef production code must not depend on .NET library APIs: %s (assembly %s)." (entity.TryFullName |> Option.defaultValue entity.DisplayName) entity.Assembly.SimpleName
        Code = "AXC002"
        Severity = Severity.Error
        Range = range
        Fixes = []
      }
    let inspectAlias (alias: FSharpEntity) =
      let rec walk depth (typ: FSharpType) =
        if depth > 32 then Error (sprintf "type step %d exceeded the alias expansion limit" depth)
        else
          try
            let children () =
              typ.GenericArguments
              |> Seq.fold (fun result child ->
                match result, walk (depth + 1) child with
                | Ok previous, Ok next -> Ok (previous @ next)
                | Error reason, _ | _, Error reason -> Error reason) (Ok [])
            if typ.IsGenericParameter || typ.IsMeasureType then Ok []
            elif typ.IsTupleType || typ.IsFunctionType || typ.IsAnonRecordType then children ()
            elif typ.HasTypeDefinition then
              let definition = typ.TypeDefinition
              let assembly = definition.Assembly.SimpleName
              if definition.IsProvided then Error (sprintf "type step %d has an unsupported provided identity" depth)
              elif typ.IsAbbreviation && assembly <> "FSharp.Core" then
                match children (), walk (depth + 1) definition.AbbreviatedType with
                | Ok arguments, Ok body -> Ok (arguments @ body)
                | Error reason, _ | _, Error reason -> Error reason
              elif typ.IsAbbreviation && assembly = "FSharp.Core" && definition.DisplayName = "obj" then
                let target = definition.AbbreviatedType
                if target.HasTypeDefinition && target.TypeDefinition.TryFullName = Some "System.Object" then Ok [ ObjectDependency ]
                else Error (sprintf "type step %d cannot establish the intrinsic obj target" depth)
              else
                match children (), classifyEntity definition with
                | Error reason, _ | _, Error reason -> Error reason
                | Ok nested, Ok isBcl when isBcl && definition.TryFullName = Some "System.Object" -> Ok (ObjectDependency :: nested)
                | Ok nested, Ok true -> Ok (BclDependency definition :: nested)
                | Ok nested, Ok false -> Ok nested
            else Error (sprintf "type step %d has an unrecognized shape" depth)
          with error -> Error (sprintf "type step %d failed: %s" depth error.Message)
      try walk 0 alias.AbbreviatedType with error -> Error error.Message
    let checkEntity range (entity: FSharpEntity) =
      let result =
        if entity.IsFSharpAbbreviation && entity.Assembly.SimpleName <> "FSharp.Core" then
          inspectAlias entity |> Result.mapError (fun reason -> sprintf "Cannot inspect alias '%s': %s" entity.DisplayName reason)
        else classifyEntity entity |> Result.map (fun isBcl -> if isBcl then [ BclDependency entity ] else [])
      match result with
      | Ok dependencies ->
        for dependency in dependencies do
          match dependency with
          | BclDependency target -> rejectBcl range target
          | ObjectDependency ->
            diagnostics.Add { Type = "Clef production boundary"; Message = sprintf "Clef production code must not declare obj types. %s resolves to System.Object." entity.DisplayName; Code = "AXC005"; Severity = Severity.Error; Range = range; Fixes = [] }
      | Error reason ->
        diagnostics.Add {
          Type = "Clef analysis incomplete"
          Message = reason
          Code = "AXA000"
          Severity = Severity.Error
          Range = range
          Fixes = []
        }
    let integerLiteralRanges = ResizeArray<range>()
    let literalSyntax =
      { new SyntaxCollectorBase() with
          override _.WalkExpr(_, expression) =
            match expression with
            | SynExpr.Const(SynConst.UserNum(_, "I"), range) -> integerLiteralRanges.Add range
            | _ -> () }
    walkAst literalSyntax context.ParseFileResults.ParseTree
    for symbolUse in context.GetAllSymbolUsesOfFile() do
      match symbolUse.Symbol with
      | :? FSharpMemberOrFunctionOrValue as value when value.CompiledName = "Box" && (value.DeclaringEntity |> Option.exists (fun entity -> entity.TryFullName = Some "Microsoft.FSharp.Core.Operators")) ->
        diagnostics.Add { Type = "Clef production boundary"; Message = "Clef production code must not widen a value to obj."; Code = "AXC004"; Severity = Severity.Error; Range = symbolUse.Range; Fixes = [] }
      | _ -> ()
      let entity =
        match symbolUse.Symbol with
        | :? FSharpEntity as entity -> Some entity
        | :? FSharpMemberOrFunctionOrValue as memberOrFunction -> memberOrFunction.DeclaringEntity
        | _ -> None
      entity |> Option.iter (fun value ->
        // FCS adds BigInteger representation entities at bigint literal spans.
        // Only these exact syntax spans qualify; explicit types, calls and opens still pass through.
        let literalRepresentation =
          (match symbolUse.Symbol with :? FSharpEntity -> true | _ -> false)
          && (value.TryFullName = Some "System" || value.TryFullName = Some "System.Numerics"
              || value.TryFullName = Some "System.Numerics.BigInteger")
          && integerLiteralRanges.Contains symbolUse.Range
        if not literalRepresentation && not (symbolUse.IsFromDefinition && value.IsFSharpAbbreviation) then
          checkEntity symbolUse.Range value)
    for declaration in context.CheckFileResults.OpenDeclarations do
      match declaration.Range with
      | Some range when not declaration.IsOwnNamespace ->
        declaration.Modules |> List.iter (checkEntity range)
        declaration.Types |> List.iter (fun typ ->
          if typ.HasTypeDefinition then checkEntity range typ.TypeDefinition)
      | _ -> ()
    let rejectNull range =
      diagnostics.Add {
        Type = "Clef production boundary"
        Message = "Clef production code must not use null."
        Code = "AXC001"
        Severity = Severity.Error
        Range = range
        Fixes = []
      }
    let explicitUpcasts = ResizeArray<range * range>()
    let authoredValues = ResizeArray<range>()
    let rec listValues expression =
      match expression with
      | SynExpr.Sequential(_, _, first, second, _, _) -> listValues first; listValues second
      | value -> authoredValues.Add(value.Range)
    let syntax =
      { new SyntaxCollectorBase() with
          override _.WalkExpr(_, expression) =
            match expression with
            | SynExpr.Null range -> rejectNull range
            | SynExpr.Upcast(input, _, range) -> explicitUpcasts.Add(input.Range, range)
            | SynExpr.App(_, _, _, argument, _) -> authoredValues.Add(argument.Range)
            | SynExpr.ArrayOrList(_, values, _) -> values |> List.iter (fun value -> authoredValues.Add(value.Range))
            | SynExpr.ArrayOrListComputed(_, values, _) -> listValues values
            | SynExpr.Record(recordFields = fields) ->
              for SynExprRecordField(_, _, value, _, _) in fields do
                value |> Option.iter (fun expression -> authoredValues.Add(expression.Range))
            | _ -> ()
          override _.WalkPat(_, pattern) =
            match pattern with
            | SynPat.Null range -> rejectNull range
            | _ -> () }
    walkAst syntax context.ParseFileResults.ParseTree
    let walker =
      { new TypedTreeCollectorBase() with
          override _.WalkCoerce targetType input =
            let rec isObject (typ: FSharp.Compiler.Symbols.FSharpType) =
              if typ.IsAbbreviation then isObject typ.AbbreviatedType
              else typ.HasTypeDefinition && typ.TypeDefinition.FullName = "System.Object"
            let explicit = explicitUpcasts |> Seq.tryFind (fun (inner, _) -> inner = input.Range)
            let authored = explicit.IsSome || (authoredValues |> Seq.contains input.Range)
            if isObject targetType && not (isObject input.Type) && authored then
              diagnostics.Add {
                Type = "Clef production boundary"
                Message = "Clef production code must not widen a value to obj."
                Code = "AXC004"
                Severity = Severity.Error
                Range = explicit |> Option.map snd |> Option.defaultValue input.Range
                Fixes = []
              }
          override _.WalkCall _ memberOrFunction _ _ _ range =
            let taskBuilder =
              memberOrFunction.DeclaringEntity
              |> Option.exists (fun entity ->
                entity.FullName = "Microsoft.FSharp.Control.TaskBuilder" ||
                entity.FullName = "Microsoft.FSharp.Control.TaskBuilderBase" ||
                entity.FullName = "Microsoft.FSharp.Control.BackgroundTaskBuilder")
            if taskBuilder then
              diagnostics.Add {
                Type = "Clef production boundary"
                Message = "Clef production code must not use task computation expressions."
                Code = "AXC003"
                Severity = Severity.Error
                Range = range
                Fixes = []
              }
      }
    walkTast walker tree
  return diagnostics |> Seq.distinctBy (fun diagnostic -> diagnostic.Code, diagnostic.Range.StartLine, diagnostic.Range.StartColumn) |> List.ofSeq
}

let private objectDeclarations (context: CliContext) = async {
  let diagnostics = ResizeArray<Message>()
  match context.TypedTree with
  | None -> () // analyzeShared owns the missing-tree refusal for this entry point.
  | Some _ ->
    for symbolUse in context.GetAllSymbolUsesOfFile() do
      match symbolUse.Symbol with
      | :? FSharpEntity as entity when entity.DisplayName = "obj" && entity.Assembly.SimpleName = "FSharp.Core" && entity.IsFSharpAbbreviation ->
        let target =
          try
            let typ = entity.AbbreviatedType
            if typ.HasTypeDefinition then typ.TypeDefinition.TryFullName else None
          with _ -> None
        if target = Some "System.Object" then
          diagnostics.Add { Type = "Clef production boundary"; Message = "Clef production code must not declare obj types."; Code = "AXC005"; Severity = Severity.Error; Range = symbolUse.Range; Fixes = [] }
        else
          diagnostics.Add { Type = "Clef analysis incomplete"; Message = "Cannot establish the target of the obj abbreviation."; Code = "AXA000"; Severity = Severity.Error; Range = symbolUse.Range; Fixes = [] }
      | _ -> ()
  return diagnostics |> Seq.distinctBy (fun diagnostic -> diagnostic.Code, diagnostic.Range.StartLine, diagnostic.Range.StartColumn) |> List.ofSeq
}

[<CliAnalyzer("Clef production baseline")>]
let clefBaseline : Analyzer<CliContext> = fun context -> async {
  let! baseline = analyzeShared context
  let! objects = objectDeclarations context
  return baseline @ objects
}

type private DebtPin = {
  File: string
  /// Top-level binding name, or "<enclosing>.<local>" for nested let rec bindings.
  Target: string
  MaxCount: int
}

type private ObservedSite = {
  Target: string
  Range: range
}

type private BindingInfo = {
  Params: FSharpMemberOrFunctionOrValue list
  Body: FSharpExpr
}

type private BindingKey = string * string * int * int
type private BindingEnv = Map<BindingKey, (FSharpMemberOrFunctionOrValue * BindingInfo) list>

type private BoundaryHits = {
  Diagnostics: Message list
  Axa003: ObservedSite list
  Axa004: ObservedSite list
  Axa007: ObservedSite list
}

let private emptyHits = { Diagnostics = []; Axa003 = []; Axa004 = []; Axa007 = [] }

let private mergeHits a b = {
  Diagnostics = a.Diagnostics @ b.Diagnostics
  Axa003 = a.Axa003 @ b.Axa003
  Axa004 = a.Axa004 @ b.Axa004
  Axa007 = a.Axa007 @ b.Axa007
}

let private collectHits items f =
  items |> List.fold (fun acc item -> mergeHits acc (f item)) emptyHits

let private tryBindingKey (value: FSharpMemberOrFunctionOrValue) : BindingKey option =
  try
    let loc = value.DeclarationLocation
    Some (value.LogicalName, loc.FileName, loc.StartLine, loc.StartColumn)
  with _ -> None

let private addBinding (value: FSharpMemberOrFunctionOrValue) (info: BindingInfo) (env: BindingEnv) : BindingEnv =
  match tryBindingKey value with
  | Some key ->
    let rest = env.TryFind key |> Option.defaultValue [] |> List.filter (fun (k, _) -> k <> value)
    env.Add(key, (value, info) :: rest)
  | None -> env

let private tryFindBinding (value: FSharpMemberOrFunctionOrValue) (env: BindingEnv) : BindingInfo option =
  tryBindingKey value
  |> Option.bind env.TryFind
  |> Option.bind (List.tryPick (fun (k, info) -> if k = value then Some info else None))

let rec private peelLambdas (expr: FSharpExpr) : FSharpMemberOrFunctionOrValue list * FSharpExpr =
  match expr with
  | Lambda(paramVal, body) ->
    let more, inner = peelLambdas body
    paramVal :: more, inner
  | _ -> [], expr

let private bindingOfExpr (expr: FSharpExpr) : BindingInfo =
  let ps, body = peelLambdas expr
  { Params = ps; Body = body }

let private bindParams (formalParams: FSharpMemberOrFunctionOrValue list) (args: FSharpExpr list) (env: BindingEnv) : BindingEnv =
  let count = min formalParams.Length args.Length
  List.zip (List.take count formalParams) (List.take count args)
  |> List.fold (fun acc (paramVal, argExpr) -> addBinding paramVal (bindingOfExpr argExpr) acc) env

let rec private unwrapApplications (expr: FSharpExpr) : FSharpExpr * FSharpExpr list =
  match expr with
  | Application(funcExpr, _, args) ->
    let head, prefixArgs = unwrapApplications funcExpr
    head, prefixArgs @ args
  | _ -> expr, []

let rec private collectModuleDeclRanges (decl: SynModuleDecl) : range list =
  match decl with
  | SynModuleDecl.Let(isRecursive = true; bindings = letBindings) ->
    letBindings |> List.map (fun (SynBinding(headPat = headPat)) -> headPat.Range)
  | SynModuleDecl.NestedModule(decls = subDecls) ->
    subDecls |> List.collect collectModuleDeclRanges
  | _ -> []

[<CliAnalyzer("Alex published boundary")>]
let alexBoundary : Analyzer<CliContext> = fun context -> async {
  let diagnostics = ResizeArray<Message>()
  match context.TypedTree with
  | None ->
    let position = Position.mkPos 1 0
    diagnostics.Add {
      Type = "Alex analysis incomplete"
      Message = "The typed tree is unavailable; Alex boundary analysis cannot run."
      Code = "AXA000"
      Severity = Severity.Error
      Range = Range.mkRange context.FileName position position
      Fixes = []
    }
  | Some tree ->
    let contract =
      try
        let rec entities (entity: FSharpEntity) = seq {
          yield entity
          for nested in entity.NestedEntities do yield! entities nested
        }
        let records =
          context.CheckFileResults.ProjectContext.GetReferencedAssemblies()
          |> Seq.filter (fun assembly -> assembly.SimpleName = "Fidelity.PSG")
          |> Seq.collect (fun assembly -> assembly.Contents.Entities |> Seq.collect entities)
          |> Seq.filter (fun entity -> entity.IsFSharpRecord)
          |> Seq.toList
        let has name = records |> List.exists (fun entity -> entity.TryFullName = Some name)
        let hasName = records |> List.exists (fun entity -> entity.TryFullName = Some "Fidelity.PSG.NominalTypeIdentity" && (entity.FSharpFields |> Seq.exists (fun field -> field.Name = "Name")))
        if has "Fidelity.PSG.Revision" && has "Fidelity.PSG.SemanticNode" && hasName then Ok ()
        else Error "The referenced Fidelity.PSG contract must define Revision, SemanticNode and NominalTypeIdentity.Name."
      with error -> Error (sprintf "Cannot inspect the referenced Fidelity.PSG contract: %s" error.Message)
    match contract with
    | Error reason ->
      let position = Position.mkPos 1 0
      diagnostics.Add { Type = "Alex analysis incomplete"; Message = reason; Code = "AXA000"; Severity = Severity.Error; Range = Range.mkRange context.FileName position position; Fixes = [] }
    | Ok () -> ()

    let normalizedFile = context.FileName.Replace('\\', '/')
    let projectFileName = System.IO.Path.GetFileName(context.ProjectOptions.ProjectFileName)
    let alexSrcMarker = "/src/Alex/"
    let alexSrcIdx = normalizedFile.IndexOf(alexSrcMarker, System.StringComparison.Ordinal)
    let alexRelativeFile =
      if projectFileName = "Alex.fsproj" && alexSrcIdx >= 0 then
        Some (normalizedFile.Substring(alexSrcIdx + alexSrcMarker.Length))
      else None
    let isProductionAlex = alexRelativeFile.IsSome
    let layerTarget =
      match alexRelativeFile with
      | Some rel -> "/" + rel
      | None -> normalizedFile
    let hasLayerSegment (segment: string) = layerTarget.Contains("/" + segment + "/", System.StringComparison.Ordinal)
    let isZipperSubstrate =
      hasLayerSegment "Traversal" || hasLayerSegment "XParsec" ||
      layerTarget.EndsWith("/Generation.fs", System.StringComparison.Ordinal) ||
      layerTarget.EndsWith("/Generation.fsx", System.StringComparison.Ordinal)
    let isNanopassArchitecture =
      layerTarget.EndsWith("/Traversal/NanopassArchitecture.fs", System.StringComparison.Ordinal) ||
      layerTarget.EndsWith("/Traversal/NanopassArchitecture.fsx", System.StringComparison.Ordinal)
    let inElements = hasLayerSegment "Elements"
    let inWitnesses = hasLayerSegment "Witnesses"
    let inImmutableLayer =
      hasLayerSegment "Dialects" || hasLayerSegment "CodeGeneration" ||
      hasLayerSegment "Elements" || hasLayerSegment "XParsec" || hasLayerSegment "Patterns"

    let isPsgAssembly (assembly: FSharpAssembly) = assembly.SimpleName = "Fidelity.PSG"
    let isPsgEntity (fullName: string) (entity: FSharpEntity) =
      isPsgAssembly entity.Assembly && entity.TryFullName = Some fullName
    let isZipperEntity (entity: FSharpEntity) =
      entity.TryFullName |> Option.exists (fun name ->
        name = "Alex.Traversal.PSGZipper" || name.StartsWith("Alex.Traversal.PSGZipper.", System.StringComparison.Ordinal))
    let isAllowedElementPsgEntity (entity: FSharpEntity) =
      entity.IsNamespace ||
      (isPsgAssembly entity.Assembly &&
       (entity.TryFullName |> Option.exists (fun name ->
          name = "Fidelity.PSG.BoundaryImport" ||
          name = "Fidelity.PSG.IntrinsicWriteImport" ||
          name = "Fidelity.PSG.SpatialModuleWitness" ||
          name = "Fidelity.PSG.BoundaryScalar")))
    let isProhibitedElementPsgEntity (entity: FSharpEntity) =
      (isPsgAssembly entity.Assembly && not (isAllowedElementPsgEntity entity)) ||
      isZipperEntity entity ||
      (entity.Assembly.SimpleName = "Alex" &&
       (entity.TryFullName |> Option.exists (fun name ->
          name = "Alex.CodeGeneration.TypeMapping" ||
          name.StartsWith("Alex.CodeGeneration.TypeMapping.", System.StringComparison.Ordinal) ||
          name = "Alex.CodeGeneration.CallableSymbols" ||
          name.StartsWith("Alex.CodeGeneration.CallableSymbols.", System.StringComparison.Ordinal))))
    let isProhibitedParserStateField (field: FSharpField) =
      (field.Name = "Graph" || field.Name = "Zipper" || field.Name = "Current") &&
      (field.DeclaringEntity |> Option.exists (fun e ->
        e.Assembly.SimpleName = "Alex" && e.TryFullName = Some "Alex.XParsec.PSGCombinators.PSGParserState"))
    let anyTypeResult (visited: Set<string>) (pred: Set<string> -> FSharpType -> Result<bool, string>) (types: seq<FSharpType>) : Result<bool, string> =
      types
      |> Seq.fold (fun state child ->
        match state with
        | Error _ -> state
        | Ok true -> state
        | Ok false -> pred visited child) (Ok false)
    let rec typeHasProhibitedPsgOrZipper (visited: Set<string>) (typ: FSharpType) : Result<bool, string> =
      try
        if typ.IsGenericParameter || typ.IsMeasureType then Ok false
        elif typ.IsTupleType || typ.IsFunctionType || typ.IsAnonRecordType then
          anyTypeResult visited typeHasProhibitedPsgOrZipper typ.GenericArguments
        elif typ.HasTypeDefinition then
          let definition = typ.TypeDefinition
          if isProhibitedElementPsgEntity definition then Ok true
          elif definition.IsFSharpAbbreviation && definition.Assembly.SimpleName <> "FSharp.Core" then
            let key = definition.TryFullName |> Option.defaultValue definition.DisplayName
            if visited.Contains key then Ok false
            else
              match typeHasProhibitedPsgOrZipper (visited.Add key) definition.AbbreviatedType with
              | Ok true -> Ok true
              | Error reason -> Error reason
              | Ok false -> anyTypeResult visited typeHasProhibitedPsgOrZipper typ.GenericArguments
          else
            anyTypeResult visited typeHasProhibitedPsgOrZipper typ.GenericArguments
        else Ok false
      with error -> Error (sprintf "Cannot inspect type for Elements layer purity: %s" error.Message)
    let rec typeFromPsg (visited: Set<string>) (typ: FSharpType) : Result<bool, string> =
      try
        if typ.IsGenericParameter || typ.IsMeasureType then Ok false
        elif typ.HasTypeDefinition then
          let definition = typ.TypeDefinition
          if isPsgAssembly definition.Assembly then Ok true
          elif definition.IsFSharpAbbreviation && definition.Assembly.SimpleName <> "FSharp.Core" then
            let key = definition.TryFullName |> Option.defaultValue definition.DisplayName
            if visited.Contains key then Ok false
            else typeFromPsg (visited.Add key) definition.AbbreviatedType
          else Ok false
        else Ok false
      with error -> Error (sprintf "Cannot inspect Fidelity.PSG type provenance: %s" error.Message)
    let isAccumulatorEntity (entity: FSharpEntity) =
      entity.TryFullName |> Option.exists (fun name ->
        name = "Alex.Traversal.TransferTypes.MLIRAccumulator" ||
        name = "Alex.Traversal.TransferTypes.MLIRAccumulatorModule")
    let isMapModule (entity: FSharpEntity) =
      entity.Assembly.SimpleName = "FSharp.Core" && entity.TryFullName = Some "Microsoft.FSharp.Collections.MapModule"
    let isOptionModule (entity: FSharpEntity) =
      entity.Assembly.SimpleName = "FSharp.Core" && entity.TryFullName = Some "Microsoft.FSharp.Core.OptionModule"
    let isOptionEntity (entity: FSharpEntity) =
      entity.Assembly.SimpleName = "FSharp.Core" && (entity.CompiledName = "FSharpOption`1" || entity.DisplayName = "option")
    let rec isOptionType (typ: FSharpType) =
      if typ.IsAbbreviation then isOptionType typ.AbbreviatedType
      else typ.HasTypeDefinition && isOptionEntity typ.TypeDefinition
    let isResultEntity (entity: FSharpEntity) =
      entity.Assembly.SimpleName = "FSharp.Core" && (entity.CompiledName = "FSharpResult`2" || entity.DisplayName = "Result")
    let isBoolType (typ: FSharpType) =
      if not typ.HasTypeDefinition then false
      else
        let definition = typ.TypeDefinition
        if definition.TryFullName = Some "System.Boolean" then true
        elif typ.IsAbbreviation && definition.Assembly.SimpleName = "FSharp.Core" && definition.DisplayName = "bool" then
          let target = definition.AbbreviatedType
          target.HasTypeDefinition && target.TypeDefinition.TryFullName = Some "System.Boolean"
        else false
    let isFSharpRefEntity (entity: FSharpEntity) =
      entity.Assembly.SimpleName = "FSharp.Core" &&
      (entity.CompiledName = "FSharpRef`1" || entity.TryFullName = Some "Microsoft.FSharp.Core.FSharpRef`1")
    let isRevisionNodesField (field: FSharpField) =
      field.Name = "Nodes" && (field.DeclaringEntity |> Option.exists (isPsgEntity "Fidelity.PSG.Revision"))
    let isRevisionTryNodeValue (value: FSharpMemberOrFunctionOrValue) =
      (value.DisplayName = "tryNode" || value.CompiledName = "tryNode") &&
      (value.DeclaringEntity |> Option.exists (fun entity ->
        isPsgEntity "Fidelity.PSG.RevisionModule" entity || isPsgEntity "Fidelity.PSG.Revision" entity))
    let isRecallValue (value: FSharpMemberOrFunctionOrValue) =
      (value.DisplayName.StartsWith("recall", System.StringComparison.Ordinal) ||
       value.CompiledName.StartsWith("recall", System.StringComparison.Ordinal)) &&
      (value.DeclaringEntity |> Option.exists isAccumulatorEntity)
    let isDeclarationFactsField (field: FSharpField) =
      field.Name = "DeclarationFacts" &&
      (field.DeclaringEntity |> Option.exists (isPsgEntity "Fidelity.PSG.BoundaryImport"))
    let isSemanticKindType (typ: FSharpType) =
      typ.HasTypeDefinition && isPsgEntity "Fidelity.PSG.SemanticKind" typ.TypeDefinition

    let recursiveHeadRanges =
      match context.ParseFileResults.ParseTree with
      | ParsedInput.ImplFile(ParsedImplFileInput(contents = modules)) ->
        modules |> List.collect (fun (SynModuleOrNamespace(decls = decls)) -> decls |> List.collect collectModuleDeclRanges)
      | _ -> []

    // AXA005: Zero-exemption Elements/ PSG & PSGZipper isolation.
    if inElements then
      for declaration in context.CheckFileResults.OpenDeclarations do
        match declaration.Range with
        | Some range when not declaration.IsOwnNamespace ->
          for entity in declaration.Modules do
            if isProhibitedElementPsgEntity entity then
              diagnostics.Add {
                Type = "Alex layer purity"
                Message = sprintf "Elements must not depend on Fidelity.PSG graph/node types, PSGZipper, or TypeMapping (%s)." (entity.TryFullName |> Option.defaultValue entity.DisplayName)
                Code = "AXA005"
                Severity = Severity.Error
                Range = range
                Fixes = []
              }
          for typ in declaration.Types do
            match typeHasProhibitedPsgOrZipper Set.empty typ with
            | Ok true ->
              diagnostics.Add {
                Type = "Alex layer purity"
                Message = "Elements must not open Fidelity.PSG graph/node types, PSGZipper, or TypeMapping."
                Code = "AXA005"
                Severity = Severity.Error
                Range = range
                Fixes = []
              }
            | Ok false -> ()
            | Error reason ->
              diagnostics.Add { Type = "Alex analysis incomplete"; Message = reason; Code = "AXA000"; Severity = Severity.Error; Range = range; Fixes = [] }
        | _ -> ()
      for symbolUse in context.GetAllSymbolUsesOfFile() do
        let leakedResult =
          match symbolUse.Symbol with
          | :? FSharpEntity as entity -> Ok (isProhibitedElementPsgEntity entity)
          | :? FSharpMemberOrFunctionOrValue as value ->
            if value.DeclaringEntity |> Option.exists isProhibitedElementPsgEntity then Ok true
            else typeHasProhibitedPsgOrZipper Set.empty value.FullType
          | :? FSharpField as field ->
            if isProhibitedParserStateField field || (field.DeclaringEntity |> Option.exists isProhibitedElementPsgEntity) then Ok true
            else typeHasProhibitedPsgOrZipper Set.empty field.FieldType
          | :? FSharpUnionCase as unionCase ->
            Ok (unionCase.ReturnType.HasTypeDefinition && isProhibitedElementPsgEntity unionCase.ReturnType.TypeDefinition)
          | _ -> Ok false
        match leakedResult with
        | Ok true ->
          diagnostics.Add {
            Type = "Alex layer purity"
            Message = sprintf "Elements must not reference Fidelity.PSG graph/node symbol, PSGZipper, or TypeMapping '%s'." symbolUse.Symbol.DisplayName
            Code = "AXA005"
            Severity = Severity.Error
            Range = symbolUse.Range
            Fixes = []
          }
        | Ok false -> ()
        | Error reason ->
          diagnostics.Add { Type = "Alex analysis incomplete"; Message = reason; Code = "AXA000"; Severity = Severity.Error; Range = symbolUse.Range; Fixes = [] }

    let rec predicateEvidence (env: BindingEnv) visited (expression: FSharpExpr) =
      try
        match expression with
        | FSharpFieldGet(_, _, field) when field.Name = "Name" &&
            (field.DeclaringEntity |> Option.exists (fun entity -> entity.TryFullName = Some "Fidelity.PSG.NominalTypeIdentity" && entity.Assembly.SimpleName = "Fidelity.PSG")) -> true, []
        | Call(_, called, _, _, [argument]) when called.CompiledName = "Not" &&
            (called.DeclaringEntity |> Option.exists (fun entity -> entity.TryFullName = Some "Microsoft.FSharp.Core.Operators" && entity.Assembly.SimpleName = "FSharp.Core")) ->
          predicateEvidence env visited argument
        | Call(receiver, called, _, _, arguments) when called.CompiledName = "StartsWith" &&
            (called.DeclaringEntity |> Option.exists (fun entity ->
              let assembly = entity.Assembly.SimpleName
              entity.TryFullName = Some "System.String" &&
              (assembly = "mscorlib" || assembly = "netstandard" || assembly.StartsWith("System.")))) ->
          let resultType = called.ReturnParameter.Type
          let isBoolean = isBoolType resultType
          match receiver with
          | Some value when isBoolean ->
            (value :: arguments)
            |> List.fold (fun (found, errors) child ->
              let nextFound, nextErrors = predicateEvidence env visited child
              found || nextFound, errors @ nextErrors) (false, [])
          | _ -> false, [ "Cannot establish the shape of the System.String.StartsWith predicate." ]
        | Call(_, called, _, _, _) when not (called.CompiledName.StartsWith("op_")) -> false, []
        | Application _ | Lambda _ -> false, []
        | Sequential(_, second) -> predicateEvidence env visited second
        | Let((value, binding, _), body) ->
          predicateEvidence (addBinding value (bindingOfExpr binding) env) visited body
        | TupleGet(_, _, Value _) | FSharpFieldGet(Some (Value _), _, _) | UnionCaseGet(Value _, _, _, _) -> false, []
        | Value value ->
          match tryFindBinding value env with
          | Some _ when value.IsMember -> false, []
          | Some _ when value.IsMutable -> false, [ sprintf "Cannot establish nominal predicate provenance through mutable local '%s'." value.DisplayName ]
          | Some _ when visited |> List.exists ((=) value) -> false, [ sprintf "Cyclic nominal predicate provenance at local '%s'." value.DisplayName ]
          | Some info -> predicateEvidence env (value :: visited) info.Body
          | None -> false, []
        | _ ->
          expression.ImmediateSubExpressions
          |> Seq.fold (fun (found, errors) child ->
            let nextFound, nextErrors = predicateEvidence env visited child
            found || nextFound, errors @ nextErrors) (false, [])
      with error -> false, [ sprintf "Cannot inspect nominal predicate provenance: %s" error.Message ]

    let rec couldHoldDeclarationFacts (typ: FSharpType) =
      if typ.IsAbbreviation then couldHoldDeclarationFacts typ.AbbreviatedType
      elif typ.IsGenericParameter then true
      elif typ.HasTypeDefinition then
        let def = typ.TypeDefinition
        (def.Assembly.SimpleName = "FSharp.Core" && def.CompiledName = "FSharpMap`2") ||
        (def.TryFullName |> Option.exists (fun n ->
          n = "System.Object" ||
          n = "System.Collections.IDictionary" ||
          n = "System.Collections.Generic.IDictionary`2" ||
          n = "System.Collections.Generic.IReadOnlyDictionary`2" ||
          n = "Fidelity.PSG.BoundaryDeclarationFact")) ||
        (typ.GenericArguments |> Seq.exists couldHoldDeclarationFacts)
      else false

    let rec hasDeclarationFactsProvenance (env: BindingEnv) visited (expression: FSharpExpr) : bool * string list =
      try
        match expression with
        | FSharpFieldGet(_, _, field) when isDeclarationFactsField field -> true, []
        | Sequential(_, second) -> hasDeclarationFactsProvenance env visited second
        | Let((value, binding, _), body) ->
          hasDeclarationFactsProvenance (addBinding value (bindingOfExpr binding) env) visited body
        | Value value ->
          match tryFindBinding value env with
          | Some _ when value.IsMember -> false, []
          | Some _ when value.IsMutable ->
            if couldHoldDeclarationFacts value.FullType then
              false, [ sprintf "Cannot establish DeclarationFacts provenance through mutable local '%s'." value.DisplayName ]
            else false, []
          | Some _ when visited |> List.exists ((=) value) ->
            if couldHoldDeclarationFacts value.FullType then
              false, [ sprintf "Cyclic DeclarationFacts provenance at local '%s'." value.DisplayName ]
            else false, []
          | Some info -> hasDeclarationFactsProvenance env (value :: visited) info.Body
          | None -> false, []
        | _ -> false, []
      with error -> false, [ sprintf "Cannot inspect DeclarationFacts provenance: %s" error.Message ]

    let rec isPsgProjectionOrMap (env: BindingEnv) visited (expression: FSharpExpr) : bool * string list =
      try
        match expression with
        | FSharpFieldGet(receiverOpt, recordType, field) ->
          if field.DeclaringEntity |> Option.exists (fun e -> isPsgAssembly e.Assembly) then true, []
          else
            match typeFromPsg Set.empty recordType with
            | Ok true -> true, []
            | Error err -> false, [ err ]
            | Ok false ->
              match receiverOpt with
              | Some recv -> isPsgProjectionOrMap env visited recv
              | None -> false, []
        | Call(receiverOpt, called, _, _, _) ->
          if called.DeclaringEntity |> Option.exists (fun e -> isPsgAssembly e.Assembly) then true, []
          else
            match receiverOpt with
            | Some recv -> isPsgProjectionOrMap env visited recv
            | None -> false, []
        | Sequential(_, second) -> isPsgProjectionOrMap env visited second
        | Let((value, binding, _), body) ->
          isPsgProjectionOrMap (addBinding value (bindingOfExpr binding) env) visited body
        | Value value ->
          match typeFromPsg Set.empty value.FullType with
          | Ok true -> true, []
          | Error err -> false, [ err ]
          | Ok false ->
            match tryFindBinding value env with
            | Some _ when value.IsMember -> false, []
            | Some _ when value.IsMutable ->
              false, [ sprintf "Cannot establish PSG table provenance through mutable local '%s'." value.DisplayName ]
            | Some _ when visited |> List.exists ((=) value) ->
              false, [ sprintf "Cyclic PSG table provenance at local '%s'." value.DisplayName ]
            | Some info -> isPsgProjectionOrMap env (value :: visited) info.Body
            | None -> false, []
        | _ -> false, []
      with error -> false, [ sprintf "Cannot inspect PSG table provenance: %s" error.Message ]

    let isForeignDomainTable (env: BindingEnv) (tableExpr: FSharpExpr) =
      let rec hasForeignField visited expr =
        match expr with
        | FSharpFieldGet(receiverOpt, _, field) ->
          if field.Name = "Foreign" && (field.DeclaringEntity |> Option.exists (fun e -> isPsgAssembly e.Assembly)) then true
          else
            match field.DeclaringEntity with
            | Some e when isPsgAssembly e.Assembly && (e.DisplayName.Contains("Foreign") || (receiverOpt |> Option.exists (hasForeignField visited))) -> true
            | _ -> receiverOpt |> Option.exists (hasForeignField visited)
        | Sequential(_, second) -> hasForeignField visited second
        | Let((v, b, _), body) -> hasForeignField visited b || hasForeignField visited body
        | Value v when not v.IsMember && not v.IsMutable && not (visited |> List.exists ((=) v)) ->
          match tryFindBinding v env with
          | Some info -> hasForeignField (v :: visited) info.Body
          | None -> false
        | _ -> false
      hasForeignField [] tableExpr

    let isFocusNodeId (env: BindingEnv) (keyExpr: FSharpExpr) =
      let rec check visited expr =
        match expr with
        | FSharpFieldGet(_, nodeTyp, field) ->
          field.Name = "Id" && nodeTyp.HasTypeDefinition && isPsgEntity "Fidelity.PSG.SemanticNode" nodeTyp.TypeDefinition
        | Sequential(_, second) -> check visited second
        | Let((v, b, _), body) -> check (visited) body || (check visited b)
        | Value v when not v.IsMember && not v.IsMutable && not (visited |> List.exists ((=) v)) ->
          match tryFindBinding v env with
          | Some info -> check (v :: visited) info.Body
          | None -> false
        | _ -> false
      check [] keyExpr

    let isWitnessDomainDispatchLookup (env: BindingEnv) (scrutinee: FSharpExpr) =
      let rec checkLookup curEnv visited expr =
        match expr with
        | Call(Some receiver, called, _, _, [keyArg]) when called.CompiledName = "TryFind" ->
          isForeignDomainTable curEnv receiver && isFocusNodeId curEnv keyArg
        | Call(_, called, _, _, [keyArg; tableArg])
            when called.CompiledName = "TryFind" && (called.DeclaringEntity |> Option.exists isMapModule) ->
          isForeignDomainTable curEnv tableArg && isFocusNodeId curEnv keyArg
        | Let((v, b, _), body) ->
          checkLookup (addBinding v (bindingOfExpr b) curEnv) visited body
        | Sequential(_, second) ->
          checkLookup curEnv visited second
        | Value v when not v.IsMember && not v.IsMutable && not (visited |> List.exists ((=) v)) ->
          match tryFindBinding v curEnv with
          | Some info when info.Params.IsEmpty -> checkLookup curEnv (v :: visited) info.Body
          | _ -> false
        | _ -> false
      inWitnesses && checkLookup env [] scrutinee

    let rec publishedFactOptionProvenance
        (env: BindingEnv)
        (visited: FSharpMemberOrFunctionOrValue list)
        (factParams: FSharpMemberOrFunctionOrValue list)
        (onlyFactParams: bool)
        (expression: FSharpExpr) : bool * string list =
      try
        match expression with
        | Value v when List.contains v factParams -> true, []
        | Call(_, called, _, _, _) when not onlyFactParams && isRevisionTryNodeValue called -> true, []
        | Call(_, called, _, _, _) when not onlyFactParams && isRecallValue called -> true, []
        | Call(_, called, _, _, _)
            when not onlyFactParams &&
                 isOptionType called.ReturnParameter.Type &&
                 (called.DeclaringEntity |> Option.exists (fun e ->
                    e.Assembly.SimpleName = "Alex" &&
                    e.TryFullName = Some "Alex.Dialects.Core.Types.BoundaryAbi")) -> true, []
        | Call(Some receiver, called, _, _, _) when not onlyFactParams && called.CompiledName = "TryFind" ->
          isPsgProjectionOrMap env [] receiver
        | Call(_, called, _, _, [_; tableArg])
            when not onlyFactParams &&
                 called.CompiledName = "TryFind" &&
                 (called.DeclaringEntity |> Option.exists isMapModule) ->
          isPsgProjectionOrMap env [] tableArg
        | Call(_, called, _, _, arguments)
            when (called.DeclaringEntity |> Option.exists isOptionModule) &&
                 (called.CompiledName = "Map" || called.CompiledName = "Bind" || called.CompiledName = "Filter") ->
          match List.tryLast arguments with
          | Some optArg -> publishedFactOptionProvenance env visited factParams onlyFactParams optArg
          | None -> false, []
        | Call(_, called, _, _, [arg; target])
            when called.CompiledName = "op_PipeRight" &&
                 (called.DeclaringEntity |> Option.exists (fun e -> e.TryFullName = Some "Microsoft.FSharp.Core.Operators")) ->
          let rec unwrapPipe pipeEnv bodyExpr =
            match bodyExpr with
            | Lambda(paramVal, inner) ->
              publishedFactOptionProvenance (addBinding paramVal (bindingOfExpr arg) pipeEnv) visited factParams onlyFactParams inner
            | Let((v, b, _), inner) ->
              unwrapPipe (addBinding v (bindingOfExpr b) pipeEnv) inner
            | Sequential(_, inner) -> unwrapPipe pipeEnv inner
            | _ ->
              let head, prefixArgs = unwrapApplications bodyExpr
              match head with
              | Value fn when not (visited |> List.exists ((=) fn)) ->
                match tryFindBinding fn pipeEnv with
                | Some info ->
                  let callEnv = bindParams info.Params (prefixArgs @ [arg]) pipeEnv
                  publishedFactOptionProvenance callEnv (fn :: visited) factParams onlyFactParams info.Body
                | None -> false, []
              | _ -> false, []
          unwrapPipe env target
        | Call(None, called, _, _, args) when not (visited |> List.exists ((=) called)) ->
          match tryFindBinding called env with
          | Some info ->
            let callEnv = bindParams info.Params args env
            publishedFactOptionProvenance callEnv (called :: visited) factParams onlyFactParams info.Body
          | None -> false, []
        | Application _ ->
          let head, allArgs = unwrapApplications expression
          match head with
          | Value fn when not (visited |> List.exists ((=) fn)) ->
            match tryFindBinding fn env with
            | Some info ->
              let callEnv = bindParams info.Params allArgs env
              publishedFactOptionProvenance callEnv (fn :: visited) factParams onlyFactParams info.Body
            | None -> false, []
          | _ -> false, []
        | Sequential(_, second) ->
          publishedFactOptionProvenance env visited factParams onlyFactParams second
        | Let((value, binding, _), body) ->
          publishedFactOptionProvenance (addBinding value (bindingOfExpr binding) env) visited factParams onlyFactParams body
        | IfThenElse(_, thenExpr, elseExpr) ->
          let f1, e1 = publishedFactOptionProvenance env visited factParams onlyFactParams thenExpr
          let f2, e2 = publishedFactOptionProvenance env visited factParams onlyFactParams elseExpr
          f1 || f2, e1 @ e2
        | DecisionTree(_, targets) ->
          targets
          |> List.fold (fun (found, errs) (_, targetExpr) ->
            let f, e = publishedFactOptionProvenance env visited factParams onlyFactParams targetExpr
            found || f, errs @ e) (false, [])
        | Value value ->
          match tryFindBinding value env with
          | Some _ when value.IsMember -> false, []
          | Some _ when value.IsMutable ->
            false, [ sprintf "Cannot establish published-fact option provenance through mutable local '%s'." value.DisplayName ]
          | Some _ when visited |> List.exists ((=) value) ->
            false, [ sprintf "Cyclic published-fact option provenance at local '%s'." value.DisplayName ]
          | Some info ->
            publishedFactOptionProvenance env (value :: visited) factParams onlyFactParams info.Body
          | None -> false, []
        | _ -> false, []
      with error -> false, [ sprintf "Cannot inspect published-fact option provenance: %s" error.Message ]

    let isParserFailCall (called: FSharpMemberOrFunctionOrValue) =
      let name = called.DisplayName
      let fromCoreOps =
        called.DeclaringEntity |> Option.exists (fun e ->
          e.Assembly.SimpleName = "FSharp.Core" &&
          (e.TryFullName = Some "Microsoft.FSharp.Core.Operators" ||
           e.TryFullName = Some "Microsoft.FSharp.Core.ExtraTopLevelOperators" ||
           e.TryFullName = Some "Microsoft.FSharp.Core.PrintfModule"))
      let fromXParsec =
        called.DeclaringEntity |> Option.exists (fun e ->
          (e.Assembly.SimpleName = "XParsec" && e.TryFullName = Some "XParsec.Parsers") ||
          (e.Assembly.SimpleName = "Alex" && e.TryFullName = Some "Alex.XParsec.PSGCombinators"))
      let fromWitnessOutput =
        called.DeclaringEntity |> Option.exists (fun e ->
          e.Assembly.SimpleName = "Alex" &&
          e.TryFullName = Some "Alex.Traversal.TransferTypes.WitnessOutputModule")
      let fromAccumulatorError =
        called.DeclaringEntity |> Option.exists (fun e ->
          e.Assembly.SimpleName = "Alex" &&
          e.TryFullName = Some "Alex.Traversal.TransferTypes.MLIRAccumulatorModule") &&
        name = "addError"
      (fromXParsec && (name = "fail" || name = "failMessage")) ||
      (fromWitnessOutput && (name = "error" || name = "errorCoded" || name = "errorDiag")) ||
      fromAccumulatorError ||
      (fromCoreOps && (called.CompiledName = "FailWith" || called.CompiledName = "InvalidOp" || called.CompiledName = "Raise" || called.CompiledName = "Reraise" || called.CompiledName = "PrintFormatToStringThenFail" || name = "failwithf"))

    let isWitnessOutputSkipValue (value: FSharpMemberOrFunctionOrValue) =
      (value.DisplayName = "skip" || value.CompiledName = "get_skip" || value.CompiledName = "skip") &&
      (value.DeclaringEntity |> Option.exists (fun e ->
        e.Assembly.SimpleName = "Alex" &&
        e.TryFullName = Some "Alex.Traversal.TransferTypes.WitnessOutputModule"))

    let rec isXParsecReaderType (typ: FSharpType) =
      if typ.IsAbbreviation then isXParsecReaderType typ.AbbreviatedType
      elif typ.HasTypeDefinition then
        let def = typ.TypeDefinition
        def.Assembly.SimpleName = "XParsec" && (def.DisplayName = "Reader" || def.DisplayName = "IReadable")
      else false

    let rec unwrapAppliedHead
        (env: BindingEnv)
        (visited: FSharpMemberOrFunctionOrValue list)
        (onBuiltinCall: FSharpMemberOrFunctionOrValue -> bool)
        (onBody: BindingEnv -> FSharpMemberOrFunctionOrValue list -> FSharpExpr -> bool)
        (headExpr: FSharpExpr)
        (args: FSharpExpr list) : bool =
      match headExpr, args with
      | Let((v, b, _), inner), _ ->
        unwrapAppliedHead (addBinding v (bindingOfExpr b) env) visited onBuiltinCall onBody inner args
      | Lambda(paramVal, inner), arg0 :: restArgs ->
        unwrapAppliedHead (addBinding paramVal (bindingOfExpr arg0) env) visited onBuiltinCall onBody inner restArgs
      | Sequential(_, inner), _
      | Coerce(_, inner), _
      | TypeLambda(_, inner), _ ->
        unwrapAppliedHead env visited onBuiltinCall onBody inner args
      | Application _, _ ->
        let innerHead, innerArgs = unwrapApplications headExpr
        unwrapAppliedHead env visited onBuiltinCall onBody innerHead (innerArgs @ args)
      | Call(_, called, _, _, callArgs), _ ->
        onBuiltinCall called ||
        (not (visited |> List.exists ((=) called)) &&
         let totalArgs = callArgs @ args
         match tryFindBinding called env with
         | Some info when totalArgs.Length >= info.Params.Length ->
           let callEnv = bindParams info.Params totalArgs env
           unwrapAppliedHead callEnv (called :: visited) onBuiltinCall onBody info.Body (List.skip info.Params.Length totalArgs)
         | _ when List.isEmpty args -> onBody env visited headExpr
         | _ -> false)
      | Value fn, allArgs when not (visited |> List.exists ((=) fn)) ->
        match tryFindBinding fn env with
        | Some info when allArgs.Length >= info.Params.Length ->
          let callEnv = bindParams info.Params allArgs env
          unwrapAppliedHead callEnv (fn :: visited) onBuiltinCall onBody info.Body (List.skip info.Params.Length allArgs)
        | _ -> false
      | _, [] -> onBody env visited headExpr
      | _ -> false

    let rec containsUnconditionalRefusal (env: BindingEnv) (visited: FSharpMemberOrFunctionOrValue list) (expr: FSharpExpr) : bool =
      let isParserBuilderEntity (entity: FSharpEntity) =
        entity.Assembly.SimpleName = "XParsec" && entity.TryFullName = Some "XParsec.Combinators.ParserCE"
      match expr with
      | Call(_, called, _, _, [arg; target])
          when called.CompiledName = "op_PipeRight" &&
               (called.DeclaringEntity |> Option.exists (fun e -> e.TryFullName = Some "Microsoft.FSharp.Core.Operators")) ->
        unwrapAppliedHead env visited isParserFailCall containsUnconditionalRefusal target [arg]
      | Call(Some _, called, _, _, [inner])
          when (called.CompiledName = "ReturnFrom" || called.CompiledName = "Delay") &&
               (called.DeclaringEntity |> Option.exists isParserBuilderEntity) ->
        let body =
          match inner with
          | Lambda(_, thunkBody) when called.CompiledName = "Delay" -> thunkBody
          | _ -> inner
        containsUnconditionalRefusal env visited body
      | Call(Some _, called, _, _, [_; Lambda(_, nextBody)])
          when called.CompiledName = "Bind" &&
               (called.DeclaringEntity |> Option.exists isParserBuilderEntity) ->
        containsUnconditionalRefusal env visited nextBody
      | Call(_, called, _, _, args) ->
        isParserFailCall called ||
        (not (visited |> List.exists ((=) called)) &&
         match tryFindBinding called env with
         | Some info when args.Length >= info.Params.Length ->
           let callEnv = bindParams info.Params args env
           unwrapAppliedHead callEnv (called :: visited) isParserFailCall containsUnconditionalRefusal info.Body (List.skip info.Params.Length args)
         | _ -> false)
      | Lambda(paramVal, body) when isXParsecReaderType paramVal.FullType ->
        containsUnconditionalRefusal env visited body
      | Application _ ->
        let head, allArgs = unwrapApplications expr
        unwrapAppliedHead env visited isParserFailCall containsUnconditionalRefusal head allArgs
      | Value v when not v.IsMember && not v.IsMutable && not (visited |> List.exists ((=) v)) ->
        match tryFindBinding v env with
        | Some info when info.Params.IsEmpty -> containsUnconditionalRefusal env (v :: visited) info.Body
        | _ -> false
      | Let((v, b, _), body) ->
        containsUnconditionalRefusal (addBinding v (bindingOfExpr b) env) visited body
      | LetRec(recBindings, body) ->
        let recEnv =
          recBindings |> List.fold (fun acc (v, rhs, _) -> addBinding v (bindingOfExpr rhs) acc) env
        containsUnconditionalRefusal recEnv visited body
      | Sequential(first, second) ->
        containsUnconditionalRefusal env visited first || containsUnconditionalRefusal env visited second
      | Coerce(_, body) | TypeLambda(_, body) ->
        containsUnconditionalRefusal env visited body
      | IfThenElse(_, thenExpr, elseExpr) ->
        containsUnconditionalRefusal env visited thenExpr && containsUnconditionalRefusal env visited elseExpr
      | DecisionTree(_, targets) ->
        not (List.isEmpty targets) && (targets |> List.forall (snd >> containsUnconditionalRefusal env visited))
      | _ -> false

    let rec unwrapUnitApplication (expr: FSharpExpr) =
      match expr with
      | Application(inner, _, _) -> unwrapUnitApplication inner
      | _ -> expr

    let rec isAllowedBoolNoneBranch
        (env: BindingEnv)
        (visited: FSharpMemberOrFunctionOrValue list)
        (factParams: FSharpMemberOrFunctionOrValue list)
        (onlyFactParams: bool)
        (expression: FSharpExpr) : bool =
      if not (isBoolType expression.Type) then false
      else
        match expression with
        | Const(:? bool as value, _) -> not value
        | Let((v, b, _), body) ->
          isAllowedBoolNoneBranch (addBinding v (bindingOfExpr b) env) visited factParams onlyFactParams body
        | Sequential(_, second) ->
          isAllowedBoolNoneBranch env visited factParams onlyFactParams second
        | Value v when not v.IsMember && not v.IsMutable && not (visited |> List.exists ((=) v)) ->
          match tryFindBinding v env with
          | Some info when info.Params.IsEmpty ->
            isAllowedBoolNoneBranch env (v :: visited) factParams onlyFactParams info.Body
          | _ -> false
        | IfThenElse(_, thenExpr, elseExpr) ->
          isAllowedBoolNoneBranch env visited factParams onlyFactParams thenExpr &&
          isAllowedBoolNoneBranch env visited factParams onlyFactParams elseExpr
        | Call(_, called, _, _, [optArg])
            when (called.DeclaringEntity |> Option.exists isOptionModule) && called.CompiledName = "IsSome" ->
          publishedFactOptionProvenance env [] factParams onlyFactParams optArg |> fst
        | Call(_, called, _, _, [_; optArg])
            when (called.DeclaringEntity |> Option.exists isOptionModule) && called.CompiledName = "Exists" ->
          publishedFactOptionProvenance env [] factParams onlyFactParams optArg |> fst
        | Call(_, called, _, _, [arg; target])
            when called.CompiledName = "op_PipeRight" &&
                 (called.DeclaringEntity |> Option.exists (fun e -> e.TryFullName = Some "Microsoft.FSharp.Core.Operators")) ->
          let rec targetIsBoolLookup pipeEnv targetExpr =
            match targetExpr with
            | Lambda(paramVal, inner) ->
              isAllowedBoolNoneBranch (addBinding paramVal (bindingOfExpr arg) pipeEnv) visited factParams onlyFactParams inner
            | Let((v, b, _), inner) ->
              targetIsBoolLookup (addBinding v (bindingOfExpr b) pipeEnv) inner
            | Sequential(_, inner) -> targetIsBoolLookup pipeEnv inner
            | Call(_, c, _, _, _)
                when (c.DeclaringEntity |> Option.exists isOptionModule) && (c.CompiledName = "Exists" || c.CompiledName = "IsSome") ->
              publishedFactOptionProvenance pipeEnv [] factParams onlyFactParams arg |> fst
            | Value c when (c.DeclaringEntity |> Option.exists isOptionModule) && c.CompiledName = "IsSome" ->
              publishedFactOptionProvenance pipeEnv [] factParams onlyFactParams arg |> fst
            | _ -> false
          targetIsBoolLookup env target
        | _ -> false

    let rec isAllowedNoneBranch
        (env: BindingEnv)
        (visited: FSharpMemberOrFunctionOrValue list)
        (factParams: FSharpMemberOrFunctionOrValue list)
        (onlyFactParams: bool)
        (allowFalseBool: bool)
        (allowSkipDomain: bool)
        (expression: FSharpExpr) : bool =
      match expression with
      | Const(:? bool as value, _) -> allowFalseBool && not value
      | _ when allowFalseBool && isBoolType expression.Type && isAllowedBoolNoneBranch env [] factParams onlyFactParams expression -> true
      | _ when containsUnconditionalRefusal env [] expression -> true
      | Value v when allowSkipDomain && isWitnessOutputSkipValue v -> true
      | NewUnionCase(unionType, unionCase, args) when unionType.HasTypeDefinition ->
        let def = unionType.TypeDefinition
        (isOptionEntity def && unionCase.Name = "None") ||
        (isResultEntity def && unionCase.Name = "Error") ||
        (isResultEntity def && unionCase.Name = "Ok" &&
         match args with
         | [inner] -> isAllowedNoneBranch env visited factParams onlyFactParams allowFalseBool allowSkipDomain inner
         | _ -> false)
      | Call(_, called, _, _, _) when isParserFailCall called -> true
      | Call(_, called, _, _, []) when allowSkipDomain && isWitnessOutputSkipValue called -> true
      | Call(Some _, called, _, _, [inner])
          when called.CompiledName = "ReturnFrom" || called.CompiledName = "Return" ->
        isAllowedNoneBranch env visited factParams onlyFactParams allowFalseBool allowSkipDomain inner
      | Call(Some _, called, _, _, [inner]) when called.CompiledName = "Delay" ->
        let body =
          match inner with
          | Lambda(_, thunkBody) -> thunkBody
          | _ -> inner
        isAllowedNoneBranch env visited factParams onlyFactParams allowFalseBool allowSkipDomain body
      | Call(_, called, _, _, args) when not (visited |> List.exists ((=) called)) ->
        let isAllowedLeaf c = isParserFailCall c || (allowSkipDomain && isWitnessOutputSkipValue c)
        let cont cEnv cVis cBody = isAllowedNoneBranch cEnv cVis factParams onlyFactParams allowFalseBool allowSkipDomain cBody
        match tryFindBinding called env with
        | Some info when args.Length >= info.Params.Length ->
          let callEnv = bindParams info.Params args env
          unwrapAppliedHead callEnv (called :: visited) isAllowedLeaf cont info.Body (List.skip info.Params.Length args)
        | _ -> false
      | Application _ ->
        let isAllowedLeaf c = isParserFailCall c || (allowSkipDomain && isWitnessOutputSkipValue c)
        let cont cEnv cVis cBody = isAllowedNoneBranch cEnv cVis factParams onlyFactParams allowFalseBool allowSkipDomain cBody
        let head, allArgs = unwrapApplications expression
        unwrapAppliedHead env visited isAllowedLeaf cont head allArgs
      | Let((v, b, _), body) ->
        isAllowedNoneBranch (addBinding v (bindingOfExpr b) env) visited factParams onlyFactParams allowFalseBool allowSkipDomain body
      | LetRec(recBindings, body) ->
        let recEnv =
          recBindings |> List.fold (fun acc (v, rhs, _) -> addBinding v (bindingOfExpr rhs) acc) env
        isAllowedNoneBranch recEnv visited factParams onlyFactParams allowFalseBool allowSkipDomain body
      | Value v when not v.IsMember && not v.IsMutable && not (visited |> List.exists ((=) v)) ->
        match tryFindBinding v env with
        | Some info when info.Params.IsEmpty ->
          isAllowedNoneBranch env (v :: visited) factParams onlyFactParams allowFalseBool allowSkipDomain info.Body
        | _ -> false
      | Sequential(_, second) ->
        isAllowedNoneBranch env visited factParams onlyFactParams allowFalseBool allowSkipDomain second
      | Coerce(_, body) | TypeLambda(_, body) ->
        isAllowedNoneBranch env visited factParams onlyFactParams allowFalseBool allowSkipDomain body
      | IfThenElse(_, thenExpr, elseExpr) ->
        isAllowedNoneBranch env visited factParams onlyFactParams allowFalseBool allowSkipDomain thenExpr &&
        isAllowedNoneBranch env visited factParams onlyFactParams allowFalseBool allowSkipDomain elseExpr
      | DecisionTree(nestedDecision, targets) ->
        let (nestedNone, _), _ = collectNoneReachedTargets env factParams onlyFactParams nestedDecision
        if not (Set.isEmpty nestedNone) then
          nestedNone
          |> Seq.forall (fun idx ->
            idx >= 0 && idx < targets.Length &&
            isAllowedNoneBranch env visited factParams onlyFactParams allowFalseBool allowSkipDomain (snd targets[idx]))
        else
          not (List.isEmpty targets) &&
          (targets |> List.forall (snd >> isAllowedNoneBranch env visited factParams onlyFactParams allowFalseBool allowSkipDomain))
      | _ -> false

    and isAllowedThunkBranch
        (env: BindingEnv)
        (visited: FSharpMemberOrFunctionOrValue list)
        (factParams: FSharpMemberOrFunctionOrValue list)
        (onlyFactParams: bool)
        (thunkExpr: FSharpExpr) : bool =
      match thunkExpr with
      | Lambda(_, body) ->
        isAllowedNoneBranch env [] factParams onlyFactParams false false body
      | Let((v, b, _), body) ->
        isAllowedThunkBranch (addBinding v (bindingOfExpr b) env) visited factParams onlyFactParams body
      | Sequential(_, second) | Coerce(_, second) | TypeLambda(_, second) ->
        isAllowedThunkBranch env visited factParams onlyFactParams second
      | Value v when not v.IsMember && not v.IsMutable && not (visited |> List.exists ((=) v)) ->
        match tryFindBinding v env with
        | Some info when info.Params.Length = 1 ->
          isAllowedNoneBranch env [] factParams onlyFactParams false false info.Body
        | Some info when info.Params.IsEmpty ->
          isAllowedThunkBranch env (v :: visited) factParams onlyFactParams info.Body
        | _ -> false
      | _ -> false

    and collectNoneReachedTargets
        (env: BindingEnv)
        (factParams: FSharpMemberOrFunctionOrValue list)
        (onlyFactParams: bool)
        (decisionExpr: FSharpExpr) : (Set<int> * bool) * string list =
      match decisionExpr with
      | IfThenElse(guard, thenExpr, elseExpr) ->
        let optionTest =
          match unwrapUnitApplication guard with
          | UnionCaseTest(scrutinee, unionType, unionCase)
              when unionType.HasTypeDefinition && isOptionEntity unionType.TypeDefinition ->
            let found, errs = publishedFactOptionProvenance env [] factParams onlyFactParams scrutinee
            if found then Some (unionCase.Name = "None", isWitnessDomainDispatchLookup env scrutinee, errs) else None
          | Call(Some scrutinee, called, _, _, [])
          | Call(None, called, _, _, [scrutinee])
              when (called.CompiledName = "get_IsSome" || called.CompiledName = "get_IsNone") &&
                   isOptionEntity (called.DeclaringEntity |> Option.defaultValue (scrutinee.Type.TypeDefinition)) ->
            let found, errs = publishedFactOptionProvenance env [] factParams onlyFactParams scrutinee
            if found then Some (called.CompiledName = "get_IsNone", isWitnessDomainDispatchLookup env scrutinee, errs) else None
          | _ -> None
        let (tSet, tSkip), tErrs = collectNoneReachedTargets env factParams onlyFactParams thenExpr
        let (eSet, eSkip), eErrs = collectNoneReachedTargets env factParams onlyFactParams elseExpr
        let rec allSuccessIndices expr =
          match expr with
          | DecisionTreeSuccess(idx, _) -> Set.singleton idx
          | IfThenElse(_, a, b) -> Set.union (allSuccessIndices a) (allSuccessIndices b)
          | Let(_, body) | Sequential(_, body) -> allSuccessIndices body
          | _ -> Set.empty
        match optionTest with
        | Some (trueIsNone, skipDomain, errs) ->
          let branchSet = if trueIsNone then allSuccessIndices thenExpr else allSuccessIndices elseExpr
          (Set.unionMany [branchSet; tSet; eSet], skipDomain && (tSet.IsEmpty && eSet.IsEmpty || tSkip || eSkip)), errs @ tErrs @ eErrs
        | None ->
          (Set.union tSet eSet, tSkip && eSkip), tErrs @ eErrs
      | DecisionTreeSuccess _ -> (Set.empty, false), []
      | Let((v, b, _), body) ->
        collectNoneReachedTargets (addBinding v (bindingOfExpr b) env) factParams onlyFactParams body
      | Sequential(_, body) -> collectNoneReachedTargets env factParams onlyFactParams body
      | _ -> (Set.empty, false), []

    let rec containsSemanticKindOrRevisionNodes (expression: FSharpExpr) : bool =
      let isHere =
        match expression with
        | UnionCaseTest(_, typ, _)
        | UnionCaseTag(_, typ)
        | UnionCaseGet(_, typ, _, _)
        | NewUnionCase(typ, _, _) -> isSemanticKindType typ
        | FSharpFieldGet(_, _, field) -> isRevisionNodesField field
        | Call(_, called, _, _, _) -> isRevisionTryNodeValue called
        | Value v -> isRevisionTryNodeValue v
        | _ -> false
      isHere || (expression.ImmediateSubExpressions |> Seq.exists containsSemanticKindOrRevisionNodes)

    let rec exprReferencesValue (target: FSharpMemberOrFunctionOrValue) (expression: FSharpExpr) : bool =
      let isHere =
        match expression with
        | Call(_, called, _, _, _) -> called = target
        | Value v -> v = target
        | _ -> false
      isHere || (expression.ImmediateSubExpressions |> Seq.exists (exprReferencesValue target))

    let isRecursiveBinding (value: FSharpMemberOrFunctionOrValue) (body: FSharpExpr) =
      (recursiveHeadRanges |> List.exists (fun r -> Range.rangeContainsRange r value.DeclarationLocation)) ||
      exprReferencesValue value body

    let isSyntheticRevisionCopyRange (syntheticRanges: range list) (expr: FSharpExpr) =
      syntheticRanges |> List.exists ((=) expr.Range)

    let isAllowedContainsKeyCall (fn: FSharpMemberOrFunctionOrValue) =
      (fn.CompiledName = "ContainsKey" || fn.CompiledName = "containsKey") &&
      (fn.DeclaringEntity |> Option.exists (fun entity ->
        entity.Assembly.SimpleName = "FSharp.Core" &&
        (isMapModule entity || entity.CompiledName = "FSharpMap`2")))

    let rec targetIsContainsKey (targetExpr: FSharpExpr) =
      match targetExpr with
      | Lambda(paramVal, inner) ->
        let rec checkInner body =
          match body with
          | Let(_, rest) | Sequential(_, rest) -> checkInner rest
          | Call(None, c, _, _, [ _; Value p2 ]) when p2 = paramVal -> isAllowedContainsKeyCall c
          | Call(Some (Value p2), c, _, _, [ _ ]) when p2 = paramVal -> isAllowedContainsKeyCall c
          | _ -> false
        checkInner inner
      | Call(None, c, _, _, _) -> isAllowedContainsKeyCall c
      | Value c -> isAllowedContainsKeyCall c
      | Let(_, inner) | Sequential(_, inner) -> targetIsContainsKey inner
      | _ -> false

    let fallbackArgForCall (env: BindingEnv) (factParams: FSharpMemberOrFunctionOrValue list) (onlyFactParams: bool) (called: FSharpMemberOrFunctionOrValue) (arguments: FSharpExpr list) =
      let fromOptionModule = called.DeclaringEntity |> Option.exists isOptionModule
      let fromOperators =
        called.DeclaringEntity |> Option.exists (fun e ->
          e.Assembly.SimpleName = "FSharp.Core" &&
          (e.TryFullName = Some "Microsoft.FSharp.Core.Operators" ||
           e.TryFullName = Some "Microsoft.FSharp.Core.ExtraTopLevelOperators"))
      match fromOptionModule, fromOperators, called.CompiledName, arguments with
      | true, _, "DefaultValue", [fallbackArg; optArg] ->
        if isAllowedNoneBranch env [] factParams onlyFactParams false false fallbackArg then None else Some optArg
      | true, _, "DefaultWith", [thunkArg; optArg] ->
        if isAllowedThunkBranch env [] factParams onlyFactParams thunkArg then None else Some optArg
      | true, _, ("OrElse" | "OrElseWith"), [_; optArg] ->
        Some optArg
      | true, _, ("ForAll" | "Iterate"), [_; optArg] ->
        Some optArg
      | true, _, ("ToList" | "ToArray" | "ToSeq" | "Count" | "ToObj"), [optArg] ->
        Some optArg
      | true, _, "Fold", [_; _; optArg] ->
        Some optArg
      | true, _, "FoldBack", [_; optArg; _] ->
        Some optArg
      | _, true, "DefaultArg", [optArg; fallbackArg] ->
        if isAllowedNoneBranch env [] factParams onlyFactParams false false fallbackArg then None else Some optArg
      | _ -> None

    let rec helperCollapsesFactParam
        (env: BindingEnv)
        (visitedHelpers: FSharpMemberOrFunctionOrValue list)
        (factParams: FSharpMemberOrFunctionOrValue list)
        (expr: FSharpExpr) : bool =
      match expr with
      | Let((v, b, _), body) ->
        helperCollapsesFactParam env visitedHelpers factParams b ||
        helperCollapsesFactParam (addBinding v (bindingOfExpr b) env) visitedHelpers factParams body
      | LetRec(recBindings, body) ->
        let recEnv =
          recBindings |> List.fold (fun acc (v, rhs, _) -> addBinding v (bindingOfExpr rhs) acc) env
        (recBindings |> List.exists (fun (_, rhs, _) -> helperCollapsesFactParam recEnv visitedHelpers factParams rhs)) ||
        helperCollapsesFactParam recEnv visitedHelpers factParams body
      | Call(receiverOpt, called, _, _, arguments) ->
        let directFallback =
          match fallbackArgForCall env factParams true called arguments with
          | Some optArg -> publishedFactOptionProvenance env [] factParams true optArg |> fst
          | None -> false
        let nestedHelperFallback =
          match called.CompiledName, arguments with
          | "op_PipeRight", [arg; target]
              when (called.DeclaringEntity |> Option.exists (fun e -> e.TryFullName = Some "Microsoft.FSharp.Core.Operators")) ->
            let pipedArgFact = publishedFactOptionProvenance env [] factParams true arg |> fst
            let targetResult =
              let rec inspectTarget pipeEnv t =
                match t with
                | Lambda(paramVal, inner) ->
                  helperCollapsesFactParam (addBinding paramVal (bindingOfExpr arg) pipeEnv) visitedHelpers factParams inner
                | Let((v, b, _), inner) -> inspectTarget (addBinding v (bindingOfExpr b) pipeEnv) inner
                | Sequential(_, inner) -> inspectTarget pipeEnv inner
                | _ when pipedArgFact ->
                  let head, prefixArgs = unwrapApplications t
                  match head with
                  | Value fn when not (visitedHelpers |> List.exists ((=) fn)) ->
                    checkHelperArgs env visitedHelpers factParams fn (prefixArgs @ [arg])
                  | _ -> false
                | _ -> false
              inspectTarget env target
            targetResult
          | _ when not (visitedHelpers |> List.exists ((=) called)) ->
            checkHelperArgs env visitedHelpers factParams called arguments
          | _ -> false
        directFallback ||
        nestedHelperFallback ||
        (receiverOpt |> Option.exists (helperCollapsesFactParam env visitedHelpers factParams)) ||
        (arguments |> List.exists (helperCollapsesFactParam env visitedHelpers factParams))
      | Application _ ->
        let head, allArgs = unwrapApplications expr
        let appHit =
          match head with
          | Value fn when not (visitedHelpers |> List.exists ((=) fn)) ->
            checkHelperArgs env visitedHelpers factParams fn allArgs
          | _ -> false
        appHit || (expr.ImmediateSubExpressions |> Seq.exists (helperCollapsesFactParam env visitedHelpers factParams))
      | DecisionTree(decisionExpr, targets) ->
        let (noneIndices, _), _ = collectNoneReachedTargets env factParams true decisionExpr
        let hitTarget =
          noneIndices
          |> Seq.exists (fun idx ->
            idx >= 0 && idx < targets.Length &&
            not (isAllowedNoneBranch env [] factParams true true false (snd targets[idx])))
        let rec checkDecisionSpine spineEnv spineExpr =
          match spineExpr with
          | IfThenElse(guard, thenExpr, elseExpr) ->
            helperCollapsesFactParam spineEnv visitedHelpers factParams guard ||
            checkDecisionSpine spineEnv thenExpr ||
            checkDecisionSpine spineEnv elseExpr
          | Let((v, b, _), body) ->
            helperCollapsesFactParam spineEnv visitedHelpers factParams b ||
            checkDecisionSpine (addBinding v (bindingOfExpr b) spineEnv) body
          | Sequential(first, second) ->
            helperCollapsesFactParam spineEnv visitedHelpers factParams first ||
            checkDecisionSpine spineEnv second
          | other -> helperCollapsesFactParam spineEnv visitedHelpers factParams other
        hitTarget ||
        checkDecisionSpine env decisionExpr ||
        (targets |> List.exists (snd >> helperCollapsesFactParam env visitedHelpers factParams))
      | IfThenElse(guard, thenExpr, elseExpr) ->
        let hitGuard =
          match unwrapUnitApplication guard with
          | UnionCaseTest(scrutinee, unionType, unionCase)
              when unionType.HasTypeDefinition && isOptionEntity unionType.TypeDefinition ->
            let found, _ = publishedFactOptionProvenance env [] factParams true scrutinee
            let noneExpr = if unionCase.Name = "None" then thenExpr else elseExpr
            found && not (isAllowedNoneBranch env [] factParams true true false noneExpr)
          | Call(Some scrutinee, called, _, _, [])
          | Call(None, called, _, _, [scrutinee])
              when called.CompiledName = "get_IsSome" && (called.DeclaringEntity |> Option.exists isOptionEntity) ->
            let found, _ = publishedFactOptionProvenance env [] factParams true scrutinee
            found && not (isAllowedNoneBranch env [] factParams true true false elseExpr)
          | Call(Some scrutinee, called, _, _, [])
          | Call(None, called, _, _, [scrutinee])
              when called.CompiledName = "get_IsNone" && (called.DeclaringEntity |> Option.exists isOptionEntity) ->
            let found, _ = publishedFactOptionProvenance env [] factParams true scrutinee
            found && not (isAllowedNoneBranch env [] factParams true true false thenExpr)
          | Call(_, called, _, _, [scrutinee])
              when (called.DeclaringEntity |> Option.exists isOptionModule) &&
                   (called.CompiledName = "IsSome" || called.CompiledName = "IsNone") ->
            let found, _ = publishedFactOptionProvenance env [] factParams true scrutinee
            let noneExpr = if called.CompiledName = "IsNone" then thenExpr else elseExpr
            found && not (isAllowedNoneBranch env [] factParams true true false noneExpr)
          | _ -> false
        hitGuard ||
        helperCollapsesFactParam env visitedHelpers factParams guard ||
        helperCollapsesFactParam env visitedHelpers factParams thenExpr ||
        helperCollapsesFactParam env visitedHelpers factParams elseExpr
      | _ ->
        expr.ImmediateSubExpressions |> Seq.exists (helperCollapsesFactParam env visitedHelpers factParams)

    and checkHelperArgs
        (env: BindingEnv)
        (visitedHelpers: FSharpMemberOrFunctionOrValue list)
        (factParams: FSharpMemberOrFunctionOrValue list)
        (fn: FSharpMemberOrFunctionOrValue)
        (args: FSharpExpr list) : bool =
      match tryFindBinding fn env with
      | Some info when info.Params.Length > 0 && args.Length >= info.Params.Length ->
        let boundParams =
          List.zip info.Params (List.take info.Params.Length args)
          |> List.choose (fun (p, a) ->
            if publishedFactOptionProvenance env [] factParams (not factParams.IsEmpty) a |> fst then Some p else None)
        if List.isEmpty boundParams then false
        else
          let callEnv = bindParams info.Params args env
          helperCollapsesFactParam callEnv (fn :: visitedHelpers) boundParams info.Body
      | _ -> false

    let rec walkExpr (env: BindingEnv) (enclosingFunc: string) (syntheticRevisionRanges: range list) (expression: FSharpExpr) : BoundaryHits =
      match expression with
      | NewRecord(recordType, args) ->
        let hereDiags =
          [ if recordType.HasTypeDefinition &&
               recordType.TypeDefinition.Assembly.SimpleName = "Fidelity.PSG" &&
               (recordType.TypeDefinition.FullName = "Fidelity.PSG.Revision" ||
                recordType.TypeDefinition.FullName = "Fidelity.PSG.SemanticNode") then
              yield {
                Type = "Alex published graph boundary"
                Message = "Alex must not construct or update published PSG records."
                Code = "AXA001"
                Severity = Severity.Error
                Range = expression.Range
                Fixes = []
              }
            if inImmutableLayer && recordType.HasTypeDefinition && isFSharpRefEntity recordType.TypeDefinition then
              yield {
                Type = "Alex layer purity"
                Message = "Mutable ref cells (FSharpRef) are forbidden in non-traversal Alex layers."
                Code = "AXA005"
                Severity = Severity.Error
                Range = expression.Range
                Fixes = []
              } ]
        let nextSynthetic =
          if recordType.HasTypeDefinition && isPsgEntity "Fidelity.PSG.Revision" recordType.TypeDefinition then
            expression.Range :: syntheticRevisionRanges
          else syntheticRevisionRanges
        let childHits = collectHits args (walkExpr env enclosingFunc nextSynthetic)
        mergeHits { emptyHits with Diagnostics = hereDiags } childHits
      | Let((value, binding, _), body) ->
        let hereDiags =
          if inImmutableLayer && value.IsMutable && not value.IsCompilerGenerated then
            [ { Type = "Alex layer purity"
                Message = sprintf "Mutable local '%s' is forbidden in non-traversal Alex layers." value.DisplayName
                Code = "AXA005"
                Severity = Severity.Error
                Range = value.DeclarationLocation
                Fixes = [] } ]
          else []
        let bindingHits = walkExpr env enclosingFunc syntheticRevisionRanges binding
        let bodyEnv = addBinding value (bindingOfExpr binding) env
        let bodyHits = walkExpr bodyEnv enclosingFunc syntheticRevisionRanges body
        mergeHits { emptyHits with Diagnostics = hereDiags } (mergeHits bindingHits bodyHits)
      | LetRec(recBindings, body) ->
        let recEnv =
          recBindings |> List.fold (fun acc (value, rhs, _) -> addBinding value (bindingOfExpr rhs) acc) env
        let recHits =
          collectHits recBindings (fun (value, rhs, _) ->
            let mutDiag =
              if inImmutableLayer && value.IsMutable && not value.IsCompilerGenerated then
                [ { Type = "Alex layer purity"
                    Message = sprintf "Mutable local '%s' is forbidden in non-traversal Alex layers." value.DisplayName
                    Code = "AXA005"
                    Severity = Severity.Error
                    Range = value.DeclarationLocation
                    Fixes = [] } ]
              else []
            let axa004 =
              if containsSemanticKindOrRevisionNodes rhs then
                let targetName =
                  if enclosingFunc = "<init>" || enclosingFunc = value.DisplayName then value.DisplayName
                  else sprintf "%s.%s" enclosingFunc value.DisplayName
                [ { Target = targetName; Range = value.DeclarationLocation } ]
              else []
            let rhsHits = walkExpr recEnv enclosingFunc syntheticRevisionRanges rhs
            mergeHits { emptyHits with Diagnostics = mutDiag; Axa004 = axa004 } rhsHits)
        let bodyHits = walkExpr recEnv enclosingFunc syntheticRevisionRanges body
        mergeHits recHits bodyHits
      | FSharpFieldGet(receiverOpt, _, field) ->
        let axa003 =
          if not isZipperSubstrate && isRevisionNodesField field && not (isSyntheticRevisionCopyRange syntheticRevisionRanges expression) then
            [ { Target = enclosingFunc; Range = expression.Range } ]
          else []
        let recvHits =
          receiverOpt
          |> Option.map (walkExpr env enclosingFunc syntheticRevisionRanges)
          |> Option.defaultValue emptyHits
        mergeHits { emptyHits with Axa003 = axa003 } recvHits
      | Value v ->
        let axa003 =
          if not isZipperSubstrate && isRevisionTryNodeValue v then
            [ { Target = enclosingFunc; Range = expression.Range } ]
          else []
        { emptyHits with Axa003 = axa003 }
      | Coerce(_, input) ->
        let found, errs = hasDeclarationFactsProvenance env [] input
        let hereDiags =
          [ if found then
              yield {
                Type = "Alex published graph boundary"
                Message = "Alex must not read string payloads or iterate entries of BoundaryImport.DeclarationFacts; only ContainsKey is permitted."
                Code = "AXA006"
                Severity = Severity.Error
                Range = expression.Range
                Fixes = []
              }
            for err in errs |> List.distinct do
              yield { Type = "Alex analysis incomplete"; Message = err; Code = "AXA000"; Severity = Severity.Error; Range = expression.Range; Fixes = [] } ]
        mergeHits { emptyHits with Diagnostics = hereDiags } (walkExpr env enclosingFunc syntheticRevisionRanges input)
      | Call(receiverOpt, called, _, _, arguments) ->
        let range = expression.Range
        let isEnsure =
          called.DisplayName = "ensure" &&
          (called.DeclaringEntity |> Option.exists (fun entity -> entity.TryFullName = Some "Alex.XParsec.PSGCombinators" && entity.Assembly.SimpleName = "Alex"))
        let axa002Diags =
          match isEnsure, arguments with
          | true, predicate :: _ ->
            let found, errors = predicateEvidence env [] predicate
            [ if found then
                yield { Type = "Alex published graph boundary"; Message = "Alex must not derive an admission predicate from a nominal declaration name."; Code = "AXA002"; Severity = Severity.Error; Range = range; Fixes = [] }
              for error in errors |> List.distinct do
                yield { Type = "Alex analysis incomplete"; Message = error; Code = "AXA000"; Severity = Severity.Error; Range = range; Fixes = [] } ]
          | _ -> []

        let axa003 =
          if not isZipperSubstrate && isRevisionTryNodeValue called then
            [ { Target = enclosingFunc; Range = range } ]
          else []

        let refDiag =
          if inImmutableLayer && called.CompiledName = "Ref" &&
             (called.DeclaringEntity |> Option.exists (fun e -> e.Assembly.SimpleName = "FSharp.Core" && e.TryFullName = Some "Microsoft.FSharp.Core.Operators")) then
            [ { Type = "Alex layer purity"
                Message = "Mutable ref cells (ref) are forbidden in non-traversal Alex layers."
                Code = "AXA005"
                Severity = Severity.Error
                Range = range
                Fixes = [] } ]
          else []

        let axa006Diags =
          let exprs = (Option.toList receiverOpt) @ arguments
          let found, errs =
            exprs
            |> List.fold (fun (fAcc, eAcc) expr ->
              let f, e = hasDeclarationFactsProvenance env [] expr
              fAcc || f, eAcc @ e) (false, [])
          let isPipeToContainsKey =
            called.CompiledName = "op_PipeRight" &&
            (called.DeclaringEntity |> Option.exists (fun e -> e.TryFullName = Some "Microsoft.FSharp.Core.Operators")) &&
            match arguments with
            | [ _; target ] -> targetIsContainsKey target
            | _ -> false
          [ if found && not (isAllowedContainsKeyCall called) && not isPipeToContainsKey then
              yield {
                Type = "Alex published graph boundary"
                Message = "Alex must not extract payloads from BoundaryImport.DeclarationFacts; only key-presence checks (ContainsKey / Map.containsKey) are permitted."
                Code = "AXA006"
                Severity = Severity.Error
                Range = range
                Fixes = []
              }
            for err in errs |> List.distinct do
              yield { Type = "Alex analysis incomplete"; Message = err; Code = "AXA000"; Severity = Severity.Error; Range = range; Fixes = [] } ]

        let axa007SitesFromComb, axa007Errs =
          match fallbackArgForCall env [] false called arguments with
          | Some optArg ->
            let found, errors = publishedFactOptionProvenance env [] [] false optArg
            let sites = if found then [ { Target = enclosingFunc; Range = range } ] else []
            sites, errors
          | None -> [], []

        let isPipeRight =
          called.CompiledName = "op_PipeRight" &&
          (called.DeclaringEntity |> Option.exists (fun e -> e.TryFullName = Some "Microsoft.FSharp.Core.Operators"))

        let helperFallbackSites =
          match isPipeRight, arguments with
          | true, [arg; target] ->
            let head, prefixArgs = unwrapApplications target
            match head with
            | Value fn ->
              if checkHelperArgs env [] [] fn (prefixArgs @ [arg]) then [ { Target = enclosingFunc; Range = range } ]
              else []
            | _ -> []
          | _ ->
            if checkHelperArgs env [] [] called arguments then [ { Target = enclosingFunc; Range = range } ]
            else []

        let axa007ErrDiags =
          axa007Errs
          |> List.distinct
          |> List.map (fun error -> { Type = "Alex analysis incomplete"; Message = error; Code = "AXA000"; Severity = Severity.Error; Range = range; Fixes = [] })

        let recvHits =
          receiverOpt
          |> Option.map (walkExpr env enclosingFunc syntheticRevisionRanges)
          |> Option.defaultValue emptyHits
        let argHits =
          match isPipeRight, arguments with
          | true, [arg; target] ->
            let argHit = walkExpr env enclosingFunc syntheticRevisionRanges arg
            let rec walkPipeTarget targetEnv targetExpr =
              match targetExpr with
              | Lambda(paramVal, inner) ->
                walkExpr (addBinding paramVal (bindingOfExpr arg) targetEnv) enclosingFunc syntheticRevisionRanges inner
              | Let((v, b, _), inner) ->
                let bHit = walkExpr targetEnv enclosingFunc syntheticRevisionRanges b
                let innerHit = walkPipeTarget (addBinding v (bindingOfExpr b) targetEnv) inner
                mergeHits bHit innerHit
              | Sequential(first, second) ->
                mergeHits (walkExpr targetEnv enclosingFunc syntheticRevisionRanges first) (walkPipeTarget targetEnv second)
              | _ -> walkExpr targetEnv enclosingFunc syntheticRevisionRanges targetExpr
            mergeHits argHit (walkPipeTarget env target)
          | _ ->
            collectHits arguments (walkExpr env enclosingFunc syntheticRevisionRanges)
        mergeHits
          { Diagnostics = axa002Diags @ refDiag @ axa006Diags @ axa007ErrDiags
            Axa003 = axa003
            Axa004 = []
            Axa007 = axa007SitesFromComb @ helperFallbackSites }
          (mergeHits recvHits argHits)
      | Application _ ->
        let head, allArgs = unwrapApplications expression
        let helperFallbackSites =
          match head with
          | Value fn ->
            if checkHelperArgs env [] [] fn allArgs then [ { Target = enclosingFunc; Range = expression.Range } ]
            else []
          | _ -> []
        let childHits =
          expression.ImmediateSubExpressions
          |> Seq.toList
          |> fun children -> collectHits children (walkExpr env enclosingFunc syntheticRevisionRanges)
        mergeHits { emptyHits with Axa007 = helperFallbackSites } childHits
      | DecisionTree(decisionExpr, targets) ->
        let (noneIndices, skipDomain), errs = collectNoneReachedTargets env [] false decisionExpr
        let errDiags =
          errs
          |> List.distinct
          |> List.map (fun error -> { Type = "Alex analysis incomplete"; Message = error; Code = "AXA000"; Severity = Severity.Error; Range = decisionExpr.Range; Fixes = [] })
        let axa007 =
          noneIndices
          |> Seq.toList
          |> List.choose (fun idx ->
            if idx >= 0 && idx < targets.Length then
              let _, targetBody = targets[idx]
              if not (isAllowedNoneBranch env [] [] false true skipDomain targetBody) then
                Some { Target = enclosingFunc; Range = targetBody.Range }
              else None
            else None)
        let rec walkDecisionSpine spineEnv expr =
          match expr with
          | IfThenElse(guard, thenExpr, elseExpr) ->
            let gHits = walkExpr spineEnv enclosingFunc syntheticRevisionRanges guard
            let tHits = walkDecisionSpine spineEnv thenExpr
            let eHits = walkDecisionSpine spineEnv elseExpr
            mergeHits gHits (mergeHits tHits eHits)
          | DecisionTreeSuccess _ -> emptyHits
          | Let((v, b, _), body) ->
            let bHits = walkExpr spineEnv enclosingFunc syntheticRevisionRanges b
            let bodyHits = walkDecisionSpine (addBinding v (bindingOfExpr b) spineEnv) body
            mergeHits bHits bodyHits
          | Sequential(first, second) ->
            mergeHits (walkExpr spineEnv enclosingFunc syntheticRevisionRanges first) (walkDecisionSpine spineEnv second)
          | other -> walkExpr spineEnv enclosingFunc syntheticRevisionRanges other
        let spineHits = walkDecisionSpine env decisionExpr
        let targetHits = collectHits targets (fun (_, targetBody) -> walkExpr env enclosingFunc syntheticRevisionRanges targetBody)
        mergeHits { emptyHits with Diagnostics = errDiags; Axa007 = axa007 } (mergeHits spineHits targetHits)
      | IfThenElse(guard, thenExpr, elseExpr) ->
        let checkGuard =
          match unwrapUnitApplication guard with
          | UnionCaseTest(scrutinee, unionType, unionCase)
              when unionType.HasTypeDefinition && isOptionEntity unionType.TypeDefinition ->
            let found, errs = publishedFactOptionProvenance env [] [] false scrutinee
            let noneExpr = if unionCase.Name = "None" then thenExpr else elseExpr
            let skipDomain = isWitnessDomainDispatchLookup env scrutinee
            if found && not (isAllowedNoneBranch env [] [] false true skipDomain noneExpr) then Some (noneExpr.Range, errs) else None
          | Call(Some scrutinee, called, _, _, [])
          | Call(None, called, _, _, [scrutinee])
              when called.CompiledName = "get_IsSome" && (called.DeclaringEntity |> Option.exists isOptionEntity) ->
            let found, errs = publishedFactOptionProvenance env [] [] false scrutinee
            let skipDomain = isWitnessDomainDispatchLookup env scrutinee
            if found && not (isAllowedNoneBranch env [] [] false true skipDomain elseExpr) then Some (elseExpr.Range, errs) else None
          | Call(Some scrutinee, called, _, _, [])
          | Call(None, called, _, _, [scrutinee])
              when called.CompiledName = "get_IsNone" && (called.DeclaringEntity |> Option.exists isOptionEntity) ->
            let found, errs = publishedFactOptionProvenance env [] [] false scrutinee
            let skipDomain = isWitnessDomainDispatchLookup env scrutinee
            if found && not (isAllowedNoneBranch env [] [] false true skipDomain thenExpr) then Some (thenExpr.Range, errs) else None
          | Call(_, called, _, _, [scrutinee])
              when (called.DeclaringEntity |> Option.exists isOptionModule) &&
                   (called.CompiledName = "IsSome" || called.CompiledName = "IsNone") ->
            let found, errs = publishedFactOptionProvenance env [] [] false scrutinee
            let noneExpr = if called.CompiledName = "IsNone" then thenExpr else elseExpr
            let skipDomain = isWitnessDomainDispatchLookup env scrutinee
            if found && not (isAllowedNoneBranch env [] [] false true skipDomain noneExpr) then Some (noneExpr.Range, errs) else None
          | _ -> None
        let hereHits =
          match checkGuard with
          | Some (r, errs) ->
            let errDiags =
              errs
              |> List.distinct
              |> List.map (fun error -> { Type = "Alex analysis incomplete"; Message = error; Code = "AXA000"; Severity = Severity.Error; Range = guard.Range; Fixes = [] })
            { emptyHits with Diagnostics = errDiags; Axa007 = [ { Target = enclosingFunc; Range = r } ] }
          | None -> emptyHits
        let childHits =
          mergeHits (walkExpr env enclosingFunc syntheticRevisionRanges guard)
            (mergeHits (walkExpr env enclosingFunc syntheticRevisionRanges thenExpr)
              (walkExpr env enclosingFunc syntheticRevisionRanges elseExpr))
        mergeHits hereHits childHits
      | _ ->
        expression.ImmediateSubExpressions
        |> Seq.toList
        |> fun children -> collectHits children (walkExpr env enclosingFunc syntheticRevisionRanges)

    let rec walkDeclaration (moduleEnv: BindingEnv) (decl: FSharpImplementationFileDeclaration) : BoundaryHits =
      match decl with
      | FSharpImplementationFileDeclaration.Entity(_, subDecls) ->
        collectHits subDecls (walkDeclaration moduleEnv)
      | FSharpImplementationFileDeclaration.MemberOrFunctionOrValue(value, paramGroups, body) ->
        if not value.IsCompilerGenerated then
          let mutDiag =
            if inImmutableLayer && value.IsMutable then
              [ { Type = "Alex layer purity"
                  Message = sprintf "Mutable binding '%s' is forbidden in non-traversal Alex layers." value.DisplayName
                  Code = "AXA005"
                  Severity = Severity.Error
                  Range = value.DeclarationLocation
                  Fixes = [] } ]
            else []
          let axa004 =
            if isRecursiveBinding value body && containsSemanticKindOrRevisionNodes body then
              [ { Target = value.DisplayName; Range = value.DeclarationLocation } ]
            else []
          let declEnv =
            let flatParams = List.concat paramGroups
            let ps, inner = peelLambdas body
            if List.isEmpty flatParams && List.isEmpty ps then moduleEnv
            else addBinding value { Params = flatParams @ ps; Body = inner } moduleEnv
          let bodyHits = walkExpr declEnv value.DisplayName [] body
          mergeHits { emptyHits with Diagnostics = mutDiag; Axa004 = axa004 } bodyHits
        else emptyHits
      | FSharpImplementationFileDeclaration.InitAction(action) ->
        walkExpr moduleEnv "<init>" [] action

    let rec collectModuleBindings (env: BindingEnv) (decl: FSharpImplementationFileDeclaration) : BindingEnv =
      match decl with
      | FSharpImplementationFileDeclaration.Entity(_, subDecls) ->
        subDecls |> List.fold collectModuleBindings env
      | FSharpImplementationFileDeclaration.MemberOrFunctionOrValue(value, paramGroups, body) ->
        if not value.IsCompilerGenerated && not value.IsMutable && not value.IsMember then
          let flatParams = List.concat paramGroups
          let ps, inner = peelLambdas body
          addBinding value { Params = flatParams @ ps; Body = inner } env
        else env
      | FSharpImplementationFileDeclaration.InitAction _ -> env

    let moduleEnv = tree.Declarations |> List.fold collectModuleBindings Map.empty
    let walkedHits = collectHits tree.Declarations (walkDeclaration moduleEnv)
    for d in walkedHits.Diagnostics do diagnostics.Add d

    let sourceRelList =
      context.ProjectOptions.SourceFiles
      |> Seq.toList
      |> List.choose (fun file ->
        let nf = file.Replace('\\', '/')
        let idx = nf.IndexOf(alexSrcMarker, System.StringComparison.Ordinal)
        if idx >= 0 then Some (nf.Substring(idx + alexSrcMarker.Length)) else None)
    let sourceRelSet = Set.ofList sourceRelList

    let enforceRatchet (code: string) (diagType: string) (ruleDesc: string) (exemptPredicate: ObservedSite -> bool) (pins: DebtPin list) (observed: ObservedSite list) =
      let remaining = observed |> List.filter (exemptPredicate >> not)
      if not isProductionAlex then
        for site in remaining do
          diagnostics.Add {
            Type = diagType
            Message = sprintf "%s (in '%s')." ruleDesc site.Target
            Code = code
            Severity = Severity.Error
            Range = site.Range
            Fixes = []
          }
      else
        let rel = alexRelativeFile.Value
        let isPrimaryProdFile = List.tryHead sourceRelList = Some rel
        if isPrimaryProdFile then
          for pin in pins do
            if not (sourceRelSet.Contains pin.File) then
              let position = Position.mkPos 1 0
              diagnostics.Add {
                Type = diagType
                Message = sprintf "%s stale ratchet pin: '%s' in '%s' is not present in Alex.fsproj; remove pin." code pin.Target pin.File
                Code = code
                Severity = Severity.Error
                Range = Range.mkRange context.FileName position position
                Fixes = []
              }
        let filePins = pins |> List.filter (fun pin -> pin.File = rel)
        let pinMap =
          filePins
          |> List.map (fun pin -> pin.Target, pin.MaxCount)
          |> Map.ofList
        let grouped =
          remaining
          |> List.groupBy (fun site -> site.Target)
          |> Map.ofList
        for KeyValue(funcName, siteList) in grouped do
          match pinMap.TryFind funcName with
          | None ->
            for site in siteList do
              diagnostics.Add {
                Type = diagType
                Message = sprintf "%s (unpinned '%s' in '%s')." ruleDesc funcName rel
                Code = code
                Severity = Severity.Error
                Range = site.Range
                Fixes = []
              }
          | Some maxCount ->
            if siteList.Length > maxCount then
              for site in siteList |> List.skip maxCount do
                diagnostics.Add {
                  Type = diagType
                  Message = sprintf "%s ('%s' in '%s' has %d sites, exceeding downward ratchet cap %d)." ruleDesc funcName rel siteList.Length maxCount
                  Code = code
                  Severity = Severity.Error
                  Range = site.Range
                  Fixes = []
                }
        for pin in filePins do
          let actualCount =
            match grouped.TryFind pin.Target with
            | Some sites -> List.length sites
            | None -> 0
          if pin.MaxCount > actualCount then
            let position = Position.mkPos 1 0
            diagnostics.Add {
              Type = diagType
              Message = sprintf "%s ratchet mismatch: '%s' in '%s' pins %d site(s) but actual count is %d; tighten downward." code pin.Target rel pin.MaxCount actualCount
              Code = code
              Severity = Severity.Error
              Range = Range.mkRange context.FileName position position
              Fixes = []
            }

    let axa003Pins : DebtPin list = [
      { File = "Dialects/Core/Types.fs"; Target = "conditionalTagSelectionAt"; MaxCount = 3 }
      { File = "Correspondence.fs"; Target = "validateOccurrence"; MaxCount = 1 }
      { File = "CodeGeneration/TypeMapping.fs"; Target = "tryNativeSlotValueType"; MaxCount = 1 }
      { File = "Patterns/MemoryPatterns.fs"; Target = "pArenaCreateIntrinsic"; MaxCount = 1 }
      { File = "Patterns/CallableAggregatePatterns.fs"; Target = "nativeAlternative"; MaxCount = 1 }
      { File = "Patterns/CallableAggregatePatterns.fs"; Target = "operationErrors"; MaxCount = 2 }
      { File = "Patterns/CallableAggregatePatterns.fs"; Target = "pReadOrdinaryComponent"; MaxCount = 1 }
      { File = "Patterns/CallableAggregatePatterns.fs"; Target = "requiresComponents"; MaxCount = 1 }
      { File = "Patterns/CallableAggregatePatterns.fs"; Target = "validateOperation"; MaxCount = 2 }
      { File = "Patterns/DUPatterns.fs"; Target = "pBuildDUInitialize"; MaxCount = 1 }
      { File = "Patterns/ContinuationPatterns.fs"; Target = "pRecallContinuationValue"; MaxCount = 1 }
      { File = "Patterns/CallablePatterns.fs"; Target = "pProgramInstance"; MaxCount = 1 }
      { File = "Patterns/SequencePatterns.fs"; Target = "pProgramInstance"; MaxCount = 1 }
      { File = "Patterns/MutableCallablePatterns.fs"; Target = "pReadMutableCallable"; MaxCount = 1 }
      { File = "Witnesses/LazyWitness.fs"; Target = "witness"; MaxCount = 1 }
      { File = "Witnesses/SeqWitness.fs"; Target = "accessSlot"; MaxCount = 2 }
      { File = "Witnesses/SeqWitness.fs"; Target = "witnessSeq"; MaxCount = 1 }
      { File = "Witnesses/EnvironmentWitness.fs"; Target = "access"; MaxCount = 1 }
      { File = "Witnesses/ControlFlowWitness.fs"; Target = "witnessBranchScope"; MaxCount = 1 }
      { File = "Witnesses/ControlFlowWitness.fs"; Target = "witnessContinuationDispatch"; MaxCount = 1 }
      { File = "Witnesses/ControlFlowWitness.fs"; Target = "witnessControlFlowWith"; MaxCount = 1 }
      { File = "Witnesses/StructuralWitness.fs"; Target = "witnessStructural"; MaxCount = 1 }
      { File = "Witnesses/BindingWitness.fs"; Target = "witnessBinding"; MaxCount = 1 }
      { File = "Witnesses/VarRefWitness.fs"; Target = "witnessVarRef"; MaxCount = 2 }
      { File = "Witnesses/MutableAssignmentWitness.fs"; Target = "witnessMutableAssignment"; MaxCount = 3 }
      { File = "Witnesses/ArithIntrinsicWitness.fs"; Target = "calleeIntrinsic"; MaxCount = 2 }
      { File = "Witnesses/LambdaWitness.fs"; Target = "witnessLambdaWith"; MaxCount = 4 }
    ]
    let axa004Pins : DebtPin list = [
      { File = "XParsec/PSGCombinators.fs"; Target = "lastValueNode"; MaxCount = 1 }
      { File = "XParsec/PSGCombinators.fs"; Target = "findLastValueNode"; MaxCount = 1 }
      { File = "Patterns/CallablePatterns.fs"; Target = "pIntrinsicCalleeAnnotation.callee"; MaxCount = 1 }
      { File = "Witnesses/VarRefWitness.fs"; Target = "witnessVarRef.assignmentTarget"; MaxCount = 1 }
    ]
    let axa007Pins : DebtPin list = [
      { File = "Dialects/Core/Types.fs"; Target = "conditionalTagSelectionAt"; MaxCount = 1 }
      { File = "CodeGeneration/TypeMapping.fs"; Target = "pointerTypeAt"; MaxCount = 1 }
      { File = "Traversal/CoverageValidation.fs"; Target = "validateCoverageWith"; MaxCount = 2 }
      { File = "Traversal/CallableOperands.fs"; Target = "closedNativeDefinition"; MaxCount = 1 }
      { File = "Traversal/CallableOperands.fs"; Target = "parametersAtCall"; MaxCount = 1 }
      { File = "Traversal/CallableOperands.fs"; Target = "projectSeen"; MaxCount = 1 }
      { File = "Patterns/MemoryPatterns.fs"; Target = "pAllocValue"; MaxCount = 1 }
      { File = "Patterns/MemoryPatterns.fs"; Target = "pPublishedMemoryOperation"; MaxCount = 1 }
      { File = "Patterns/MemoryPatterns.fs"; Target = "pRetireResultAt"; MaxCount = 1 }
      { File = "Patterns/CallableAggregatePatterns.fs"; Target = "operationErrors"; MaxCount = 1 }
      { File = "Patterns/CallableAggregatePatterns.fs"; Target = "requiresComponents"; MaxCount = 2 }
      { File = "Patterns/CallableAggregatePatterns.fs"; Target = "validateOperation"; MaxCount = 2 }
      { File = "Patterns/MemRefPatterns.fs"; Target = "pGlobalSlotInit"; MaxCount = 1 }
      { File = "Patterns/MemRefPatterns.fs"; Target = "pGlobalSlotLoad"; MaxCount = 1 }
      { File = "Patterns/MemRefPatterns.fs"; Target = "pGlobalSlotStore"; MaxCount = 1 }
      { File = "Patterns/ContinuationPatterns.fs"; Target = "pAllocateFrame"; MaxCount = 1 }
      { File = "Patterns/ContinuationPatterns.fs"; Target = "pConstructSequence"; MaxCount = 1 }
      { File = "Patterns/ContinuationPatterns.fs"; Target = "pInitializeEnvironmentSlots"; MaxCount = 1 }
      { File = "Patterns/ContinuationPatterns.fs"; Target = "pSlotType"; MaxCount = 1 }
      { File = "Patterns/ContinuationPatterns.fs"; Target = "pWriteContinuationSlot"; MaxCount = 1 }
      { File = "Patterns/EnvironmentPatterns.fs"; Target = "pCreateEnvironment"; MaxCount = 1 }
      { File = "Patterns/EnvironmentPatterns.fs"; Target = "pRecallEnvironment"; MaxCount = 2 }
      { File = "Patterns/LazyPatterns.fs"; Target = "pCreateLazyEnvironment"; MaxCount = 1 }
      { File = "Patterns/LazyPatterns.fs"; Target = "pRecallLazyEnvironment"; MaxCount = 1 }
      { File = "Patterns/EagerPatterns.fs"; Target = "pEagerValue"; MaxCount = 2 }
      { File = "Patterns/MutableCallablePatterns.fs"; Target = "pCreateMutableCallable"; MaxCount = 1 }
      { File = "Patterns/PlatformPatterns.fs"; Target = "boundaryImportsAt"; MaxCount = 1 }
      { File = "Patterns/PlatformPatterns.fs"; Target = "pBoundaryCall"; MaxCount = 1 }
      { File = "Traversal/NanopassArchitecture.fs"; Target = "combineWitnesses"; MaxCount = 1 }
      { File = "Traversal/NanopassArchitecture.fs"; Target = "runAllNanopasses"; MaxCount = 1 }
      { File = "Witnesses/TypeAnnotationWitness.fs"; Target = "witnessTypeAnnotation"; MaxCount = 1 }
      { File = "Witnesses/FunctionPointerWitness.fs"; Target = "witness"; MaxCount = 1 }
      { File = "Witnesses/SeqWitness.fs"; Target = "frameAt"; MaxCount = 1 }
      { File = "Witnesses/StructuralWitness.fs"; Target = "witnessStructural"; MaxCount = 1 }
      { File = "Witnesses/BindingWitness.fs"; Target = "witnessBinding"; MaxCount = 4 }
      { File = "Witnesses/VarRefWitness.fs"; Target = "witnessVarRef"; MaxCount = 3 }
      { File = "Witnesses/ApplicationWitness.fs"; Target = "direct"; MaxCount = 1 }
      { File = "Witnesses/ApplicationWitness.fs"; Target = "invoke"; MaxCount = 1 }
      { File = "Witnesses/ApplicationWitness.fs"; Target = "witnessApplication"; MaxCount = 3 }
      { File = "Witnesses/LambdaWitness.fs"; Target = "ordinaryParameterComponents"; MaxCount = 1 }
      { File = "Witnesses/LambdaWitness.fs"; Target = "witnessLambdaWith"; MaxCount = 2 }
    ]

    enforceRatchet "AXA003" "Alex published graph boundary" "Alex must confine Revision.Nodes and Revision.tryNode to Traversal/, XParsec/, or Generation.fs" (fun _ -> false) axa003Pins walkedHits.Axa003
    enforceRatchet "AXA004" "Alex published graph boundary" "Alex must not write recursive SemanticKind or Revision.Nodes catamorphisms outside Traversal/NanopassArchitecture.fs (tryWitnesses)" (fun site -> isNanopassArchitecture && (site.Target = "tryWitnesses" || site.Target = "combineWitnesses.tryWitnesses")) axa004Pins walkedHits.Axa004
    enforceRatchet "AXA007" "Alex published graph boundary" "Alex must not collapse None from a published-fact or symbol lookup into a fallback value" (fun _ -> false) axa007Pins walkedHits.Axa007

  return diagnostics |> Seq.distinctBy (fun diagnostic -> diagnostic.Code, diagnostic.Range.StartLine, diagnostic.Range.StartColumn, diagnostic.Message) |> List.ofSeq
}

[<CliAnalyzer("Alex dependency context")>]
let dependencyContext : Analyzer<CliContext> = fun context -> async {
  let options = context.ProjectOptions
  let assemblies =
    context.CheckFileResults.ProjectContext.GetReferencedAssemblies()
    |> Seq.map (fun assembly ->
      {| simpleName = assembly.SimpleName
         qualifiedName = assembly.QualifiedName
         file = assembly.FileName |> Option.toObj |})
    |> Seq.toArray
  let record =
    {| project = options.ProjectFileName
       sourceFiles = options.SourceFiles
       referencedProjects = options.ReferencedProjectsPath
       options = options.OtherOptions
       assemblies = assemblies |}
  let serialize value = System.Text.Json.JsonSerializer.Serialize(value)
  let paths =
    seq {
      for option in options.OtherOptions do
        if option.StartsWith("-r:", System.StringComparison.Ordinal) then yield option.Substring(3)
      for assembly in assemblies do
        if not (System.String.IsNullOrWhiteSpace assembly.file) then yield assembly.file
      yield! options.SourceFiles
    } |> Seq.distinct
  let hashes =
    paths
    |> Seq.map (fun path ->
      if System.IO.File.Exists path then
        use stream = System.IO.File.OpenRead path
        path, System.Security.Cryptography.SHA256.HashData(stream) |> System.Convert.ToHexString
      else
        path, "MISSING")
    |> readOnlyDict
  let payload = {| context = record; hashedBy = context.FileName; hashes = hashes |} |> serialize
  let position = Position.mkPos 1 0
  return [{ Type = "Alex dependency context"; Message = payload; Code = "AXD000"; Severity = Severity.Info; Range = Range.mkRange context.FileName position position; Fixes = [] }]
}
