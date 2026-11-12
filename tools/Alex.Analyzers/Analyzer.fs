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
    let bindings = System.Collections.Generic.Dictionary<FSharpMemberOrFunctionOrValue, FSharpExpr>()
    let rec predicateEvidence visited (expression: FSharpExpr) =
      try
        match expression with
        | FSharpFieldGet(_, _, field) when field.Name = "Name" &&
            (field.DeclaringEntity |> Option.exists (fun entity -> entity.TryFullName = Some "Fidelity.PSG.NominalTypeIdentity" && entity.Assembly.SimpleName = "Fidelity.PSG")) -> true, []
        | Call(_, called, _, _, [argument]) when called.CompiledName = "Not" &&
            (called.DeclaringEntity |> Option.exists (fun entity -> entity.TryFullName = Some "Microsoft.FSharp.Core.Operators" && entity.Assembly.SimpleName = "FSharp.Core")) ->
          predicateEvidence visited argument
        | Call(receiver, called, _, _, arguments) when called.CompiledName = "StartsWith" &&
            (called.DeclaringEntity |> Option.exists (fun entity ->
              let assembly = entity.Assembly.SimpleName
              entity.TryFullName = Some "System.String" &&
              (assembly = "mscorlib" || assembly = "netstandard" || assembly.StartsWith("System.")))) ->
          let resultType = called.ReturnParameter.Type
          let isBoolean =
            if not resultType.HasTypeDefinition then false
            else
              let definition = resultType.TypeDefinition
              if definition.TryFullName = Some "System.Boolean" then true
              elif resultType.IsAbbreviation && definition.Assembly.SimpleName = "FSharp.Core" && definition.DisplayName = "bool" then
                let target = definition.AbbreviatedType
                target.HasTypeDefinition && target.TypeDefinition.TryFullName = Some "System.Boolean"
              else false
          match receiver with
          | Some value when isBoolean ->
            (value :: arguments)
            |> List.fold (fun (found, errors) child ->
              let nextFound, nextErrors = predicateEvidence visited child
              found || nextFound, errors @ nextErrors) (false, [])
          | _ -> false, [ "Cannot establish the shape of the System.String.StartsWith predicate." ]
        | Call(_, called, _, _, _) when not (called.CompiledName.StartsWith("op_")) -> false, []
        | Application _ | Lambda _ -> false, []
        | Sequential(_, second) -> predicateEvidence visited second
        | Let((value, binding, _), body) ->
          bindings[value] <- binding
          predicateEvidence visited body
        | TupleGet(_, _, Value _) | FSharpFieldGet(Some (Value _), _, _) | UnionCaseGet(Value _, _, _, _) -> false, []
        | Value value ->
          match bindings.TryGetValue value with
          | true, _ when value.IsMember -> false, []
          | true, _ when value.IsMutable -> false, [ sprintf "Cannot establish nominal predicate provenance through mutable local '%s'." value.DisplayName ]
          | true, _ when visited |> List.exists ((=) value) -> false, [ sprintf "Cyclic nominal predicate provenance at local '%s'." value.DisplayName ]
          | true, binding -> predicateEvidence (value :: visited) binding
          | _ -> false, []
        | _ ->
          expression.ImmediateSubExpressions
          |> Seq.fold (fun (found, errors) child ->
            let nextFound, nextErrors = predicateEvidence visited child
            found || nextFound, errors @ nextErrors) (false, [])
      with error -> false, [ sprintf "Cannot inspect nominal predicate provenance: %s" error.Message ]
    let walker =
      { new TypedTreeCollectorBase() with
          override _.WalkLet value binding _ = bindings[value] <- binding
          override _.WalkCall _ called _ _ arguments range =
            let isEnsure =
              called.DisplayName = "ensure" &&
              (called.DeclaringEntity |> Option.exists (fun entity -> entity.TryFullName = Some "Alex.XParsec.PSGCombinators" && entity.Assembly.SimpleName = "Alex"))
            match isEnsure, arguments with
            | true, predicate :: _ ->
              let found, errors = predicateEvidence [] predicate
              if found then diagnostics.Add { Type = "Alex published graph boundary"; Message = "Alex must not derive an admission predicate from a nominal declaration name."; Code = "AXA002"; Severity = Severity.Error; Range = range; Fixes = [] }
              for error in errors |> List.distinct do
                diagnostics.Add { Type = "Alex analysis incomplete"; Message = error; Code = "AXA000"; Severity = Severity.Error; Range = range; Fixes = [] }
            | _ -> ()
          override _.WalkNewRecord recordType _ range =
            if recordType.HasTypeDefinition &&
               recordType.TypeDefinition.Assembly.SimpleName = "Fidelity.PSG" &&
               (recordType.TypeDefinition.FullName = "Fidelity.PSG.Revision" ||
                recordType.TypeDefinition.FullName = "Fidelity.PSG.SemanticNode") then
              diagnostics.Add {
                Type = "Alex published graph boundary"
                Message = "Alex must not construct or update published PSG records."
                Code = "AXA001"
                Severity = Severity.Error
                Range = range
                Fixes = []
              } }
    walkTast walker tree
  return List.ofSeq diagnostics
}
