/// SMTTransfer: the build-time dispatch -- the graph's obligations as `smt` dialect IR
///
/// Architecturally parallel to XDCTransfer. Both are transfers: pure functions
/// from settled data to text, with no traversal and no decision.
///   - XDCTransfer: the pin-mapping coeffect -> XDC constraints
///   - SMTTransfer: the graph's obligation nodes -> an `smt` verification module
///
/// Obligations are graph citizens: minted into the PSG by the Baker obligation
/// recipes at saturation (CCS Pass 5), each a node in V with a hyperedge in F
/// whose source set is the structure it constrains (C-01 14.5;
/// Obligation_Residency 3). This module reads those records from the graph and
/// transcribes them. Every fact in an ObligationBody was fixed at saturation;
/// nothing here computes.
///
/// One birth, two dispatches. The anchor name is the identity that travels:
/// CCS renders the same records to SMT-LIB at design time (06b); this module
/// renders them to `smt` dialect at build time (09), and mlir-translate
/// --export-smtlib carries the `smt.declare_fun` names through verbatim, so the
/// two dispatches pair one for one (HelloProof proof-trace 03).
///
/// Output: a standalone verification module beside the program, with one
/// smt.solver scope per solver-ready obligation. Pending retains its ledger
/// citizen and has no solver operation or discharge.
module Alex.Traversal.SMTTransfer

open Alex.Dialects.Core.Types
open Alex.Dialects.Core.Serialize
open Fidelity.PSG

type private SharedTerm =
    | STVar of string
    | STConst of int64
    | STAdd of SharedTerm * SharedTerm
    | STMul of SharedTerm * SharedTerm
    | STMod of SharedTerm * SharedTerm

type private SharedPred =
    | SPEq of SharedTerm * SharedTerm
    | SPCmp of SMTCmpPred * SharedTerm * SharedTerm
    | SPAnd of SharedPred list
    | SPOr of SharedPred list
    | SPNot of SharedPred

/// Transcribe one obligation into an isolated smt.solver scope.
/// SSA numbering is fresh per scope (solver regions are isolated).
let private scope (ob: ObligationInfo) : Result<MLIROp list, string> =
    let mutable n = -1
    let v () = n <- n + 1; Alex.Traversal.Values.solverValue n   // fresh per isolated solver scope: the SMT module, not the program graph
    let smt op = MLIROp.SMTOp op

    // Anchor discipline: %ob names the obligation; assert (ob = definition)
    // and (not ob). The declare_fun name is the identity that travels.
    let anchor (defSSA: SSA) (body: MLIROp list) : MLIROp list =
        let ob' = v ()
        let bind = v ()
        let neg = v ()
        body
        @ [ smt (SMTDeclareFun (ob', ob.Id, SMTBool))
            smt (SMTEq (bind, ob', defSSA, SMTBool))
            smt (SMTAssert bind)
            smt (SMTNot (neg, ob'))
            smt (SMTAssert neg) ]

    // The current SMT dialect has no Real sort. For these ground rational
    // facts, a/b <= c/d is exactly a*d <= c*b when b,d > 0. Transcribe the
    // products of integer constants rather than evaluating the comparison;
    // this preserves the source QF_LRA claim in a QF_LIA solver scope.
    let rationalComparisons (pairs: (ExactRational * ExactRational) list) : Result<MLIROp list, string> =
        if pairs |> List.exists (fun (left, right) -> left.Denominator <= 0I || right.Denominator <= 0I) then
            Error (sprintf "Obligation '%s' requires positive rational denominators." ob.Id)
        else
            let mutable statements: MLIROp list = []
            let constant value =
                let ssa = v ()
                statements <- (smt (SMTBigIntConstant(ssa, value))) :: statements
                ssa
            let product numerator denominator =
                let a, b, output = constant numerator, constant denominator, v ()
                statements <- (smt (SMTIntMul(output, a, b))) :: statements
                output
            let clauses = pairs |> List.map (fun (left, right) ->
                let l = product left.Numerator right.Denominator
                let r = product right.Numerator left.Denominator
                let clause = v ()
                statements <- (smt (SMTIntCmp(clause, SmtLe, l, r))) :: statements
                clause)
            let conjunction = v ()
            statements <- (smt (SMTAnd(conjunction, clauses))) :: statements
            Ok (anchor conjunction (List.rev statements))

    let integerComparisons (pairs: (bigint * bigint) list) : MLIROp list =
        let mutable statements: MLIROp list = []
        let clauses = pairs |> List.map (fun (left, right) ->
            let l, r, comparison = v (), v (), v ()
            statements <- (smt (SMTBigIntConstant(l, left))) :: statements
            statements <- (smt (SMTBigIntConstant(r, right))) :: statements
            statements <- (smt (SMTIntCmp(comparison, SmtLe, l, r))) :: statements
            comparison)
        let conjunction = v ()
        statements <- (smt (SMTAnd(conjunction, clauses))) :: statements
        anchor conjunction (List.rev statements)

    // A finite postorder fold formats the canonical logical expression. It
    // never traverses the program graph or re-enters an elaboration pass.
    let resource (projection: Result<ResourceProof.Projection, string>) : Result<MLIROp list, string> =
        match projection with
        | Error reason -> Error (sprintf "Obligation '%s': %s" ob.Id reason)
        | Ok projection ->
            let sort = function ResourceProof.Sort.Boolean -> SMTBool | ResourceProof.Sort.Integer -> SMTInt
            let variables = projection.Declarations |> List.map (fun (name, ty) -> name, (v (), sort ty)) |> Map.ofList
            let declarations = variables |> Map.toList |> List.map (fun (name, (value, ty)) -> smt (SMTDeclareFun(value, name, ty)))
            let children = function
                | ResourceProof.Expr.Boolean _ | ResourceProof.Expr.Integer _ | ResourceProof.Expr.Variable _ -> []
                | ResourceProof.Expr.Not value -> [value]
                | ResourceProof.Expr.And values | ResourceProof.Expr.Or values | ResourceProof.Expr.Add values -> values
                | ResourceProof.Expr.Implies(left, right) | ResourceProof.Expr.Equal(left, right)
                | ResourceProof.Expr.LessThan(left, right) | ResourceProof.Expr.LessOrEqual(left, right)
                | ResourceProof.Expr.Multiply(left, right) | ResourceProof.Expr.Modulo(left, right) -> [left; right]
                | ResourceProof.Expr.IfThenElse(condition, left, right) -> [condition; left; right]
            let ordered =
                [projection.Premises, false; projection.Conclusion, false]
                |> List.unfold (function
                    | [] -> None
                    | (expression, true) :: rest -> Some(Some expression, rest)
                    | (expression, false) :: rest ->
                        Some(None, (children expression |> List.map (fun child -> child, false)) @ ((expression, true) :: rest)))
                |> List.choose id
            let folded =
                ordered
                |> List.fold (fun stateResult expression ->
                    match stateResult with
                    | Error _ as err -> err
                    | Ok (values, bodies) ->
                        if Map.containsKey expression values then Ok (values, bodies)
                        else
                            let child expression = Map.find expression values
                            let output = v ()
                            let boolean value =
                                let zero, equal = v (), if value then output else v ()
                                [smt (SMTBigIntConstant(zero, 0I)); smt (SMTEq(equal, zero, zero, SMTInt))]
                                @ (if value then [] else [smt (SMTNot(output, equal))])
                            let inferred expression =
                                ResourceProof.sortOf projection.Declarations expression
                                |> Result.map sort
                            let stepResult =
                                match expression with
                                | ResourceProof.Expr.Variable name -> Ok (fst variables[name], [])
                                | ResourceProof.Expr.Integer value -> Ok (output, [smt (SMTBigIntConstant(output, value))])
                                | ResourceProof.Expr.Boolean value -> Ok (output, boolean value)
                                | ResourceProof.Expr.Not value -> Ok (output, [smt (SMTNot(output, child value))])
                                | ResourceProof.Expr.And [] -> Ok (output, boolean true)
                                | ResourceProof.Expr.Or [] -> Ok (output, boolean false)
                                | ResourceProof.Expr.And [value] | ResourceProof.Expr.Or [value] -> Ok (child value, [])
                                | ResourceProof.Expr.And operands -> Ok (output, [smt (SMTAnd(output, List.map child operands))])
                                | ResourceProof.Expr.Or operands -> Ok (output, [smt (SMTOr(output, List.map child operands))])
                                | ResourceProof.Expr.Implies(left, right) ->
                                    let negated = v ()
                                    Ok (output, [smt (SMTNot(negated, child left)); smt (SMTOr(output, [negated; child right]))])
                                | ResourceProof.Expr.Equal(left, right) ->
                                    inferred left |> Result.map (fun ty -> output, [smt (SMTEq(output, child left, child right, ty))])
                                | ResourceProof.Expr.LessThan(left, right) -> Ok (output, [smt (SMTIntCmp(output, SmtLt, child left, child right))])
                                | ResourceProof.Expr.LessOrEqual(left, right) -> Ok (output, [smt (SMTIntCmp(output, SmtLe, child left, child right))])
                                | ResourceProof.Expr.Multiply(left, right) -> Ok (output, [smt (SMTIntMul(output, child left, child right))])
                                | ResourceProof.Expr.Modulo(left, right) -> Ok (output, [smt (SMTIntMod(output, child left, child right))])
                                | ResourceProof.Expr.Add [] -> Ok (output, [smt (SMTBigIntConstant(output, 0I))])
                                | ResourceProof.Expr.Add (first :: remaining) ->
                                    Ok (
                                        remaining |> List.fold (fun (left, body) right ->
                                            let sum = v ()
                                            sum, body @ [smt (SMTIntAdd(sum, left, child right))]) (child first, []))
                                | ResourceProof.Expr.IfThenElse(condition, left, right) ->
                                    inferred expression |> Result.map (fun ty -> output, [smt (SMTIte(output, child condition, child left, child right, ty))])
                            match stepResult with
                            | Ok (value, body) -> Ok (Map.add expression value values, body :: bodies)
                            | Error reason -> Error reason) (Ok (Map.empty, []))
            match folded with
            | Error reason -> Error reason
            | Ok (values, bodies) ->
                Ok (
                    anchor values[projection.Conclusion]
                        (declarations @ (bodies |> List.rev |> List.concat) @ [smt (SMTAssert values[projection.Premises])]))

    let boolConst (value: bool) : SSA * MLIROp list =
        let zero, eqOut = v (), v ()
        if value then
            eqOut, [ smt (SMTBigIntConstant(zero, 0I)); smt (SMTEq(eqOut, zero, zero, SMTInt)) ]
        else
            let negated = v ()
            negated, [ smt (SMTBigIntConstant(zero, 0I)); smt (SMTEq(eqOut, zero, zero, SMTInt)); smt (SMTNot(negated, eqOut)) ]

    let intConst (value: bigint) : SSA * MLIROp list =
        let ssa = v ()
        ssa, [ smt (SMTBigIntConstant(ssa, value)) ]

    let int64Const (value: int) : SSA * MLIROp list =
        let ssa = v ()
        ssa, [ smt (SMTIntConstant(ssa, int64 value)) ]

    let cmpVal (pred: SMTCmpPred) (left: bigint) (right: bigint) : SSA * MLIROp list =
        let l, lOps = intConst left
        let r, rOps = intConst right
        let out = v ()
        out, lOps @ rOps @ [ smt (SMTIntCmp(out, pred, l, r)) ]

    let cmpInt (pred: SMTCmpPred) (left: int) (right: int) : SSA * MLIROp list =
        let l, lOps = int64Const left
        let r, rOps = int64Const right
        let out = v ()
        out, lOps @ rOps @ [ smt (SMTIntCmp(out, pred, l, r)) ]

    let eqInt32 (left: int) (right: int) : SSA * MLIROp list =
        let l, lOps = int64Const left
        let r, rOps = int64Const right
        let out = v ()
        out, lOps @ rOps @ [ smt (SMTEq(out, l, r, SMTInt)) ]

    let anchorClauses (clauses: (SSA * MLIROp list) list) : MLIROp list =
        let conjunction = v ()
        let body = (clauses |> List.collect snd) @ [ smt (SMTAnd(conjunction, List.map fst clauses)) ]
        anchor conjunction body

    let sharedBufferObligation (bareOb: BAREWire.Platform.Obligation) : Result<MLIROp list, string> =
        if ob.Id <> bareOb.Id || ob.Kind <> bareOb.Kind || ob.Logic <> bareOb.Logic || Alex.Text.isBlank bareOb.Id then
            Error (sprintf "Obligation '%s' disagrees with its BAREWire obligation metadata." ob.Id)
        else
            let f = bareOb.Form
            let gtVar nm k = SPCmp(SmtGt, STVar nm, STConst k)
            let geVar nm k = SPCmp(SmtGe, STVar nm, STConst k)
            let leVar nm k = SPCmp(SmtLe, STVar nm, STConst k)
            let eqVar nm k = SPEq(STVar nm, STConst k)
            let eqVars lhs rhs = SPEq(STVar lhs, STVar rhs)
            let pow2Constants = [ for k in 0 .. 30 -> 1L <<< k ]
            let elemWidthConstants = [ 1L; 2L; 4L; 8L ]
            let pow2Disjunction (varName: string) : SharedPred =
                SPOr (pow2Constants |> List.map (fun c -> eqVar varName c))
            let dividesBothFrom (constants: int64 list) (dividend1: string) (dividend2: string) (divisor: string) : SharedPred =
                SPOr (
                    constants
                    |> List.map (fun c ->
                        SPAnd
                            [ eqVar divisor c
                              SPEq(STMod(STVar dividend1, STConst c), STConst 0L)
                              SPEq(STMod(STVar dividend2, STConst c), STConst 0L) ]))
            let fieldGeometryFrom (constants: int64 list) (fOff: string) (fCount: string) (fLen: string) (fAlign: string) : SharedPred =
                SPOr (
                    constants
                    |> List.map (fun c ->
                        SPAnd
                            [ eqVar fAlign c
                              SPEq(STMod(STVar fOff, STConst c), STConst 0L)
                              SPEq(STVar fLen, STMul(STVar fCount, STConst c)) ]))
            let transcribeNamedSharedBufferForm (buildPreds: Map<string, SSA> -> Result<SharedPred list, string>) : Result<MLIROp list, string> =
                if Array.length f.Names = 0
                   || Array.length f.Names <> Array.length f.Values
                   || (f.Names |> Array.exists Alex.Text.isBlank)
                   || (Set.ofArray f.Names).Count <> Array.length f.Names then
                    Error (sprintf "Obligation '%s' has invalid or duplicate BAREWire symbol bindings." ob.Id)
                else
                    let pairs = Array.zip f.Names f.Values |> Array.toList
                    let boundVars =
                        pairs
                        |> List.map (fun (nm, value) ->
                            let varSSA = v ()
                            let valSSA = v ()
                            let eqSSA = v ()
                            let ops =
                                [ smt (SMTDeclareFun(varSSA, nm, SMTInt))
                                  smt (SMTIntConstant(valSSA, value))
                                  smt (SMTEq(eqSSA, varSSA, valSSA, SMTInt))
                                  smt (SMTAssert eqSSA) ]
                            (nm, varSSA), ops)
                    let varMap = boundVars |> List.map fst |> Map.ofList
                    let declAndPinOps = boundVars |> List.collect snd
                    let rec evalTerm (term: SharedTerm) : Result<SSA * MLIROp list, string> =
                        match term with
                        | STVar name ->
                            match Map.tryFind name varMap with
                            | Some ssa -> Ok(ssa, [])
                            | None -> Error (sprintf "Obligation '%s' references undeclared BAREWire symbol '%s'." ob.Id name)
                        | STConst k ->
                            let c = v ()
                            Ok(c, [ smt (SMTIntConstant(c, k)) ])
                        | STAdd(lhs, rhs) ->
                            match evalTerm lhs, evalTerm rhs with
                            | Ok(l, lOps), Ok(r, rOps) ->
                                let out = v ()
                                Ok(out, lOps @ rOps @ [ smt (SMTIntAdd(out, l, r)) ])
                            | Error e, _ | _, Error e -> Error e
                        | STMul(lhs, rhs) ->
                            match evalTerm lhs, evalTerm rhs with
                            | Ok(l, lOps), Ok(r, rOps) ->
                                let out = v ()
                                Ok(out, lOps @ rOps @ [ smt (SMTIntMul(out, l, r)) ])
                            | Error e, _ | _, Error e -> Error e
                        | STMod(lhs, rhs) ->
                            match evalTerm lhs, evalTerm rhs with
                            | Ok(l, lOps), Ok(r, rOps) ->
                                let out = v ()
                                Ok(out, lOps @ rOps @ [ smt (SMTIntMod(out, l, r)) ])
                            | Error e, _ | _, Error e -> Error e
                    let rec evalPred (pred: SharedPred) : Result<SSA * MLIROp list, string> =
                        let evalPredList (items: SharedPred list) : Result<SSA list * MLIROp list, string> =
                            let rec loop accSSAs accOps remaining =
                                match remaining with
                                | [] -> Ok(List.rev accSSAs, List.rev accOps |> List.concat)
                                | p :: rest ->
                                    match evalPred p with
                                    | Ok(ssa, ops) -> loop (ssa :: accSSAs) (ops :: accOps) rest
                                    | Error err -> Error err
                            loop [] [] items
                        match pred with
                        | SPEq(lhs, rhs) ->
                            match evalTerm lhs, evalTerm rhs with
                            | Ok(l, lOps), Ok(r, rOps) ->
                                let out = v ()
                                Ok(out, lOps @ rOps @ [ smt (SMTEq(out, l, r, SMTInt)) ])
                            | Error e, _ | _, Error e -> Error e
                        | SPCmp(cmpPred, lhs, rhs) ->
                            match evalTerm lhs, evalTerm rhs with
                            | Ok(l, lOps), Ok(r, rOps) ->
                                let out = v ()
                                Ok(out, lOps @ rOps @ [ smt (SMTIntCmp(out, cmpPred, l, r)) ])
                            | Error e, _ | _, Error e -> Error e
                        | SPAnd [] ->
                            let out, ops = boolConst true
                            Ok(out, ops)
                        | SPAnd [ single ] -> evalPred single
                        | SPAnd items ->
                            match evalPredList items with
                            | Ok(ssas, ops) ->
                                let out = v ()
                                Ok(out, ops @ [ smt (SMTAnd(out, ssas)) ])
                            | Error err -> Error err
                        | SPOr [] ->
                            let out, ops = boolConst false
                            Ok(out, ops)
                        | SPOr [ single ] -> evalPred single
                        | SPOr items ->
                            match evalPredList items with
                            | Ok(ssas, ops) ->
                                let out = v ()
                                Ok(out, ops @ [ smt (SMTOr(out, ssas)) ])
                            | Error err -> Error err
                        | SPNot inner ->
                            match evalPred inner with
                            | Ok(innerSSA, ops) ->
                                let out = v ()
                                Ok(out, ops @ [ smt (SMTNot(out, innerSSA)) ])
                            | Error err -> Error err
                    match buildPreds varMap with
                    | Error err -> Error err
                    | Ok preds ->
                        let rec evalAll accSSAs accOps remaining =
                            match remaining with
                            | [] -> Ok(List.rev accSSAs, List.rev accOps |> List.concat)
                            | p :: rest ->
                                match evalPred p with
                                | Ok(ssa, ops) -> evalAll (ssa :: accSSAs) (ops :: accOps) rest
                                | Error err -> Error err
                        match evalAll [] [] preds with
                        | Error err -> Error err
                        | Ok(clauseSSAs, clauseOps) ->
                            let conclusion = v ()
                            let body =
                                declAndPinOps
                                @ clauseOps
                                @ [ smt (SMTAnd(conclusion, clauseSSAs)) ]
                            Ok (anchor conclusion body)
            match f.Kind with
            | BAREWire.Platform.FormKind.SharedBufferSpaceExtent ->
                if Array.length f.Names = 0
                   || Array.length f.Values <> 2 * Array.length f.Names
                   || (f.Names |> Array.exists Alex.Text.isBlank)
                   || (Set.ofArray f.Names).Count <> Array.length f.Names then
                    Error (sprintf "Obligation '%s' has invalid SharedBufferSpaceExtent values." ob.Id)
                else
                    let count = Array.length f.Names
                    let spaceCap = v ()
                    let capConst = v ()
                    let capEq = v ()
                    let capPremise =
                        [ smt (SMTDeclareFun(spaceCap, "space_cap", SMTInt))
                          smt (SMTIntConstant(capConst, f.A))
                          smt (SMTEq(capEq, spaceCap, capConst, SMTInt))
                          smt (SMTAssert capEq) ]
                    let rec declareRegions idx accDecls accRegions =
                        if idx >= count then
                            Ok(List.rev accDecls |> List.concat, List.rev accRegions)
                        else
                            match Array.tryItem (2 * idx) f.Values, Array.tryItem (2 * idx + 1) f.Values with
                            | Some offVal, Some lenVal ->
                                let offSSA = v ()
                                let offC = v ()
                                let offEq = v ()
                                let lenSSA = v ()
                                let lenC = v ()
                                let lenEq = v ()
                                let ops =
                                    [ smt (SMTDeclareFun(offSSA, sprintf "off_%d" idx, SMTInt))
                                      smt (SMTIntConstant(offC, offVal))
                                      smt (SMTEq(offEq, offSSA, offC, SMTInt))
                                      smt (SMTAssert offEq)
                                      smt (SMTDeclareFun(lenSSA, sprintf "len_%d" idx, SMTInt))
                                      smt (SMTIntConstant(lenC, lenVal))
                                      smt (SMTEq(lenEq, lenSSA, lenC, SMTInt))
                                      smt (SMTAssert lenEq) ]
                                declareRegions (idx + 1) (ops :: accDecls) ((offSSA, lenSSA) :: accRegions)
                            | _ ->
                                Error (sprintf "Obligation '%s' has truncated SharedBufferSpaceExtent values." ob.Id)
                    match declareRegions 0 [] [] with
                    | Error err -> Error err
                    | Ok(regionPremises, regions) ->
                        let zero = v ()
                        let zeroOp = [ smt (SMTIntConstant(zero, 0L)) ]
                        let perRegion =
                            regions
                            |> List.map (fun (offSSA, lenSSA) ->
                                let geZero = v ()
                                let gtZero = v ()
                                let endSSA = v ()
                                let leCap = v ()
                                let ops =
                                    [ smt (SMTIntCmp(geZero, SmtGe, offSSA, zero))
                                      smt (SMTIntCmp(gtZero, SmtGt, lenSSA, zero))
                                      smt (SMTIntAdd(endSSA, offSSA, lenSSA))
                                      smt (SMTIntCmp(leCap, SmtLe, endSSA, spaceCap)) ]
                                (offSSA, lenSSA, endSSA), [ geZero; gtZero; leCap ], ops)
                        let regionTriples = perRegion |> List.map (fun (t, _, _) -> t)
                        let perRegionClauses = perRegion |> List.collect (fun (_, c, _) -> c)
                        let perRegionOps = perRegion |> List.collect (fun (_, _, o) -> o)
                        let sumClause, sumOps =
                            match regionTriples |> List.map (fun (_, lenSSA, _) -> lenSSA) with
                            | [] ->
                                let leCap = v ()
                                leCap, [ smt (SMTIntCmp(leCap, SmtLe, zero, spaceCap)) ]
                            | firstLen :: restLens ->
                                let totalSSA, addOps =
                                    restLens
                                    |> List.fold (fun (accSSA, accOps) nextLen ->
                                        let nextSum = v ()
                                        nextSum, accOps @ [ smt (SMTIntAdd(nextSum, accSSA, nextLen)) ]) (firstLen, [])
                                let leCap = v ()
                                leCap, addOps @ [ smt (SMTIntCmp(leCap, SmtLe, totalSSA, spaceCap)) ]
                        let indexedTriples = List.indexed regionTriples
                        let disjPairs =
                            [ for (i, (offI, _, endI)) in indexedTriples do
                                for (_, (offJ, _, endJ)) in List.skip (i + 1) indexedTriples do
                                    let leftBefore = v ()
                                    let rightBefore = v ()
                                    let disj = v ()
                                    yield
                                        disj,
                                        [ smt (SMTIntCmp(leftBefore, SmtLe, endI, offJ))
                                          smt (SMTIntCmp(rightBefore, SmtLe, endJ, offI))
                                          smt (SMTOr(disj, [ leftBefore; rightBefore ])) ] ]
                        let disjClauses = disjPairs |> List.map fst
                        let disjOps = disjPairs |> List.collect snd
                        let allClauses = perRegionClauses @ [ sumClause ] @ disjClauses
                        let conclusion = v ()
                        let body =
                            capPremise
                            @ regionPremises
                            @ zeroOp
                            @ perRegionOps
                            @ sumOps
                            @ disjOps
                            @ [ smt (SMTAnd(conclusion, allClauses)) ]
                        Ok (anchor conclusion body)
            | BAREWire.Platform.FormKind.SharedBufferExtent ->
                transcribeNamedSharedBufferForm (fun _ ->
                    let stride = f.A
                    Ok
                        [ gtVar "elem_size" 0L
                          gtVar "measured_size" 0L
                          eqVar "measured_size" stride
                          eqVars "elem_size" "measured_size"
                          gtVar "elem_count" 0L
                          gtVar "region_bytes" 0L
                          gtVar "space_cap" 0L
                          gtVar "buffer_cap" 0L
                          SPEq(STVar "required_bytes", STMul(STVar "elem_count", STConst stride))
                          leVar "required_bytes" 2147483647L
                          SPCmp(SmtGe, STVar "region_bytes", STVar "required_bytes")
                          SPCmp(SmtLe, STVar "region_bytes", STVar "space_cap")
                          SPCmp(SmtLe, STVar "region_bytes", STVar "buffer_cap")
                          geVar "space_offset" 0L
                          SPCmp(SmtLe, STAdd(STVar "space_offset", STVar "region_bytes"), STVar "space_cap")
                          geVar "max_elem_idx" 0L
                          SPCmp(SmtLt, STVar "max_elem_idx", STVar "elem_count") ])
            | BAREWire.Platform.FormKind.SharedBufferLayout ->
                transcribeNamedSharedBufferForm (fun varMap ->
                    if f.A <= 0L || f.A > 1024L then
                        Error (sprintf "Obligation '%s' has out-of-range field count %d." ob.Id f.A)
                    else
                        let fieldCount = int f.A
                        if Map.containsKey (sprintf "field_name_len_%d" fieldCount) varMap
                           || Map.containsKey (sprintf "field_off_%d" fieldCount) varMap then
                            Error (sprintf "Obligation '%s' has trailing field symbols beyond field count %d." ob.Id fieldCount)
                        else
                            let mayAlias = f.B <> 0L
                            let basePreds =
                                [ gtVar "placement_name_len" 0L
                                  gtVar "measured_size" 0L
                                  gtVar "struct_bytes" 0L
                                  eqVars "elem_size" "measured_size"
                                  eqVars "struct_bytes" "measured_size"
                                  eqVars "struct_align" "layout_align"
                                  eqVars "view_align" "layout_align"
                                  SPCmp(SmtGe, STVar "region_align", STVar "layout_align")
                                  SPCmp(SmtLe, STVar "region_align", STVar "space_align")
                                  geVar "space_offset" 0L
                                  pow2Disjunction "space_align"
                                  dividesBothFrom pow2Constants "measured_size" "region_align" "layout_align"
                                  dividesBothFrom pow2Constants "space_align" "space_offset" "region_align"
                                  gtVar "view_schema_len" 0L
                                  gtVar "buffer_schema_len" 0L
                                  SPCmp(SmtGe, STVar "measured_size", STVar "view_elem_width")
                                  SPCmp(SmtGe, STVar "view_align", STVar "view_elem_width")
                                  SPCmp(SmtGe, STVar "layout_align", STVar "view_elem_width")
                                  dividesBothFrom elemWidthConstants "measured_size" "view_align" "view_elem_width"
                                  SPOr [ eqVar "core_byte_order" 1L; eqVar "core_byte_order" 2L ]
                                  eqVars "space_byte_order" "core_byte_order"
                                  eqVars "layout_byte_order" "space_byte_order"
                                  SPOr
                                      [ SPAnd [ eqVar "space_kind" 1L; eqVar "memory_region" 1L ]
                                        SPAnd [ eqVar "space_kind" 2L; eqVar "memory_region" 2L ]
                                        SPAnd [ eqVar "space_kind" 3L; eqVar "memory_region" 3L ]
                                        SPAnd [ eqVar "space_kind" 4L; eqVar "memory_region" 4L ]
                                        SPAnd [ eqVar "space_kind" 5L; SPOr [ eqVar "memory_region" 1L; eqVar "memory_region" 2L ] ] ]
                                  eqVar "raw_ptr_field_count" 0L
                                  eqVar "flex_array_count" 0L
                                  eqVar "unverified_export_count" 0L
                                  eqVar "duplicate_name_count" 0L
                                  gtVar "field_count" 0L ]
                            let fieldAndBitfieldPreds =
                                [ for fk in 0 .. fieldCount - 1 do
                                    let fNameLen = sprintf "field_name_len_%d" fk
                                    let fDupName = sprintf "field_dup_name_%d" fk
                                    let fOff = sprintf "field_off_%d" fk
                                    let fCount = sprintf "field_elem_count_%d" fk
                                    let fLen = sprintf "field_len_%d" fk
                                    let fAlign = sprintf "field_align_%d" fk
                                    yield gtVar fNameLen 0L
                                    yield eqVar fDupName 0L
                                    yield geVar fOff 0L
                                    yield gtVar fCount 0L
                                    yield gtVar fLen 0L
                                    yield SPCmp(SmtLe, STAdd(STVar fOff, STVar fLen), STVar "measured_size")
                                    yield SPCmp(SmtGe, STVar "layout_align", STVar fAlign)
                                    yield fieldGeometryFrom elemWidthConstants fOff fCount fLen fAlign
                                    let rec countBf b =
                                        if Map.containsKey (sprintf "bf_pos_%d_%d" fk b) varMap then
                                            countBf (b + 1)
                                        else b
                                    let bfCount = countBf 0
                                    for b in 0 .. bfCount - 1 do
                                        let bfNameLen = sprintf "bf_name_len_%d_%d" fk b
                                        let bfDupName = sprintf "bf_dup_name_%d_%d" fk b
                                        let bfPos = sprintf "bf_pos_%d_%d" fk b
                                        let bfWidth = sprintf "bf_width_%d_%d" fk b
                                        let bfAccess = sprintf "bf_access_%d_%d" fk b
                                        yield gtVar bfNameLen 0L
                                        yield eqVar bfDupName 0L
                                        yield geVar bfPos 0L
                                        yield gtVar bfWidth 0L
                                        yield SPCmp(SmtLe, STAdd(STVar bfPos, STVar bfWidth), STMul(STVar fAlign, STConst 8L))
                                        yield geVar bfAccess 1L
                                        yield leVar bfAccess 3L
                                    if bfCount >= 2 then
                                        for ba in 0 .. bfCount - 2 do
                                            let posA = STVar(sprintf "bf_pos_%d_%d" fk ba)
                                            let widA = STVar(sprintf "bf_width_%d_%d" fk ba)
                                            for bb in ba + 1 .. bfCount - 1 do
                                                let posB = STVar(sprintf "bf_pos_%d_%d" fk bb)
                                                let widB = STVar(sprintf "bf_width_%d_%d" fk bb)
                                                yield SPOr [ SPCmp(SmtLe, STAdd(posA, widA), posB); SPCmp(SmtLe, STAdd(posB, widB), posA) ] ]
                            let nonOverlapPreds =
                                if not mayAlias && fieldCount >= 2 then
                                    [ for fi in 0 .. fieldCount - 2 do
                                        let offI = STVar(sprintf "field_off_%d" fi)
                                        let lenI = STVar(sprintf "field_len_%d" fi)
                                        for fj in fi + 1 .. fieldCount - 1 do
                                            let offJ = STVar(sprintf "field_off_%d" fj)
                                            let lenJ = STVar(sprintf "field_len_%d" fj)
                                            yield SPOr [ SPCmp(SmtLe, STAdd(offI, lenI), offJ); SPCmp(SmtLe, STAdd(offJ, lenJ), offI) ] ]
                                else []
                            Ok(basePreds @ fieldAndBitfieldPreds @ nonOverlapPreds))
            | BAREWire.Platform.FormKind.SharedBufferLifetime ->
                transcribeNamedSharedBufferForm (fun _ ->
                    Ok
                        [ gtVar "region_depth" 0L
                          geVar "lib_retention_depth" 0L
                          SPCmp(SmtLe, STVar "region_depth", STVar "lib_retention_depth")
                          geVar "mapped_depth" 0L
                          SPCmp(SmtLe, STVar "mapped_depth", STVar "first_use_depth")
                          SPCmp(SmtLe, STVar "first_use_depth", STVar "last_use_depth")
                          SPCmp(SmtLe, STVar "last_use_depth", STVar "lib_retention_end_depth")
                          SPCmp(SmtLt, STVar "lib_retention_end_depth", STVar "unmap_depth")
                          eqVar "leaked" 0L ])
            | BAREWire.Platform.FormKind.SharedBufferExclusivity ->
                transcribeNamedSharedBufferForm (fun varMap ->
                    if f.A <= 0L || f.A > 1024L then
                        Error (sprintf "Obligation '%s' has out-of-range field count %d." ob.Id f.A)
                    else
                        let fieldCount = int f.A
                        if Map.containsKey (sprintf "field_access_%d" fieldCount) varMap then
                            Error (sprintf "Obligation '%s' has trailing field_access symbols beyond field count %d." ob.Id fieldCount)
                        else
                            let basePreds =
                                [ SPOr
                                      [ SPAnd [ eqVar "declared_access" 1L; eqVar "view_access" 1L ]
                                        SPAnd [ eqVar "declared_access" 2L; eqVar "view_access" 2L ]
                                        SPAnd [ eqVar "declared_access" 3L; eqVar "view_access" 3L ]
                                        SPAnd [ eqVar "declared_access" 4L; eqVar "view_access" 3L ] ]
                                  SPOr
                                      [ SPAnd [ eqVar "declared_access" 1L; SPOr [ eqVar "space_access" 1L; eqVar "space_access" 3L ] ]
                                        SPAnd [ eqVar "declared_access" 2L; SPOr [ eqVar "space_access" 2L; eqVar "space_access" 3L ] ]
                                        SPAnd [ SPOr [ eqVar "declared_access" 3L; eqVar "declared_access" 4L ]; eqVar "space_access" 3L ] ]
                                  SPOr
                                      [ SPAnd [ eqVar "declared_access" 1L; SPOr [ eqVar "buffer_access" 1L; eqVar "buffer_access" 3L ] ]
                                        SPAnd [ eqVar "declared_access" 2L; SPOr [ eqVar "buffer_access" 2L; eqVar "buffer_access" 3L ] ]
                                        SPAnd [ SPOr [ eqVar "declared_access" 3L; eqVar "declared_access" 4L ]; eqVar "buffer_access" 3L ] ]
                                  SPOr [ eqVar "lib_mutates" 0L; eqVar "lib_mutates" 1L ]
                                  SPNot (SPAnd [ eqVar "declared_access" 1L; eqVar "lib_mutates" 1L ])
                                  eqVar "concurrent_clef_write" 0L
                                  eqVar "overlap_mutable_share" 0L ]
                            let fieldPreds =
                                [ for fk in 0 .. fieldCount - 1 ->
                                    let fa = sprintf "field_access_%d" fk
                                    SPOr
                                        [ SPAnd [ eqVar "declared_access" 1L; eqVar fa 1L ]
                                          SPAnd [ eqVar "declared_access" 2L; eqVar fa 2L ]
                                          SPAnd
                                              [ SPOr [ eqVar "declared_access" 3L; eqVar "declared_access" 4L ]
                                                SPOr [ eqVar fa 1L; eqVar fa 3L ] ] ] ]
                            Ok(basePreds @ fieldPreds))
            | _ ->
                Error (sprintf "Obligation '%s' has unsupported shared-buffer form kind." ob.Id)

    let opsResult : Result<MLIROp list, string> =
        match ob.Body with
        | ObligationBody.Pending _ ->
            Error "A Pending obligation has no solver scope."
        | ObligationBody.SharedBufferPlacementObligation bareOb ->
            sharedBufferObligation bareOb
        | ObligationBody.ZeroCopyBufferExtent model ->
            let maxCount, maxCountOps = intConst model.MaximumCount
            let elemBytes, elemBytesOps = int64Const model.ElementBytes
            let scaledMax = v ()
            let cap, capOps = intConst model.ExtentCapacity
            let boundOut = v ()
            let scaledClause =
                boundOut,
                maxCountOps
                @ elemBytesOps
                @ [ smt (SMTIntMul(scaledMax, maxCount, elemBytes)) ]
                @ capOps
                @ [ smt (SMTIntCmp(boundOut, SmtLe, scaledMax, cap)) ]
            Ok (
                anchorClauses
                    [ cmpVal SmtLe 0I model.MinimumCount
                      cmpVal SmtLe model.MinimumCount model.MaximumCount
                      scaledClause
                      cmpInt SmtGt model.ElementBytes 0 ])
        | ObligationBody.BufferRetentionDomination model ->
            let acq = model.AcquireOrder
            let modeClauses =
                match model.Mode with
                | BufferRetentionMode.DuringCall ->
                    [ eqInt32 model.RetirementOrders.Length 0 ]
                | BufferRetentionMode.RetainedUntilOwner(ownerParam, releaseCount) ->
                    [ cmpInt SmtGe ownerParam 0
                      cmpInt SmtGt releaseCount 0
                      eqInt32 releaseCount model.RetirementOrders.Length ]
                    @ (model.RetirementOrders |> List.map (fun ord -> cmpInt SmtLt acq ord))
            Ok (anchorClauses (cmpInt SmtGe acq 0 :: modeClauses))
        | ObligationBody.UncountedPathTermination model ->
            let modeClause =
                match model.Mode with
                | UncountedPathStagingMode.StaticImageZeroCopy poolEntry ->
                    cmpInt SmtGe poolEntry 0
                | UncountedPathStagingMode.CallScopedStaged(_, capacity) ->
                    let cap, capOps = int64Const capacity
                    let len, lenOps = intConst model.ByteLength
                    let one, oneOps = int64Const 1
                    let sum, eqOut = v (), v ()
                    eqOut, capOps @ lenOps @ oneOps @ [ smt (SMTIntAdd(sum, len, one)); smt (SMTEq(eqOut, cap, sum, SMTInt)) ]
            Ok (
                anchorClauses
                    [ cmpVal SmtGe model.ByteLength 0I
                      boolConst model.RequiresNoInteriorNul
                      boolConst model.RequiresTrailingNul
                      modeClause ])
        | ObligationBody.BorrowedResultViewScope model ->
            let callOrd = model.CallOrder
            let invClauses = model.InvalidationOrders |> List.map (fun inv -> cmpInt SmtGt inv callOrd)
            let readClauses =
                model.ReadOrders |> List.collect (fun rd ->
                    cmpInt SmtGe rd callOrd
                    :: (model.InvalidationOrders |> List.map (fun inv -> cmpInt SmtLt rd inv)))
            Ok (
                anchorClauses
                    ([ cmpInt SmtGe callOrd 0
                       boolConst model.NullToNoneBoundary
                       cmpInt SmtGt model.InvalidationOrders.Length 0 ]
                     @ invClauses @ readClauses))
        | ObligationBody.BufferAbsenceArgumentConversion model -> BufferAbsenceArgumentProof.project model |> resource
        | ObligationBody.SnapshotBorrowBound(count, snapshot, copy, allocation, minimum, maximum, elementBytes, allocationCapacity) ->
            SnapshotBorrowProof.ofBounds count snapshot copy allocation minimum maximum elementBytes allocationCapacity |> resource
        | ObligationBody.ResourceConversion model -> ResourceProof.ofConversion model |> resource
        | ObligationBody.ResourceCleanup model -> ResourceProof.ofCleanup model |> resource
        | ObligationBody.OptionalEntryArgumentConversion model -> OptionalEntryArgumentProof.project model |> resource
        | ObligationBody.OptionalEntryAbsenceArgumentConversion model -> OptionalEntryArgumentProof.projectAbsence model |> resource
        | ObligationBody.ForeignResultCoverage model ->
            ForeignResultCoverage.ofModel model
            |> Result.mapError (fun reason -> sprintf "Obligation '%s': %s" ob.Id reason)
            |> Result.map (fun projection ->
                let declaredTerms = ForeignResultCoverage.declaredTerms projection

                let declared =
                    declaredTerms
                    |> List.map (fun item -> item, (v (), ForeignResultCoverage.termName item))
                    |> Map.ofList

                let declarations =
                    declaredTerms
                    |> List.map (fun item ->
                        let value, name = declared[item]
                        smt (SMTDeclareFun(value, name, SMTInt)))

                let term =
                    function
                    | ForeignResultCoverage.Term.Constant value ->
                        let name = v ()
                        name, [ smt (SMTBigIntConstant(name, value)) ]
                    | variable -> fst declared[variable], []
                // Structural formatting of the canonical predicate, not graph
                // analysis or a second coverage formula.
                let rec predicate =
                    function
                    | ForeignResultCoverage.Predicate.LessOrEqual(left, right) ->
                        let left, leftOps = term left
                        let right, rightOps = term right
                        let value = v ()
                        value, leftOps @ rightOps @ [ smt (SMTIntCmp(value, SmtLe, left, right)) ]
                    | ForeignResultCoverage.Predicate.And [] ->
                        let zero, value = v (), v ()
                        value, [ smt (SMTBigIntConstant(zero, 0I)); smt (SMTEq(value, zero, zero, SMTInt)) ]
                    | ForeignResultCoverage.Predicate.And clauses ->
                        let values = clauses |> List.map predicate
                        let value = v ()
                        value, (values |> List.collect snd) @ [ smt (SMTAnd(value, List.map fst values)) ]
                    | ForeignResultCoverage.Predicate.Implies(premise, conclusion) ->
                        let premise, premiseOps = predicate premise
                        let conclusion, conclusionOps = predicate conclusion
                        let negated, value = v (), v ()

                        value,
                        premiseOps
                        @ conclusionOps
                        @ [ smt (SMTNot(negated, premise)); smt (SMTOr(value, [ negated; conclusion ])) ]

                let premise, premiseOps = predicate (ForeignResultCoverage.refutationPremises projection)
                let conclusion, body = predicate projection.Conclusion
                anchor conclusion (declarations @ premiseOps @ body @ [ smt (SMTAssert premise) ]))
        | ObligationBody.ProgramInitializationOrder(initializerOrdinal, initializerCount, useOrdinals) ->
            let constant (value: int) =
                let name = v ()
                name, [smt (SMTBigIntConstant(name, (NumericLiteralI.FromString (string value))))]
            let ordinal, ordinalOps = constant initializerOrdinal
            let count, countOps = constant initializerCount
            let zero, zeroOps = constant 0
            let nonnegative, inPlan = v (), v ()
            let uses = useOrdinals |> List.map (fun useOrdinal ->
                let usePhase, useOps = constant useOrdinal
                let after, bounded = v (), v ()
                [after; bounded], useOps @
                    [smt (SMTIntCmp(after, SmtLt, ordinal, usePhase))
                     smt (SMTIntCmp(bounded, SmtLe, usePhase, count))])
            let conclusion = v ()
            Ok (
                anchor conclusion
                    (ordinalOps @ countOps @ zeroOps @
                     [smt (SMTIntCmp(nonnegative, SmtLe, zero, ordinal))
                      smt (SMTIntCmp(inPlan, SmtLt, ordinal, count))] @
                     (uses |> List.collect snd) @
                     [smt (SMTAnd(conclusion, nonnegative :: inPlan :: (uses |> List.collect fst)))]))
        | ObligationBody.FiniteLoopTrip model ->
            let mutable statements: MLIROp list = []
            let constant value =
                let output = v ()
                statements <- (smt (SMTBigIntConstant(output, value))) :: statements
                output
            let cmp pred left right =
                let output = v ()
                statements <- (smt (SMTIntCmp(output, pred, left, right))) :: statements
                output
            let start, limit = constant model.InitialLower, constant model.LimitUpper
            let step, count, zero = constant model.MinimumStep, constant model.MaximumIterations, constant 0I
            let distance, ending = v (), v ()
            statements <- (smt (SMTIntMul(distance, count, step))) :: statements
            statements <- (smt (SMTIntAdd(ending, start, distance))) :: statements
            let clauses = [cmp SmtGt step zero; cmp SmtGe count zero
                           cmp (if model.Inclusive then SmtGt else SmtGe) ending limit]
            let conclusion = v ()
            statements <- (smt (SMTAnd(conclusion, clauses))) :: statements
            Ok (anchor conclusion (List.rev statements))
        | ObligationBody.FiniteSequencePull model ->
            let steps = model.Steps |> List.map (fun step -> step.Label, step) |> Map.ofList
            let wellShaped =
                not model.Steps.IsEmpty && steps.Count = model.Steps.Length &&
                steps.ContainsKey model.Entry &&
                (model.Steps |> List.forall (fun step -> step.Successors |> List.forall steps.ContainsKey))
            if not wellShaped then Ok (integerComparisons [1I, 0I])
            else
                let constant value =
                    let result = v ()
                    result, [smt (SMTBigIntConstant(result, value))]
                let lessOrEqual (left, leftOps) (right, rightOps) =
                    let result = v ()
                    result, leftOps @ rightOps @ [smt (SMTIntCmp(result, SmtLe, left, right))]
                let plus (left, leftOps) (right, rightOps) =
                    let result = v ()
                    result, leftOps @ rightOps @ [smt (SMTIntAdd(result, left, right))]
                let clauses =
                    [ yield lessOrEqual (constant 0I) (constant model.MaximumPulls)
                      yield lessOrEqual (constant steps[model.Entry].Remaining) (constant model.MaximumPulls)
                      for step in model.Steps do
                          yield lessOrEqual (constant 0I) (constant step.Remaining)
                          let weight = if step.Suspend then 1I else 0I
                          match step.Successors with
                          | [] -> yield lessOrEqual (constant weight) (constant step.Remaining)
                          | successors ->
                              for successor in successors do
                                  yield lessOrEqual
                                      (plus (constant weight) (constant steps[successor].Remaining))
                                      (constant step.Remaining) ]
                let conclusion = v ()
                Ok (anchor conclusion ((clauses |> List.collect snd) @ [smt (SMTAnd(conclusion, List.map fst clauses))]))
        | ObligationBody.AdditiveLoopInvariant model ->
            let mutable statements: MLIROp list = []
            let constant value =
                let output = v ()
                statements <- (smt (SMTBigIntConstant(output, value))) :: statements
                output
            let declare name =
                let output = v ()
                statements <- (smt (SMTDeclareFun(output, name, SMTInt))) :: statements
                output
            let binary make left right =
                let output = v ()
                statements <- (smt (make (output, left, right))) :: statements
                output
            let cmp pred left right =
                let output = v ()
                statements <- (smt (SMTIntCmp(output, pred, left, right))) :: statements
                output
            let conjunction clauses =
                let output = v ()
                statements <- (smt (SMTAnd(output, clauses))) :: statements
                output
            let implies premise conclusion =
                let negated, output = v (), v ()
                statements <- (smt (SMTNot(negated, premise))) :: statements
                statements <- (smt (SMTOr(output, [negated; conclusion]))) :: statements
                output
            let lo, hi = constant model.InitialLower, constant model.InitialUpper
            let dlo, dhi = constant model.DeltaLower, constant model.DeltaUpper
            let lower, upper = constant model.Lower, constant model.Upper
            let count, zero, one = constant model.MaximumIterations, constant 0I, constant 1I
            let down, up = constant (min 0I model.DeltaLower), constant (max 0I model.DeltaUpper)
            let k, value, delta = declare "recurrence_k", declare "recurrence_value", declare "recurrence_delta"
            let envelope seed slope iteration = binary SMTIntAdd seed (binary SMTIntMul iteration slope)
            let lowAtK, highAtK = envelope lo down k, envelope hi up k
            let domain = conjunction [cmp SmtLe zero k; cmp SmtLe k count]
            let enclosed = conjunction [cmp SmtLe lower lowAtK; cmp SmtLe highAtK upper]
            let stepDomain = conjunction [cmp SmtLe zero k; cmp SmtLt k count
                                          cmp SmtLe lowAtK value; cmp SmtLe value highAtK
                                          cmp SmtLe dlo delta; cmp SmtLe delta dhi]
            let nextK, nextValue = binary SMTIntAdd k one, binary SMTIntAdd value delta
            let preserved = conjunction [cmp SmtLe (envelope lo down nextK) nextValue
                                         cmp SmtLe nextValue (envelope hi up nextK)]
            // Numeric consistency is part of the conclusion. Global assertions
            // here would hide malformed models behind an empty premise domain.
            let conclusion = conjunction [cmp SmtGe count zero; cmp SmtLe lo hi; cmp SmtLe dlo dhi
                                          cmp SmtLe lower upper; cmp SmtLe lower lo; cmp SmtLe hi upper
                                          implies domain enclosed; implies stepDomain preserved]
            Ok (anchor conclusion (List.rev statements))
        | ObligationBody.FiniteAdditiveEffects(initial, contributions, lower, upper) ->
            let mutable statements: MLIROp list = []
            let constant value =
                let output = v ()
                statements <- (smt (SMTBigIntConstant(output, value))) :: statements
                output
            let binary make left right =
                let output = v ()
                statements <- (smt (make(output, left, right))) :: statements
                output
            let cmp predicate left right =
                let output = v ()
                statements <- (smt (SMTIntCmp(output, predicate, left, right))) :: statements
                output
            let conjunction values =
                let output = v ()
                statements <- (smt (SMTAnd(output, values))) :: statements
                output
            let zero = constant 0I
            let mutable total = constant initial
            let mutable domain = [cmp SmtLe zero zero]
            let mutable counts = []
            for index, (maximum, delta) in List.indexed contributions do
                let actual = v ()
                statements <- (smt (SMTDeclareFun(actual, sprintf "effect_count_%d" index, SMTInt))) :: statements
                let maximum, delta = constant maximum, constant delta
                counts <- cmp SmtGe maximum zero :: counts
                domain <- cmp SmtLe zero actual :: cmp SmtLe actual maximum :: domain
                total <- binary SMTIntAdd total (binary SMTIntMul actual delta)
            let enclosed = conjunction [cmp SmtLe (constant lower) total; cmp SmtLe total (constant upper)]
            let premise = conjunction domain
            let negated, implication = v (), v ()
            statements <- (smt (SMTNot(negated, premise))) :: statements
            statements <- (smt (SMTOr(implication, [negated; enclosed]))) :: statements
            let conclusion = conjunction (implication :: counts)
            Ok (anchor conclusion (List.rev statements))
        | ObligationBody.FiniteLinearRecurrence model ->
            let dimension = model.InitialLower.Length
            let vectorShape values = List.length values = dimension
            let matrixShape rows = List.length rows = dimension && List.forall vectorShape rows
            let wellShaped =
                (dimension = 1 || dimension = 2) && vectorShape model.InitialUpper &&
                vectorShape model.Lower && vectorShape model.Upper &&
                matrixShape model.CoefficientLower && matrixShape model.CoefficientUpper &&
                (model.Powers |> List.forall (fun step -> matrixShape step.Matrix))
            if not wellShaped then Ok (integerComparisons [1I, 0I])
            else
                let mutable statements: MLIROp list = []
                let constant value =
                    let output = v ()
                    statements <- (smt (SMTBigIntConstant(output, value))) :: statements
                    output
                let binary make left right =
                    let output = v ()
                    statements <- (smt (make (output, left, right))) :: statements
                    output
                let compare pred left right =
                    let output = v ()
                    statements <- (smt (SMTIntCmp(output, pred, left, right))) :: statements
                    output
                let equal left right =
                    let output = v ()
                    statements <- (smt (SMTEq(output, left, right, SMTInt))) :: statements
                    output
                let vector values = values |> List.map constant |> List.toArray
                let matrix rows = rows |> List.map vector |> List.toArray
                let dot (left: SSA array) (right: SSA array) =
                    Array.map2 (binary SMTIntMul) left right |> Array.reduce (binary SMTIntAdd)
                let multiply (left: SSA array array) (right: SSA array array) =
                    Array.init dimension (fun row ->
                        Array.init dimension (fun column ->
                            dot left.[row] (Array.init dimension (fun k -> right.[k].[column]))))
                let zero, one, two = constant 0I, constant 1I, constant 2I
                let count = constant model.MaximumIterations
                let initialLo, initialHi = vector model.InitialLower, vector model.InitialUpper
                let coefficientLo, coefficientHi = matrix model.CoefficientLower, matrix model.CoefficientUpper
                let lower, upper = vector model.Lower, vector model.Upper
                let mutable clauses: SSA list = []
                clauses <- (compare SmtGe count zero) :: clauses
                for row in 0 .. dimension - 1 do
                    clauses <- (compare SmtLe zero initialLo.[row]) :: clauses
                    clauses <- (compare SmtLe initialLo.[row] initialHi.[row]) :: clauses
                    clauses <- (compare SmtLe lower.[row] zero) :: clauses
                    clauses <- (compare SmtLe initialHi.[row] (dot coefficientHi.[row] initialHi)) :: clauses
                    for column in 0 .. dimension - 1 do
                        clauses <- (compare SmtLe zero coefficientLo.[row].[column]) :: clauses
                        clauses <- (compare SmtLe coefficientLo.[row].[column] coefficientHi.[row].[column]) :: clauses
                let mutable previousExponent = zero
                let mutable previousMatrix =
                    Array.init dimension (fun row -> Array.init dimension (fun column -> if row = column then one else zero))
                for step in model.Powers do
                    let squared = multiply previousMatrix previousMatrix
                    let expected = if step.Odd then multiply squared coefficientHi else squared
                    let supplied = matrix step.Matrix
                    let exponent = constant step.Exponent
                    clauses <- (equal exponent (binary SMTIntAdd (binary SMTIntMul two previousExponent) (if step.Odd then one else zero))) :: clauses
                    for row in 0 .. dimension - 1 do
                        for column in 0 .. dimension - 1 do
                            clauses <- (equal supplied.[row].[column] expected.[row].[column]) :: clauses
                    previousExponent <- exponent
                    previousMatrix <- supplied
                clauses <- (equal previousExponent count) :: clauses
                for row in 0 .. dimension - 1 do
                    clauses <- (compare SmtLe (dot previousMatrix.[row] initialHi) upper.[row]) :: clauses
                let conclusion = v ()
                statements <- (smt (SMTAnd(conclusion, List.rev clauses))) :: statements
                // Malformed or false supplied certificates remain refutable;
                // no global assumption can conceal an inconsistent premise.
                Ok (anchor conclusion (List.rev statements))
        | ObligationBody.MappedElementSpan model ->
            let mutable statements: MLIROp list = []
            let declare name =
                let output = v ()
                statements <- (smt (SMTDeclareFun(output, name, SMTInt))) :: statements
                output
            let constant value =
                let output = v ()
                statements <- (smt (SMTBigIntConstant(output, value))) :: statements
                output
            let binary make left right =
                let output = v ()
                statements <- (smt (make (output, left, right))) :: statements
                output
            let cmp pred left right =
                let output = v ()
                statements <- (smt (SMTIntCmp(output, pred, left, right))) :: statements
                output
            let equal left right =
                let output = v ()
                statements <- (smt (SMTEq(output, left, right, SMTInt))) :: statements
                output
            let assume value = statements <- (smt (SMTAssert value)) :: statements
            let baseAddress, bytes, index = declare "mapped_base", declare "mapped_bytes", declare "mapped_index"
            let zero, maximum = constant 0I, constant model.MaximumExtent
            let elementBytes, baseAlignment, elementAlignment = constant ((NumericLiteralI.FromString (string model.ElementBytes))), constant ((NumericLiteralI.FromString (string model.BaseAlignment))), constant ((NumericLiteralI.FromString (string model.ElementAlignment)))
            cmp SmtGt baseAddress zero |> assume
            cmp SmtGt bytes zero |> assume
            cmp SmtLe bytes maximum |> assume
            cmp SmtLe baseAddress (binary SMTIntSub maximum bytes) |> assume
            equal (binary SMTIntMod bytes elementBytes) zero |> assume
            equal (binary SMTIntMod baseAddress baseAlignment) zero |> assume
            cmp SmtLe zero index |> assume
            cmp SmtLt index (binary SMTIntDiv bytes elementBytes) |> assume
            let start = binary SMTIntAdd baseAddress (binary SMTIntMul index elementBytes)
            let ending = binary SMTIntAdd start elementBytes
            let clauses = [cmp SmtLe baseAddress start; cmp SmtLe ending (binary SMTIntAdd baseAddress bytes)
                           cmp SmtLe ending maximum; equal (binary SMTIntMod start elementAlignment) zero]
            let conclusion = v ()
            statements <- (smt (SMTAnd(conclusion, clauses))) :: statements
            Ok (anchor conclusion (List.rev statements))
        | ObligationBody.IntegerLiteralRange (value, lower, upper) ->
            Ok (integerComparisons [ lower, value; value, upper ])
        | ObligationBody.IntegerRepresentationCoverage (lower, upper, minimum, maximum) ->
            Ok (integerComparisons [ minimum, lower; lower, upper; upper, maximum ])
        | ObligationBody.IntegerDivisorNonzero (lower, upper) ->
            let lo, hi, zero = v (), v (), v ()
            let ordered, negative, positive, excludesZero, conclusion = v (), v (), v (), v (), v ()
            Ok (
                anchor conclusion
                    [ smt (SMTBigIntConstant(lo, lower)); smt (SMTBigIntConstant(hi, upper)); smt (SMTBigIntConstant(zero, 0I))
                      smt (SMTIntCmp(ordered, SmtLe, lo, hi))
                      smt (SMTIntCmp(negative, SmtLt, hi, zero)); smt (SMTIntCmp(positive, SmtGt, lo, zero))
                      smt (SMTOr(excludesZero, [negative; positive]))
                      smt (SMTAnd(conclusion, [ordered; excludesZero])) ])
        | ObligationBody.IntegerShiftCount (lower, upper, bits) ->
            let lo, hi, zero, width = v (), v (), v (), v ()
            let positive, nonnegative, ordered, belowWidth, conclusion = v (), v (), v (), v (), v ()
            Ok (
                anchor conclusion
                    [ smt (SMTBigIntConstant(lo, lower)); smt (SMTBigIntConstant(hi, upper))
                      smt (SMTBigIntConstant(zero, 0I)); smt (SMTBigIntConstant(width, (NumericLiteralI.FromString (string bits))))
                      smt (SMTIntCmp(positive, SmtGt, width, zero)); smt (SMTIntCmp(nonnegative, SmtLe, zero, lo))
                      smt (SMTIntCmp(ordered, SmtLe, lo, hi)); smt (SMTIntCmp(belowWidth, SmtLt, hi, width))
                      smt (SMTAnd(conclusion, [positive; nonnegative; ordered; belowWidth])) ])
        | ObligationBody.SpatialKernelPartition(elements, grain, columns, slices, depth, iterations) ->
            let mutable statements: MLIROp list = []
            let constant value =
                let result = v ()
                statements <- (smt (SMTBigIntConstant(result, value))) :: statements
                result
            let cmp predicate left right =
                let result = v ()
                statements <- (smt (SMTIntCmp(result, predicate, left, right))) :: statements
                result
            let binary operation left right =
                let result = v ()
                statements <- (smt (operation(result, left, right))) :: statements
                result
            let equal = binary (fun (result, left, right) -> SMTEq(result, left, right, SMTInt))
            let zero, extent, grain = constant 0I, constant elements, constant grain
            let columns, depth, iterations = constant((NumericLiteralI.FromString (string columns))), constant((NumericLiteralI.FromString (string depth))), constant iterations
            let count = constant((NumericLiteralI.FromString (string slices.Length)))
            let terms = slices |> List.map (fun (column, offset, count) -> constant((NumericLiteralI.FromString (string column))), constant offset, constant count)
            let ends = terms |> List.map (fun (_, offset, count) -> binary SMTIntAdd offset count)
            let clauses =
                [ yield cmp SmtGt extent zero; yield cmp SmtGt grain zero; yield cmp SmtGt columns zero
                  yield cmp SmtGt depth zero; yield cmp SmtGt iterations zero; yield cmp SmtGt count zero
                  yield equal extent (binary SMTIntMul count grain)
                  for ordinal, (column, offset, size) in List.indexed terms do
                      yield cmp SmtLe zero column; yield cmp SmtLt column columns; yield cmp SmtLe zero offset
                      yield equal size grain
                      yield equal offset (if ordinal = 0 then zero else ends[ordinal - 1])
                      yield cmp SmtLe ends[ordinal] extent
                      for other, _, _ in terms |> List.take ordinal do
                          let same, different = equal column other, v ()
                          statements <- (smt (SMTNot(different, same))) :: statements
                          yield different
                  yield equal (List.tryLast ends |> Option.defaultValue zero) extent ]
            let conclusion = v ()
            statements <- (smt (SMTAnd(conclusion, clauses))) :: statements
            Ok (anchor conclusion (List.rev statements))
        | ObligationBody.StringBorrowBound origins ->
            let mutable statements: MLIROp list = []
            let constant value =
                let output = v ()
                statements <- (smt (SMTBigIntConstant(output, value))) :: statements
                output
            let comparison predicate left right =
                let output = v ()
                statements <- (smt (SMTIntCmp(output, predicate, left, right))) :: statements
                output
            let zero = constant 0I
            // A missing origin domain is a false claim, not a vacuous proof.
            let nonempty = comparison SmtGt (constant ((NumericLiteralI.FromString (string origins.Length)))) zero
            let clauses = origins |> List.collect (fun (count, extent, storage) ->
                let count, extent, storage = constant count, constant extent, constant storage
                let sameExtent = v ()
                statements <- (smt (SMTEq(sameExtent, count, extent, SMTInt))) :: statements
                [comparison SmtLe zero count; sameExtent; comparison SmtLt extent storage])
            let conclusion = v ()
            statements <- (smt (SMTAnd(conclusion, nonempty :: clauses))) :: statements
            Ok (anchor conclusion (List.rev statements))
        | ObligationBody.RealLiteralRange (value, lower, upper) ->
            rationalComparisons [ lower, value; value, upper ]
        | ObligationBody.RealRepresentationCoverage (lower, upper, minimum, maximum) ->
            rationalComparisons [ minimum, lower; lower, upper; upper, maximum ]
        | ObligationBody.ApplicationDimensions comparisons ->
            let mutable statements: MLIROp list = []
            let constant value =
                let ssa = v ()
                statements <- (smt (SMTIntConstant(ssa, int64 value))) :: statements
                ssa
            let equation left right =
                let l, r, output = constant left, constant right, v ()
                statements <- (smt (SMTEq(output, l, r, SMTInt))) :: statements
                output
            let clauses =
                [ for _, expected, actual in comparisons do
                    match expected, actual with
                    | Some expected, Some actual ->
                        let coordinates project =
                            let left, right = project expected, project actual
                            Set.union (left |> Map.keys |> Set.ofSeq) (right |> Map.keys |> Set.ofSeq)
                            |> Set.toList
                            |> List.map (fun axis ->
                                (Map.tryFind axis left |> Option.defaultValue 0),
                                (Map.tryFind axis right |> Option.defaultValue 0))
                        let axes = coordinates (fun d -> d.Bases) @ coordinates (fun d -> d.Vars)
                        match axes with
                        | [] -> yield equation 0 0 // Both dimensions are explicitly dimensionless.
                        | _ ->
                            for left, right in axes do
                                yield equation left right
                    | _ -> yield equation 0 1 ] // Missing evidence cannot establish compatibility.
            let definition =
                match clauses with
                | [] -> equation 0 1
                | [single] -> single
                | _ ->
                    let conjunction = v ()
                    statements <- (smt (SMTAnd(conjunction, clauses))) :: statements
                    conjunction
            Ok (anchor definition (List.rev statements))
        | ObligationBody.DimensionalRelation (rule, left, right, result) ->
            let dimensions = left :: right :: Option.toList result
            let coordinates project =
                dimensions |> List.collect (project >> Map.toList >> List.map fst)
                |> Set.ofList |> Set.toList
                |> List.map (fun axis ->
                    let exponent dim = project dim |> Map.tryFind axis |> Option.defaultValue 0
                    exponent left, exponent right, Option.map exponent result)
            let axes = coordinates (fun d -> d.Bases) @ coordinates (fun d -> d.Vars)
            let mutable statements: MLIROp list = []
            let constant value =
                let ssa = v ()
                statements <- (smt (SMTIntConstant(ssa, int64 value))) :: statements
                ssa
            let equation left right =
                let ssa = v ()
                statements <- (smt (SMTEq(ssa, left, right, SMTInt))) :: statements
                ssa
            let clauses =
                [ for left, right, output in axes do
                    let l, r = constant left, constant right
                    match rule, output with
                    | DimensionalRule.Product, Some output
                    | DimensionalRule.Quotient, Some output ->
                        let expected = v ()
                        statements <- (smt (if rule = DimensionalRule.Product then SMTIntAdd(expected, l, r) else SMTIntSub(expected, l, r))) :: statements
                        yield equation (constant output) expected
                    | DimensionalRule.SameDimension, Some output ->
                        yield equation l r
                        yield equation (constant output) l
                    | DimensionalRule.Comparison, None -> yield equation l r
                    | _ -> () ]
            let definition =
                if (rule = DimensionalRule.Comparison) <> Option.isNone result then
                    equation (constant 0) (constant 1)
                else
                    match clauses with
                    | [] -> equation (constant 0) (constant 0)
                    | [single] -> single
                    | _ ->
                        let conjunction = v ()
                        statements <- (smt (SMTAnd(conjunction, clauses))) :: statements
                        conjunction
            Ok (anchor definition (List.rev statements))
        | ObligationBody.StorageReservation (len, storage) ->
            let s = v ()
            let l = v ()
            let one = v ()
            let sum = v ()
            let def = v ()
            Ok (
                anchor def
                    [ smt (SMTIntConstant (s, int64 storage))
                      smt (SMTIntConstant (l, int64 len))
                      smt (SMTIntConstant (one, 1L))
                      smt (SMTIntAdd (sum, l, one))
                      smt (SMTEq (def, s, sum, SMTInt)) ])
        | ObligationBody.ViewContainment (view, len, storage) ->
            let vw = v ()
            let l = v ()
            let s = v ()
            let eq = v ()
            let lt = v ()
            let def = v ()
            Ok (
                anchor def
                    [ smt (SMTIntConstant (vw, int64 view))
                      smt (SMTIntConstant (l, int64 len))
                      smt (SMTIntConstant (s, int64 storage))
                      smt (SMTEq (eq, vw, l, SMTInt))
                      smt (SMTIntCmp (lt, SmtLt, vw, s))
                      smt (SMTAnd (def, [eq; lt])) ])
        | ObligationBody.NulSentinel _ ->
            Error (sprintf "Obligation '%s' uses retired legacy NulSentinel without checked storage coordinates." ob.Id)
        | ObligationBody.MaterializedNulSentinel (entry, offset, observedEntry, observedOffset, observedByte) ->
            let rows =
                ObligationBody.sentinelFields ob.Id (entry, offset, observedEntry, observedOffset, observedByte)
                |> List.map (fun (name, width, observed, expected) ->
                    let variable = v ()
                    let observation = v ()
                    let premise = v ()
                    let claim = v ()
                    let clause = v ()
                    [ smt (SMTDeclareFun (variable, name, SMTBV width))
                      smt (SMTBVConstant (observation, observed, width))
                      smt (SMTEq (premise, variable, observation, SMTBV width))
                      smt (SMTAssert premise)
                      smt (SMTBVConstant (claim, expected, width))
                      smt (SMTEq (clause, variable, claim, SMTBV width)) ], clause)
            let definition = v ()
            Ok (anchor definition ((rows |> List.collect fst) @ [smt (SMTAnd (definition, List.map snd rows))]))
        | ObligationBody.OmittedNulSentinel ->
            Error (sprintf "Obligation '%s' has an established storage omission and no solver scope." ob.Id)
        | ObligationBody.StaticStorageLayout (slots, usedSize, allocationSize, poolAlignment, capacity, spaceAlignment, granularity) ->
            // Every placement is a concrete compiler fact. No adjacency premise
            // assumes the layout that this claim is meant to establish.
            let mutable statements: MLIROp list = []
            let constant (value: bigint) =
                let result = v ()
                statements <- (smt (SMTBigIntConstant(result, value))) :: statements
                result
            let cmp pred a b =
                let result = v ()
                statements <- (smt (SMTIntCmp(result, pred, a, b))) :: statements
                result
            let equal a b =
                let result = v ()
                statements <- (smt (SMTEq(result, a, b, SMTInt))) :: statements
                result
            let any clauses =
                match clauses with
                | [only] -> only
                | _ ->
                    let result = v ()
                    statements <- (smt (SMTOr(result, clauses))) :: statements
                    result
            let zero = constant 0I
            let divisible value divisor =
                // Invalid zero/negative alignments fail a separate conjunct;
                // use a defined modulus so they cannot introduce vacuity.
                let denominator = constant ((NumericLiteralI.FromString (string (max 1 divisor))))
                let remainder = v ()
                statements <- (smt (SMTIntMod(remainder, value, denominator))) :: statements
                equal remainder zero
            let used, allocation = constant ((NumericLiteralI.FromString (string usedSize))), constant ((NumericLiteralI.FromString (string allocationSize)))
            let pool, space, grain, cap = constant ((NumericLiteralI.FromString (string poolAlignment))), constant ((NumericLiteralI.FromString (string spaceAlignment))), constant ((NumericLiteralI.FromString (string granularity))), constant ((NumericLiteralI.FromString (string capacity)))
            let mutable clauses: SSA list = []
            for term in [pool; space; grain] do clauses <- (cmp SmtGt term zero) :: clauses
            clauses <- (cmp SmtGe used zero) :: clauses
            clauses <- (cmp SmtGe cap zero) :: clauses
            clauses <- (cmp SmtLe used allocation) :: clauses
            clauses <- (cmp SmtLe allocation cap) :: clauses
            clauses <- (cmp SmtGe pool space) :: clauses
            clauses <- (divisible allocation granularity) :: clauses
            clauses <- (divisible pool spaceAlignment) :: clauses
            let placements = slots |> List.map (fun (offset, length, alignment) ->
                let beginAt = constant ((NumericLiteralI.FromString (string offset)))
                let lengthTerm = constant ((NumericLiteralI.FromString (string length)))
                let align = constant ((NumericLiteralI.FromString (string alignment)))
                let endAt = v ()
                statements <- (smt (SMTIntAdd(endAt, beginAt, lengthTerm))) :: statements
                clauses <- (cmp SmtGe beginAt zero) :: clauses
                clauses <- (cmp SmtGt lengthTerm zero) :: clauses
                clauses <- (cmp SmtGt align zero) :: clauses
                clauses <- (divisible beginAt alignment) :: clauses
                clauses <- (divisible pool alignment) :: clauses
                clauses <- (cmp SmtLe endAt allocation) :: clauses
                clauses <- (cmp SmtLe endAt used) :: clauses
                beginAt, endAt)
            match placements with
            | [] -> clauses <- (equal used zero) :: clauses
            | _ -> clauses <- (placements |> List.map (fun (_, ending) -> equal ending used) |> any) :: clauses
            for i, (leftBegin, leftEnd) in List.indexed placements do
                for rightBegin, rightEnd in List.skip (i + 1) placements do
                    clauses <- (any [cmp SmtLe leftEnd rightBegin; cmp SmtLe rightEnd leftBegin]) :: clauses
            let definition = v ()
            statements <- (smt (SMTAnd(definition, List.rev clauses))) :: statements
            Ok (anchor definition (List.rev statements))
        | ObligationBody.ContinuationLayout (slots, extent, alignment) ->
            let mutable statements: MLIROp list = []
            let constant value =
                let result = v ()
                statements <- (smt (SMTBigIntConstant(result, value))) :: statements
                result
            let binary make left right =
                let result = v ()
                statements <- (smt (make (result, left, right))) :: statements
                result
            let cmp predicate left right =
                let result = v ()
                statements <- (smt (SMTIntCmp(result, predicate, left, right))) :: statements
                result
            let equal left right =
                let result = v ()
                statements <- (smt (SMTEq(result, left, right, SMTInt))) :: statements
                result
            let any values =
                let result = v ()
                statements <- (smt (SMTOr(result, values))) :: statements
                result
            let zero, one = constant 0I, constant 1I
            let powerOfTwo value =
                [0 .. 30] |> List.map (fun exponent -> equal value (constant (1I <<< exponent))) |> any
            let aligned endpoint required =
                // Nonpositive alignments fail their own clause; use a defined
                // divisor while transcribing the exact rounding equation.
                let divisor = constant ((NumericLiteralI.FromString (string (max 1 required))))
                let adjustment = binary SMTIntSub divisor one
                let rounded = binary SMTIntDiv (binary SMTIntAdd endpoint adjustment) divisor
                binary SMTIntMul rounded divisor
            let extentTerm, alignmentTerm = constant ((NumericLiteralI.FromString (string extent))), constant ((NumericLiteralI.FromString (string alignment)))
            let mutable clauses: SSA list = []
            clauses <- (cmp SmtGe extentTerm zero) :: clauses
            clauses <- (powerOfTwo alignmentTerm) :: clauses
            clauses <- (cmp SmtGe alignmentTerm one) :: clauses
            let mutable previous = zero
            let placements = slots |> List.map (fun (offset, bytes, alignment) ->
                let beginAt, length, required = constant ((NumericLiteralI.FromString (string offset))), constant ((NumericLiteralI.FromString (string bytes))), constant ((NumericLiteralI.FromString (string alignment)))
                let endAt = binary SMTIntAdd beginAt length
                clauses <- (cmp SmtGe beginAt zero) :: clauses
                clauses <- (cmp SmtGt length zero) :: clauses
                clauses <- (powerOfTwo required) :: clauses
                clauses <- (cmp SmtGe alignmentTerm required) :: clauses
                let divisor = constant ((NumericLiteralI.FromString (string (max 1 alignment))))
                clauses <- (equal (binary SMTIntMod beginAt divisor) zero) :: clauses
                clauses <- (equal (binary SMTIntMod alignmentTerm divisor) zero) :: clauses
                clauses <- (equal beginAt (aligned previous alignment)) :: clauses
                clauses <- (cmp SmtLe endAt extentTerm) :: clauses
                previous <- endAt
                beginAt, endAt, required)
            clauses <- (any (equal alignmentTerm one :: (placements |> List.map (fun (_, _, required) -> equal alignmentTerm required)))) :: clauses
            clauses <- (equal extentTerm (aligned previous alignment)) :: clauses
            for index, (leftBegin, leftEnd, _) in List.indexed placements do
                for rightBegin, rightEnd, _ in List.skip (index + 1) placements do
                    clauses <- (any [cmp SmtLe leftEnd rightBegin; cmp SmtLe rightEnd leftBegin]) :: clauses
            let definition = v ()
            statements <- (smt (SMTAnd(definition, List.rev clauses))) :: statements
            Ok (anchor definition (List.rev statements))
        | ObligationBody.EnvironmentStorageReservation (extent, alignment, capacity, spaceAlignment, granularity) ->
            match extent, alignment, capacity, spaceAlignment, granularity with
            | Some extent, Some alignment, Some capacity, Some spaceAlignment, Some granularity ->
                let constant value =
                    let name = v ()
                    name, [smt (SMTBigIntConstant(name, value))]
                let bytes, bytesOps = constant ((NumericLiteralI.FromString (string extent)))
                let align, alignOps = constant ((NumericLiteralI.FromString (string alignment)))
                let spaceAlign, spaceOps = constant ((NumericLiteralI.FromString (string spaceAlignment)))
                let grain, grainOps = constant ((NumericLiteralI.FromString (string granularity)))
                let limit, limitOps = constant ((NumericLiteralI.FromString (string capacity)))
                let zero, zeroOps = constant 0I
                let one, oneOps = constant 1I
                let divisor, divisorOps = constant ((NumericLiteralI.FromString (string (max 1 granularity))))
                let alignDivisor, alignDivisorOps = constant ((NumericLiteralI.FromString (string (max 1 alignment))))
                let powers value =
                    let choices = [0 .. 30] |> List.map (fun exponent ->
                        let power, ops = constant (1I <<< exponent)
                        let clause = v ()
                        clause, ops @ [smt (SMTEq(clause, value, power, SMTInt))])
                    let result = v ()
                    result, (choices |> List.collect snd) @ [smt (SMTOr(result, List.map fst choices))]
                let validAlign, validAlignOps = powers align
                let validSpace, validSpaceOps = powers spaceAlign
                let validGrain, validGrainOps = powers grain
                let positive, remainder, divisible = v (), v (), v ()
                let padding, padded, units, rounded, covered, conclusion = v (), v (), v (), v (), v (), v ()
                Ok (
                    anchor conclusion
                        (bytesOps @ alignOps @ spaceOps @ grainOps @ limitOps @ zeroOps @ oneOps @ divisorOps @ alignDivisorOps
                         @ validAlignOps @ validSpaceOps @ validGrainOps
                         @ [smt (SMTIntCmp(positive, SmtGt, bytes, zero))
                            smt (SMTIntMod(remainder, spaceAlign, alignDivisor))
                            smt (SMTEq(divisible, remainder, zero, SMTInt))
                            smt (SMTIntSub(padding, divisor, one))
                            smt (SMTIntAdd(padded, bytes, padding))
                            smt (SMTIntDiv(units, padded, divisor))
                            smt (SMTIntMul(rounded, units, divisor))
                            smt (SMTIntCmp(covered, SmtLe, rounded, limit))
                            smt (SMTAnd(conclusion, [positive; validAlign; validSpace; validGrain; divisible; covered]))]))
            | _ -> Ok (integerComparisons [1I, 0I])
        | ObligationBody.ConsecutiveLayout (storages, span, capacity) ->
            let sizes = List.toArray storages
            let n' = Array.length sizes
            let bases = [ for i in 0 .. n' - 1 -> v (), sprintf "b%d" i ]
            let baseSSA i = fst bases[i]
            let declOps =
                [ for (ssa, name) in bases -> smt (SMTDeclareFun (ssa, name, SMTInt)) ]
            // b0 >= 0
            let zero = v ()
            let nn = v ()
            let nonNeg =
                [ smt (SMTIntConstant (zero, 0L))
                  smt (SMTIntCmp (nn, SmtGe, baseSSA 0, zero))
                  smt (SMTAssert nn) ]
            // adjacency premises: b[i] = b[i-1] + size[i-1]
            let adjacency =
                [ for i in 1 .. n' - 1 do
                    let c = v ()
                    let a = v ()
                    let eq = v ()
                    yield smt (SMTIntConstant (c, int64 sizes[i-1]))
                    yield smt (SMTIntAdd (a, baseSSA (i-1), c))
                    yield smt (SMTEq (eq, baseSSA i, a, SMTInt))
                    yield smt (SMTAssert eq) ]
            // pairwise disjointness: end_i <= b_j OR end_j <= b_i
            let mutable disjSSAs = []
            let disjoint =
                [ for i in 0 .. n' - 1 do
                    for j in i + 1 .. n' - 1 do
                        let si = v ()
                        let ei = v ()
                        let li = v ()
                        let sj = v ()
                        let ej = v ()
                        let lj = v ()
                        let d = v ()
                        disjSSAs <- disjSSAs @ [d]
                        yield smt (SMTIntConstant (si, int64 sizes[i]))
                        yield smt (SMTIntAdd (ei, baseSSA i, si))
                        yield smt (SMTIntCmp (li, SmtLe, ei, baseSSA j))
                        yield smt (SMTIntConstant (sj, int64 sizes[j]))
                        yield smt (SMTIntAdd (ej, baseSSA j, sj))
                        yield smt (SMTIntCmp (lj, SmtLe, ej, baseSSA i))
                        yield smt (SMTOr (d, [li; lj])) ]
            // span: b[n-1] + size[n-1] = b[0] + span
            let lastSz = v ()
            let hi = v ()
            let spanC = v ()
            let lo = v ()
            let spanEq = v ()
            let def = v ()
            // smt.and is variadic with a two-operand minimum: with exactly one
            // disjointness pair (two strings), use that pair's SSA directly
            let allDisj, allDisjOps =
                match disjSSAs with
                | [only] -> only, []
                | _ -> let a = v () in a, [ smt (SMTAnd (a, disjSSAs)) ]
            // where a declared space bounds the layout: span <= capacity
            let fitsSSAs, fitsOps =
                match capacity with
                | Some cap ->
                    let c = v ()
                    let f = v ()
                    [f], [ smt (SMTIntConstant (c, cap)); smt (SMTIntCmp (f, SmtLe, spanC, c)) ]
                | None -> [], []
            let spanOps =
                [ smt (SMTIntConstant (lastSz, int64 sizes[n' - 1]))
                  smt (SMTIntAdd (hi, baseSSA (n' - 1), lastSz))
                  smt (SMTIntConstant (spanC, int64 span))
                  smt (SMTIntAdd (lo, baseSSA 0, spanC))
                  smt (SMTEq (spanEq, hi, lo, SMTInt)) ]
                @ allDisjOps
                @ fitsOps
                @ [ smt (SMTAnd (def, [allDisj; spanEq] @ fitsSSAs)) ]
            Ok (anchor def (declOps @ nonNeg @ adjacency @ disjoint @ spanOps))
        | ObligationBody.ConcatCopyBound (leftLen, rightLen) ->
            let ll = v ()
            let lr = v ()
            let al = v ()
            let zero = v ()
            let geL = v ()
            let geR = v ()
            let decls =
                [ smt (SMTDeclareFun (ll, "len_l", SMTInt))
                  smt (SMTDeclareFun (lr, "len_r", SMTInt))
                  smt (SMTDeclareFun (al, "alloc", SMTInt))
                  smt (SMTIntConstant (zero, 0L))
                  smt (SMTIntCmp (geL, SmtGe, ll, zero))
                  smt (SMTAssert geL)
                  smt (SMTIntCmp (geR, SmtGe, lr, zero))
                  smt (SMTAssert geR) ]
            // pin an operand to its concrete byte length where the graph has it
            let pin (ssa: SSA) (len: int option) : MLIROp list =
                match len with
                | Some n ->
                    let c = v ()
                    let eq = v ()
                    [ smt (SMTIntConstant (c, int64 n))
                      smt (SMTEq (eq, ssa, c, SMTInt))
                      smt (SMTAssert eq) ]
                | None -> []
            // emission-contract premise: alloc = len_l + len_r
            let sum = v ()
            let aeq = v ()
            let premise =
                [ smt (SMTIntAdd (sum, ll, lr))
                  smt (SMTEq (aeq, al, sum, SMTInt))
                  smt (SMTAssert aeq) ]
            // conclusion: both copy windows lie within the allocation
            let c1 = v ()
            let c2 = v ()
            let def = v ()
            let conclusion =
                [ smt (SMTIntCmp (c1, SmtLe, ll, al))
                  smt (SMTIntCmp (c2, SmtLe, sum, al))
                  smt (SMTAnd (def, [c1; c2])) ]
            Ok (anchor def (decls @ pin ll leftLen @ pin lr rightLen @ premise @ conclusion))

        | ObligationBody.CapacityPositive cap ->
            let c = v ()
            let zero = v ()
            let def = v ()
            Ok (
                anchor def
                    [ smt (SMTIntConstant (c, cap))
                      smt (SMTIntConstant (zero, 0L))
                      smt (SMTIntCmp (def, SmtGt, c, zero)) ])
        | ObligationBody.CapacityFits (cap, spaceCap) ->
            let c = v ()
            let sc = v ()
            let def = v ()
            Ok (
                anchor def
                    [ smt (SMTIntConstant (c, cap))
                      smt (SMTIntConstant (sc, spaceCap))
                      smt (SMTIntCmp (def, SmtLe, c, sc)) ])
        | ObligationBody.InputBufferBound (count, allocation) ->
            let c = v ()
            let a = v ()
            let def = v ()
            Ok (
                anchor def
                    [ smt (SMTIntConstant (c, count))
                      smt (SMTIntConstant (a, allocation))
                      smt (SMTIntCmp (def, SmtLe, c, a)) ])
        | ObligationBody.InputCopyBound (cap, bound) ->
            // for all r, 1 <= r <= cap: r - 1 <= bound
            let r = v ()
            let one = v ()
            let capC = v ()
            let geOne = v ()
            let leCap = v ()
            let rm1 = v ()
            let b = v ()
            let def = v ()
            Ok (
                anchor def
                    [ smt (SMTDeclareFun (r, "r", SMTInt))
                      smt (SMTIntConstant (one, 1L))
                      smt (SMTIntCmp (geOne, SmtGe, r, one))
                      smt (SMTAssert geOne)
                      smt (SMTIntConstant (capC, cap))
                      smt (SMTIntCmp (leCap, SmtLe, r, capC))
                      smt (SMTAssert leCap)
                      smt (SMTIntSub (rm1, r, one))
                      smt (SMTIntConstant (b, bound))
                      smt (SMTIntCmp (def, SmtLe, rm1, b)) ])

    opsResult |> Result.map (fun ops ->
        let logic, transformation =
            match ob.Body with
            | ObligationBody.RealLiteralRange _ | ObligationBody.RealRepresentationCoverage _ ->
                "QF_LIA", [ MLIROp.RawMLIR "// Exact rational bounds: QF_LRA comparisons with positive denominators cleared to QF_LIA." ]
            | _ -> ob.Logic, []
        [ MLIROp.RawMLIR (sprintf "// %s: %s" ob.Id ob.Statement)
          MLIROp.RawMLIR (sprintf "// origin: %s" ob.Source)
        ] @ transformation @ [ smt (SMTSolver (smt (SMTSetLogic logic) :: ops @ [ smt SMTCheck ])) ])

/// The verification module from the graph's obligations.
/// Pure function: ObligationInfo list -> Result<MLIROp list, string>. The list is
/// the complete ledger; only bodies with a solver scope (`ObligationBody.hasSolverScope`)
/// emit solver scopes.
let operations (obs: ObligationInfo list) : Result<MLIROp list, string> =
    let rec loop acc remaining =
        match remaining with
        | [] -> Ok (acc |> List.rev |> List.concat)
        | ob :: rest ->
            if not (ObligationBody.hasSolverScope ob.Body) then loop acc rest
            else
                match scope ob with
                | Ok scopedOps -> loop (scopedOps :: acc) rest
                | Error reason -> Error reason
    loop [] obs

let transfer (obs: ObligationInfo list) : Result<string, string> =
    operations obs
    |> Result.bind (moduleToString (Error "the obligations module carries no pointer-sized type") "obligations")
