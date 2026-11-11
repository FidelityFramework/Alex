module internal Alex.Text

let isAsciiLetter c = ('a' <= c && c <= 'z') || ('A' <= c && c <= 'Z')
let isAsciiDigit c = '0' <= c && c <= '9'

let isWhitespace = function
    | '\u0009' | '\u000A' | '\u000B' | '\u000C' | '\u000D' | '\u0020'
    | '\u0085' | '\u00A0' | '\u1680' | '\u2028' | '\u2029' | '\u202F'
    | '\u205F' | '\u3000' -> true
    | c -> '\u2000' <= c && c <= '\u200A'

let isBlank (value: string) =
    // FSharp.Core's length treats a missing string as empty.
    String.length value = 0 || String.forall isWhitespace value

let startsWith (prefix: string) (value: string) =
    String.length value >= String.length prefix
    && Seq.forall2 (=) prefix (Seq.take (String.length prefix) value)

let firstLine (value: string) =
    value |> Seq.takeWhile ((<>) '\n') |> Seq.map string |> String.concat ""

let replace (oldValue: string) newValue (value: string) =
    let count = String.length oldValue
    if count = 0 then invalidArg "oldValue" "Replacement requires a nonempty token."
    let rec loop offset reversed =
        if offset = String.length value then reversed |> List.rev |> String.concat ""
        elif offset + count <= String.length value
             && Seq.forall (fun index -> value[offset + index] = oldValue[index]) (seq { 0 .. count - 1 }) then
            loop (offset + count) (newValue :: reversed)
        else loop (offset + 1) (string value[offset] :: reversed)
    loop 0 []

let exceptionMessage = function
    | Failure message -> message
    | error -> sprintf "%A" error
