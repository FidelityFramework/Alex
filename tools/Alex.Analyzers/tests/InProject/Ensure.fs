module Alex.XParsec.PSGCombinators

type Parser<'a> = Parser of 'a
type Builder() =
  member _.Bind(Parser value, next) = next value
  member _.Return value = Parser value
  member _.Delay f = f ()
let parser = Builder()
let ensure condition message = if condition then Parser () else failwith message
