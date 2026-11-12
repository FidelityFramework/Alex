module Alex.Cases

open Fidelity.PSG
open Alex.XParsec.PSGCombinators

let historical (handleType: TypeIdentity) bits = parser {
  do! ensure (match handleType with TypeIdentity.Application(constructor, []) -> constructor.Declaration.Name = "Mmio" + string bits | _ -> false) "bad"
  return ()
}

let published bits = parser {
  do! ensure (bits = 8 || bits = 16 || bits = 32) "bad"
  return ()
}
