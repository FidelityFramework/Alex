module Alex.XParsec.PSGCombinators

let ensure (condition: bool) (message: string) = if condition then () else failwith message
