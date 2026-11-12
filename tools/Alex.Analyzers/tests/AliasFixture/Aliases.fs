namespace AliasFixture

type Foreign = System.Text.StringBuilder
type ObjectAlias = obj
type ObjectNominal = System.Object
type Chain = Foreign
type Builders = System.Text.StringBuilder list
type Handler = string -> obj
type Pair = int * obj
type Both = System.Text.StringBuilder * obj
type Boxed<'T> = 'T * obj
type Arr = System.Text.StringBuilder[]
type Text = string
type Names = string list
type Lookup = Map<string, int>
type Function = int -> int
type PurePair = int * string
type Optional = int option
type Generic<'T> = 'T list
type NestedObj = Generic<obj>
type NestedForeign = Generic<System.Text.StringBuilder>
type Anonymous = {| Name: string; Value: int |}
type AnonymousObj = {| Value: obj |}
[<Measure>]
type m
type Distance = float<m>
type Ints = int[]
type UnitFunction = unit -> unit
type Nat = nativeint
type Resizable = ResizeArray<int>
type LazyValue = Lazy<int>
type Sequence = seq<int>
type Local = { Value: int }
type LocalAlias = Local
type ExceptionType = exn
type BigInteger = bigint
type DecimalValue = decimal
