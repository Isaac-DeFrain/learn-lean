-- # 7 Programming with Dependent Types

-- _dependent types_ are types that contain non-type expressions

def natOrStringThree (b : Bool) : if b then Nat else String :=
  match b with
  | true => (3 : Nat)
  | false => "three"

-- ## 7.1 Indexed Families

inductive Vect (α : Type u) : Nat → Type u where
  | nil : Vect α 0
  | cons : α → Vect α n → Vect α (n + 1)

-- `α` is a parameter - fixed
-- `n` is an index - varies

def List.toVect : (l : List α) → Vect α l.length
  | [] => .nil
  | x :: xs => .cons x <| toVect xs

def Vect.toList : Vect α n → List α
  | .nil => []
  | .cons x xs => x :: toList xs

def Vect.print [ToString α] : Vect α n → String → String
  | .nil, _ => ""
  | .cons x .nil, _ => ToString.toString x
  | .cons x xs, sep =>
    ToString.toString x |>.append sep |>.append <| print xs sep

example : Vect String 2 := .cons "hello" <| .cons "world" .nil

/-- info: "hello world" -/
#guard_msgs in
#eval ["hello", "world"].toVect.print " "

def Vect.replicate (n : Nat) (x : α) : Vect α n :=
  match n with
  | 0 => .nil
  | n + 1 => .cons x <| replicate n x

-- require `zip` to take vectors of the same length

def Vect.zip : Vect α n → Vect β n → Vect (α × β) n
  | .nil, _ => .nil
  | .cons x xs, .cons y ys => .cons (x, y) <| zip xs ys

-- do not need to pattern match on `.cons _ _, .nil`

-- Getting a feel for programming with dependent types requires experience, and the exercises
-- in this section are very important. For each exercise, try to see which mistakes the type
-- checker can catch, and which ones it can't, by experimenting with the code as you go. This
-- is also a good way to develop a feel for the error messages.

-- - Double-check that `Vect.zip` gives the right answer when combining the three highest peaks
--   in Oregon with the three highest peaks in Denmark. Because `Vect` doesn't have the
--   syntactic sugar that `List` has, it can be helpful to begin by defining
--   `oregonianPeaks : Vect String 3` and `danishPeaks : Vect String 3`.

/-- info: [("a", 0), ("b", 1), ("c", 2)] -/
#guard_msgs in
#eval Vect.zip ["a", "b", "c"].toVect [0, 1, (2 : Nat)].toVect |>.toList

-- - Define a function `Vect.map` with type `(α → β) → Vect α n → Vect β n`.

def Vect.map : (α → β) → Vect α n → Vect β n
  | _, .nil => .nil
  | f, .cons x xs => .cons (f x) <| map f xs

-- - Define a function `Vect.zipWith` that combines the entries in a `Vect` one at a time with
--   a function. It should have the type `(α → β → γ) → Vect α n → Vect β n → Vect γ n`.

def Vect.zipWith : (α → β → γ) → Vect α n → Vect β n → Vect γ n
  | _, .nil, _ => .nil
  | f, .cons x xs, .cons y ys => .cons (f x y) <| zipWith f xs ys

-- - Define a function `Vect.unzip` that splits a `Vect` of pairs into a pair of `Vect`s. It
--   should have the type `Vect (α × β) n → Vect α n × Vect β n`.

def Vect.unzip : Vect (α × β) n → Vect α n × Vect β n
  | .nil => (.nil, .nil)
  | .cons (x, y) xys =>
    let (xs, ys) := unzip xys
    (.cons x xs, .cons y ys)

-- - Define a function `Vect.push` that adds an entry to the end of a `Vect`. Its type should
--   be `Vect α n → α → Vect α (n + 1)` and `#eval Vect.push (.cons "snowy" .nil) "peaks"`
--   should yield `Vect.cons "snowy" (Vect.cons "peaks" (Vect.nil))`.

def Vect.push : Vect α n → α → Vect α (n + 1)
  | .nil, y => .cons y .nil
  | .cons x xs, y => .cons x <| push xs y

/-- info: Vect.cons "snowy" (Vect.cons "peaks" (Vect.nil)) -/
#guard_msgs in
#eval Vect.push (.cons "snowy" .nil) "peaks"

-- - Define a function `Vect.reverse` that reverses the order of a `Vect`.

def Vect.reverse : Vect α n → Vect α n
  | .nil => .nil
  | .cons x xs => xs.reverse.push x

/-- info: Vect.cons "peaks" (Vect.cons "snowy" (Vect.nil)) -/
#guard_msgs in
#eval Vect.cons "snowy" (Vect.cons "peaks" (Vect.nil)) |>.reverse

-- - Define a function `Vect.drop` with the following type:
--   `(n : Nat) → Vect α (k + n) → Vect α k`. Verify that it works by checking that
--   `#eval danishPeaks.drop 2 yields Vect.cons "Ejer Bavnehøj" (Vect.nil)`.

def Vect.drop : (n : Nat) → Vect α (k + n) → Vect α k
  | 0, xs => xs
  | n + 1, .cons _ xs => xs.drop n

/-- info: Vect.nil -/
#guard_msgs in
#eval Vect.push (.cons "a" .nil) "b" |>.drop 2

-- - Define a function `Vect.take` with type `(n : Nat) → Vect α (k + n) → Vect α n` that
--   returns the first n entries in the Vect. Check that it works on an example.

def Vect.take : (n : Nat) → Vect α (k + n) → Vect α n
  | 0, _ => .nil
  | n + 1, .cons x xs => .cons x <| take n xs

/-- info: Vect.cons "a" (Vect.nil) -/
#guard_msgs in
#eval Vect.push (.cons "a" .nil) "b" |>.take 1

-- ## 7.2 The Universe Design Pattern

-- Russell-style universe - `Sort u` directly describe other types

-- Tarski-style universe - represent types as data and include an explicit function to interpret

inductive NatOrBool where
  | nat | bool  -- codes

abbrev NatOrBool.asType : NatOrBool → Type
  | nat => Nat
  | bool => Bool

def decode : (t : NatOrBool) → String → Option t.asType
  | .nat, input => input.toNat?
  | .bool, "true" => some true
  | .bool, "false" => some false
  | _, _ => none

-- codes can be recursive

inductive NestedPairs where
  | nat : NestedPairs
  | pair : NestedPairs → NestedPairs → NestedPairs

abbrev NestedPairs.asType : NestedPairs → Type
  | .nat => Nat
  | .pair t1 t2 => t1.asType × t2.asType

def NestedPairs.beq (t : NestedPairs) (x y : t.asType) : Bool :=
  match t with
  | .nat => x == y
  | .pair t1 t2 => beq t1 x.fst y.fst && beq t2 x.snd y.snd

instance {t : NestedPairs} : BEq t.asType where
  beq := t.beq

-- ### 7.2.1 Type Classes vs Universes

-- type classes allow an open-ended collection of types to be used with an API

-- universes a la Tarski restrict the API to be usable with only predetermined types

-- ### 7.2.2 A Universe of Finite Types

-- one way to represent finite types is by a universe:

inductive Finite where
  | empty : Finite
  | unit : Finite
  | bool : Finite
  | opt : Finite → Finite
  | pair : Finite → Finite → Finite
  | arr : Finite → Finite → Finite
deriving Repr

abbrev Finite.asType : Finite → Type
  | .empty => Empty
  | .unit => Unit
  | .bool => Bool
  | .opt t => Option t.asType
  | .pair t1 t2 => t1.asType × t2.asType
  | .arr dom cod => dom.asType → cod.asType

def List.product : List α → List β → List (α × β) :=
  let rec prod : List α → List β → List (α × β)
    | [], _ => []
    | x :: xs, ys => ys.map (x, ·) |>.append <| prod xs ys
  prod

/-- info: [(0, 'a'), (0, 'b'), (1, 'a'), (1, 'b'), (2, 'a'), (2, 'b')] -/
#guard_msgs in
#eval [0, 1, 2].product ['a', 'b']

mutual
def Finite.enumerate : (t : Finite) → List t.asType
  | .empty => []
  | .unit => [()]
  | .bool => [true, false]
  | .opt t => t.enumerate.map some |>.concat none
  | .pair t1 t2 => t1.enumerate.product t2.enumerate
  | .arr dom cod => dom.functions cod.enumerate

def Finite.functions : (t : Finite) → List α → List (t.asType → α)
  | .empty, _ => []
  | .unit, res => res.map fun r _ => r
  | .bool, res =>
    res.product res |>.map fun (r1, r2) => fun
      | true => r1
      | false => r2
  | .opt t, res =>
    t.functions res |>.product res |>.map fun (f, r) => fun
      | none => r
      | some x => f x
  | .pair t1 t2, res =>
    let fs := t1.functions <| t2.functions res
    fs.map fun f (x, y) => f x y
  | .arr t1 t2, res =>
    let args := t1.enumerate
    let base := res.map fun r _ => r
    args.foldr (fun arg rest =>
      (t2.functions rest).map fun more =>
        fun f => more (f arg) f)
      base
end

/-- info: 4 -/
#guard_msgs in
#eval Finite.bool.functions Finite.bool.enumerate |>.length

def Finite.beq (t : Finite) (x y : t.asType) : Bool :=
  match t with
  | .empty | .unit => true
  | .bool => x == y
  | .opt t =>
    match x, y with
    | none, none => true
    | some x, some y => t.beq x y
    | _, _ => false
  | .pair t1 t2 => t1.beq x.fst y.fst && t2.beq x.snd y.snd
  | .arr dom cod =>
    dom.enumerate.all fun arg => cod.beq (x arg) (y arg)

-- ### 7.2.3 Exercises

-- - Write a function that converts any value from a type coded for by `Finite` into a string.
--   Functions should be represented as their tables.

def Finite.toString (t : Finite) (x : t.asType) : String :=
  match t with
  | .empty => ""
  | .unit => "()"
  | .bool => ToString.toString x
  | .opt t =>
    match x with
    | none => "none"
    | some x => t.toString x
  | .pair t1 t2 => s!"({t1.toString x.fst}, {t2.toString x.snd})"
  | .arr t1 t2 =>
    t1.enumerate.map (fun t => s!"{t1.toString t} ↦ {t2.toString (x t)}\n")
    |>.foldr (· ++ ·) ""

/-- info: "true ↦ true\nfalse ↦ false\n" -/
#guard_msgs in
#eval Finite.arr .bool .bool |>.toString fun
  | true => true
  | false => false

instance {t : Finite} : ToString t.asType where
  toString := t.toString

-- - Add the empty type `Empty` to `Finite` and `Finite.beq`.

-- see above

instance {t : Finite} : BEq t.asType where
  beq := t.beq

/-- info: Finite.empty.beq : Finite.empty.asType → Finite.empty.asType → Bool -/
#guard_msgs in
#check (Finite.empty.beq : Empty → Empty → Bool)

-- - Add `Option` to `Finite` and `Finite.beq`.

-- see above

/-- info: true -/
#guard_msgs in
#eval Finite.opt Finite.bool |>.beq (some false) (some false)

-- ## 7.3 Worked Example: Typed Queries

-- ### 7.3.1 A Universe of Data

inductive DBType where
  | bool | int | string
deriving Repr

abbrev DBType.asType : DBType → Type
  | .bool => Bool
  | .int => Int
  | .string => String

#check ("abc" : DBType.string.asType)

def DBType.beq (t : DBType) (x y : t.asType) : Bool :=
  match t with
  | .bool => x == y
  | .int => x == y
  | .string => x == y

instance {t : DBType} : BEq t.asType where
  beq := t.beq

-- distinct from the instance on the codes

instance : BEq DBType where
  beq
    | .int, .int => true
    | .string, .string => true
    | .bool, .bool => true
    | _, _ => false

instance {t : DBType} : Repr t.asType where
  reprPrec :=
    match t with
    | .bool => reprPrec
    | .int => reprPrec
    | .string => reprPrec

-- ### 7.3.2 Schemas and Tables

structure Column where
  name : String
  contains : DBType

abbrev Schema := List Column

-- schema can be seen as a universe that describes rows in a table

abbrev Row : Schema → Type
  | [] => Unit
  | [col] => col.contains.asType
  | col :: cols => col.contains.asType × Row cols

-- a table is a list of rows that share a schema

abbrev Table (s : Schema) := List <| Row s

-- e.g. a diary of mountain peaks

abbrev peak : Schema := [
  ⟨"name", .string⟩,
  ⟨"location", .string⟩,
  ⟨"elevation", .int⟩,
  ⟨"lastVisited", .int⟩
]

def mountainDiary : Table peak := [
  ("Mount Nebo",       "USA",     3637, 2013),
  ("Moscow Mountain",  "USA",     1519, 2015),
  ("Himmelbjerget",    "Denmark",  147, 2004),
  ("Mount St. Helens", "USA",     2549, 2010)
]

-- #### 7.3.2.1 Recursion and Universes, Revisited

-- the convenience of structuring rows as tuples comes at a cost

/--
error: Type mismatch
  (v1, r1')
has type
  ?m.12 × ?m.13
but is expected to have type
  Row (head✝ :: tail✝)
-/
#guard_msgs in
def Row.beq' (r1 r2 : Row s) : Bool :=
  match s with
  | [] => true
  | _::_ =>
    match r1, r2 with
    | (v1, r1'), (v2, r2') =>
      v1 == v2 && bEq r1' r2'

-- need to refine the type of rows further

def Row.beq (r1 r2 : Row s) : Bool :=
  match s with
  | [] => true
  | [_] => r1 == r2
  | _::_::_ =>
    match r1, r2 with
    | (v1, r1'), (v2, r2') =>
      v1 == v2 && r1'.beq r2'

instance : BEq (Row s) where
  beq := Row.beq

-- Unlike in other contexts, functions that occur in types cannot be considered only in terms
-- of their input/output behavior. Programs that use these types will find themselves forced
-- to mirror the algorithm used in the type-level function so that their structure matches the
-- pattern-matching and recursive behavior of the type. A big part of the skill of programming
-- with dependent types is the selection of appropriate type-level functions with the right
-- computational behavior.

-- #### 7.3.2.2 Column Pointers

-- some queries only make sense if a schema contains a particular column

-- schema can contain a column either at the beginning or later

inductive HasCol : Schema → String → DBType → Type where
  | here : HasCol (⟨n, t⟩ :: _) n t
  | there : HasCol s n t → HasCol (_ :: s) n t

-- "elevation" is the third column of `peak`
example : HasCol peak "elevation" .int := .there <| .there .here

-- gets the value in a specific column in a specific row
def Row.get (row : Row s) (col : HasCol s n t) : t.asType :=
  match s, col, row with
  | [_], .here, v => v
  | _::_::_, .here, (v, _) => v
  | _::_::_, .there next, (_, r) => r.get next

-- `HasCol s n t` guarantees the column exists in the schema so we don't return an `Option`

-- `HasCol` plays two roles:
-- 1. It serves as _evidence_ that a column with a particular name and type exists in a schema.
-- 2. It serves as _data_ that can be used to find the value associated with the column in a row.

-- #### 7.3.2.3 Subschemas

-- _project_ a table or row into a smaller schema, i.e. a subschema
-- every column in a subschema must be present in the larger schema

-- the ways in which a schema can be a subschema of another can be defined as an indexed family

-- `nil` - empty schema is a subschema of every schema
-- `cons` - if the smaller schema has a column, then that column must be in the larger schema and
-- all the rest of the columns in the subschema must also be a subschema of the larger one

inductive Subschema : Schema → Schema → Type where
  | nil : Subschema [] super
  | cons :
      HasCol super n t →
      Subschema sub super →
      Subschema (⟨n, t⟩ :: sub) super -- it makes sense to read this function type backwards

-- `Subschema` assigns each column in the subschema a pointer to its location in the larger one

example : Subschema [] peak := .nil
example : Subschema [] peak := by constructor

abbrev travelDiary : Schema :=
  [⟨"name", .string⟩, ⟨"location", .string⟩, ⟨"lastVisited", .int⟩]

example : Subschema travelDiary peak :=
  let name := .here                                 -- first column
  let location := .there .here                      -- second column
  let lastVisited := .there (.there (.there .here)) -- third column
  .cons name
    <| .cons location
    <| .cons lastVisited .nil

example : Subschema travelDiary peak := by repeat constructor

-- four constructors
example : Subschema [⟨"location", .string⟩] peak := .cons (.there .here) .nil

example : Subschema [⟨"name", .string⟩] peak := by repeat constructor
example : Subschema [⟨"location", .string⟩] peak := by repeat constructor
example : Subschema [⟨"elevation", .int⟩] peak := by repeat constructor
example : Subschema [⟨"lastVisited", .int⟩] peak := by repeat constructor

-- adding a column to the larger schema does not change a subschema

def Subschema.addColumn :
    Subschema sub super →
    Subschema sub (c :: super)
  | .nil => .nil
  | .cons col sub' => .cons (.there col) sub'.addColumn

-- a subschema describes where to find each column of the smaller schema in the larger one

-- `Subschema` defines a (relfexive, transitive) relation between schemas

def Subschema.reflexive : (s : Schema) → Subschema s s
  | [] => .nil
  | _ :: cs => .cons .here (reflexive cs).addColumn

def Subschema.hasCol : Subschema sub super → HasCol sub n t → HasCol super n t
  | .cons col _, .here => col
  | .cons _ sub', .there col' => sub'.hasCol col'

def Subschema.transitive : Subschema s t → Subschema t u → Subschema s u
  | .nil, _ => .nil
  | .cons col sub, sub' => .cons (sub'.hasCol col) (sub.transitive sub')

-- #### 7.3.2.4 Projecting Rows

-- given that `sub` is a subschema of `super`, a row in `super` can be projected to a row in `sub`

def Row.project (row : Row super) : (sub : Schema) → Subschema sub super → Row sub
  | [], .nil => ()
  | [_], .cons c .nil => row.get c
  | _::_::_, .cons c cs => (row.get c, row.project _ cs)
