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
  | bool | int | string | date
deriving Repr

structure Date where
  day : Nat
  month : Nat
  year : Nat
deriving BEq

abbrev DBType.asType : DBType → Type
  | .bool => Bool
  | .int => Int
  | .string => String
  | .date => Date

#check ("abc" : DBType.string.asType)

-- nullable
structure NDBType where
  underlying : DBType
  nullable : Bool

abbrev NDBType.asType (t : NDBType) : Type :=
  match t.nullable with
  | true => Option t.underlying.asType
  | false => t.underlying.asType

def DBType.beq (t : DBType) (x y : t.asType) : Bool :=
  match t with
  | .bool => x == y
  | .int => x == y
  | .string => x == y
  | .date => x == y

def NDBType.beq (t : NDBType) (x y : t.asType) : Bool :=
  match t with
  | ⟨.bool, true⟩ => x == y
  | ⟨.bool, false⟩ => x == y
  | ⟨.int, true⟩ => x == y
  | ⟨.int, false⟩ => x == y
  | ⟨.string, true⟩ => x == y
  | ⟨.string, false⟩ => x == y
  | ⟨.date, true⟩ => x == y
  | ⟨.date, false⟩ => x == y

instance {t : DBType} : BEq t.asType where
  beq := t.beq

instance {t : NDBType} : BEq t.asType where
  beq := t.beq

-- coerce `DBType` to non-nullable `NDBType`
instance : Coe DBType NDBType where
  coe t := ⟨t, false⟩

-- distinct from the instance on the codes

instance : BEq DBType where
  beq
    | .int, .int => true
    | .string, .string => true
    | .bool, .bool => true
    | .date, .date => true
    | _, _ => false

instance : Repr Date where
  reprPrec d _ := s!"{d.year}/{d.month}/{d.day}"

instance {t : DBType} : Repr t.asType where
  reprPrec :=
    match t with
    | .bool => reprPrec
    | .int => reprPrec
    | .string => reprPrec
    | .date => reprPrec

-- ### 7.3.2 Schemas and Tables

structure Column where
  name : String
  contains : NDBType

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
  ⟨"name", ⟨.string, false⟩⟩,
  ⟨"location", ⟨.string, false⟩⟩,
  ⟨"elevation", ⟨.int, false⟩⟩,
  ⟨"lastVisited", ⟨.int, false⟩⟩
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

inductive HasCol : Schema → String → NDBType → Type where
  | here : HasCol (⟨n, t⟩ :: _) n t
  | there : HasCol s n t → HasCol (_ :: s) n t

-- "elevation" is the third column of `peak`
open DBType in
example : HasCol peak "elevation" int := .there <| .there .here

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

open DBType in
abbrev travelDiary : Schema :=
  [⟨"name", string⟩, ⟨"location", string⟩, ⟨"lastVisited", int⟩]

example : Subschema travelDiary peak :=
  let name := .here                                 -- first column
  let location := .there .here                      -- second column
  let lastVisited := .there (.there (.there .here)) -- third column
  .cons name
    <| .cons location
    <| .cons lastVisited .nil

example : Subschema travelDiary peak := by repeat constructor

-- four constructors
example : Subschema [⟨"location", DBType.string⟩] peak := .cons (.there .here) .nil

example : Subschema [⟨"name", DBType.string⟩] peak := by repeat constructor
example : Subschema [⟨"location", DBType.string⟩] peak := by repeat constructor
example : Subschema [⟨"elevation", DBType.int⟩] peak := by repeat constructor
example : Subschema [⟨"lastVisited", DBType.int⟩] peak := by repeat constructor

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

-- ### 7.3.3 Conditions and Selection

-- projection removes unwanted columns from a table
-- queries must also be able to remove unwanted rows - _selection_

-- all subexpressions refer to the same schema so this is a parameter

open DBType in
inductive DBExpr (s : Schema) : NDBType → Type where
  | col (n : String) (loc : HasCol s n t) : DBExpr s t  -- reference to a column
  | eq (e1 e2 : DBExpr s t) : DBExpr s bool             -- compares e1, e2 for equality
  | lt (e1 e2 : DBExpr s int) : DBExpr s bool               -- less than
  | and (e1 e2 : DBExpr s bool) : DBExpr s bool             -- conjunction
  | const : t.asType → DBExpr s t                       -- constant value
  | before (e1 e2 : DBExpr s date) : DBExpr s bool

macro "col!" n:term : term => `(DBExpr.col $n (by repeat constructor))

open DBType in
def tallInDenmark : DBExpr peak bool :=
  let tall := .lt (.const 1000) (col! "elevation")
  let inDenmark := .eq (col! "location") (.const "Denmark")
  .and tall inDenmark

def Date.before : Date → Date → Bool
  | ⟨day1, month1, year1⟩, ⟨day2, month2, year2⟩ =>
    if year1 < year2 then true
    else if month1 < month2 then true
    else day1 < day2

def DBExpr.evaluate (row : Row s) : DBExpr s t → t.asType
  | .col _ loc => row.get loc
  | .eq e1 e2 => evaluate row e1 == evaluate row e2
  | .lt e1 e2 => evaluate row e1 < evaluate row e2
  | .and e1 e2 => evaluate row e1 && evaluate row e2
  | .const v => v
  | .before e1 e2 => (evaluate row e1).before (evaluate row e2)

/-- info: false -/
#guard_msgs in
#eval tallInDenmark.evaluate ("Valby Bakke", "Denmark", 31, 2023)

/-- info: true -/
#guard_msgs in
#eval tallInDenmark.evaluate ("Fictional mountain", "Denmark", 1230, 2023)

/-- info: false -/
#guard_msgs in
#eval tallInDenmark.evaluate ("Mount Borah", "USA", 3859, 1996)

-- ### 7.3.4 Queries

-- based on relational algebra

-- 1. The union of two expressions that have the same schema combines the rows that result
--    from two queries
-- 2. The difference of two expressions that have the same schema removes rows found in the
--    second result from the rows in the first result
-- 3. Selection by some criterion filters the result of a query according to an expression
-- 4. Projection into a subschema, removing columns from the result of a query
-- 5. Cartesian product, combining every row from one query with every row from another
-- 6. Renaming a column in the result of a query, which modifies its schema
-- 7. Prefixing all columns in a query with a name

-- queries are represented by an indexed family

def disjoint [BEq α] (xs ys : List α) : Bool :=
  !xs.any ys.contains && !ys.any xs.contains

def Schema.columnNames (s : Schema) : List String :=
  s.map Column.name

def Schema.renameColumn : (s : Schema) → HasCol s n t → String → Schema
  | c :: cs, .here, n' => {c with name := n'} :: cs
  | c :: cs, .there next, n' => c :: renameColumn cs next n'

def Column.prefix (pre : String) (c : Column) : Column :=
  {c with name := pre ++ "." ++ c.name}

open DBType in
inductive Query : Schema → Type where
  | table : Table s → Query s
  | union : Query s → Query s → Query s
  | diff : Query s → Query s → Query s
  | select : Query s → DBExpr s bool → Query s
  | project : Query s → (s' : Schema) → Subschema s' s → Query s'
  | product :
    Query s1 → Query s2 →
    disjoint s1.columnNames s2.columnNames →
    Query (s1 ++ s2)
  | renameColumn :
    Query s → (c : HasCol s n t) → (n' : String) →
    !(s.columnNames.contains n') →
    Query (s.renameColumn c n')
  | prefixWith : (n : String) → Query s → Query (s.map <| .prefix n)

-- use of an expression of type `Bool` where a type is expected triggers a coercion from
-- `Bool` to `Prop`

-- ### 7.3.5 Executing Queries

-- the result of a query is a table
-- this means that each operation in the query language requires a corresponding implementation
-- that works with tables

-- #### 7.3.5.1 Cartesian Product

def addVal (v : c.contains.asType) (row : Row s) : Row (c :: s) :=
  match s, row with
  | [], () => v
  | _::_, v' => (v, v')

def Row.append (r1 : Row s1) (r2 : Row s2) : Row (s1 ++ s2) :=
  match s1, r1 with
  | [], () => r2
  | [_], v => addVal v r2
  | _::_::_, (v, r') => (v, r'.append r2)

def Table.cartesianProduct (t1 : Table s1) (t2 : Table s2) : Table (s1 ++ s2) :=
  t1.flatMap fun r => t2.map r.append

-- #### 7.3.5.2 Difference

def List.without [BEq α] (source exclude : List α) : List α :=
  source.filter fun a => !(exclude.contains a)

-- #### 7.3.5.3 Renaming Columns

def Row.rename (c : HasCol s n t) (row : Row s) : Row (s.renameColumn c n') :=
  match s, row, c with
  | [_], r, .here => r
  | _::_::_, r, .here => r
  | _::_::_, (v, r), .there next => addVal v (r.rename next)

-- while this funciton changes the type of its argument, the actual return value contains the
-- same data as the original argument

-- from a runtime perspective, `Row.rename` is just a slow identity function

-- #### 7.3.5.4 Prefixing Column Names

def prefixRow (row : Row s) : Row (s.map <| Column.prefix pre) :=
  match s, row with
  | [], _ => ()
  | [_], v => v
  | _::_::_, (v, r) => (v, prefixRow r)

-- #### 7.3.5.5 Putting the Pieces Together

def Query.exec : Query s → Table s
  | .table t => t
  | .union q1 q2 => exec q1 ++ exec q2
  | .diff q1 q2 => (exec q1).without (exec q2)
  | .select q e => (exec q).filter e.evaluate
  | .project q _ sub => (exec q).map (·.project _ sub)
  | .product q1 q2 _ => (exec q1).cartesianProduct (exec q2)
  | .renameColumn q c _ _ => (exec q).map (·.rename c)
  | .prefixWith _ q => (exec q).map prefixRow

-- heights of mountains peaks with elevation greater than 500m

open Query DBType in
def example1 :=
  table mountainDiary |>.select
  (.lt (.const 500) (col! "elevation")) |>.project
  [⟨"elevation", int⟩] (by repeat constructor)

/-- info: [3637, 1519, 2549] -/
#guard_msgs in
#eval example1.exec

-- to plan a sightseeing tour, we may want to match all pairs of peaks and waterfalls in the
-- same location

open DBType in
abbrev waterfall : Schema := [
  ⟨"name", string⟩,
  ⟨"location", string⟩,
  ⟨"lastVisited", int⟩
]

def waterfallDiary : Table waterfall := [
  ("Multnomah Falls", "USA", 2018),
  ("Shoshone Falls",  "USA", 2014)
]

open Query DBType in
def example2 :=
  let mountains := table mountainDiary |>.prefixWith "m"
  let waterfalls := table waterfallDiary |>.prefixWith "w"
  let final := [⟨"m.name", string⟩, ⟨"w.name", string⟩]
  mountains.product waterfalls (by decide)
  |>.select (.eq (col! "m.location") (col! "w.location"))
  |>.project final (by repeat constructor)

/-- info:
[("Mount Nebo", "Multnomah Falls"),
 ("Mount Nebo", "Shoshone Falls"),
 ("Moscow Mountain", "Multnomah Falls"),
 ("Moscow Mountain", "Shoshone Falls"),
 ("Mount St. Helens", "Multnomah Falls"),
 ("Mount St. Helens", "Shoshone Falls")]
-/
#guard_msgs in
#eval example2.exec

-- #### 7.3.5.6 Errors You May Meet

-- ### 7.3.6 Exercises

-- #### 7.3.6.1 Dates
-- Define a structure to represent dates. Add it to the `DBType` universe and update the rest
-- of the code accordingly. Provide the extra `DBExpr` constructors that seem to be necessary.

-- see above

-- #### 7.3.6.2 Nullable Types
-- Add support for nullable columns to the query language by representing database types with
-- `NDBType`

-- Use this type in place of `DBType` in `Column` and `DBExpr`, and look up SQL's rules for
-- NULL and comparison operators to determine the types of `DBExpr`'s constructors.

-- see above

-- #### 7.3.6.3. Experimenting with Tactics
-- What is the result of asking Lean to find values of the following types using
-- `by repeat constructor`? Explain why each gives the result that it does.

-- `0` is a constructor
example : Nat := by constructor
example : Nat := 0

-- `[]` is a constructor
example : List α := by constructor
example : List α := []

-- `.cons 0 <| .cons 0 <| .cons 0 <| .cons 0 .nil` is a collection of constructors
example : Vect Nat 4 := by repeat constructor
example : Vect Nat 4 := .cons 0 <| .cons 0 <| .cons 0 <| .cons 0 .nil

-- `()` is a constructor
example : Row [] := by constructor
example : Row [] := ()

-- `0` is a constructor
example : Row [⟨"price", DBType.int⟩] := by repeat constructor
example : Row [⟨"price", DBType.int⟩] := 0

-- `String` does not have a constructor
/-- error: failed to compile definition, consider marking it as 'noncomputable' because it depends on 'List.utf8Encode', which is 'noncomputable' -/
#guard_msgs in
example : Row peak := by repeat constructor
example : Row peak := ("", "", 0, 0)

-- `.here` is a constructor
example : HasCol [⟨"price", DBType.int⟩, ⟨"price", DBType.int⟩] "price" DBType.int := by constructor
example : HasCol [⟨"price", DBType.int⟩, ⟨"price", DBType.int⟩] "price" DBType.int := .here
