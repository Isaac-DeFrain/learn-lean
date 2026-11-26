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
