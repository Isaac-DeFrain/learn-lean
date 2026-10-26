/- 1. Getting to Know Lean -/

-- 1.1 Evaluating Expressions

-- 1.2 Types

-- 1.3 Functions and Definitions

def Natural : Type := Nat

/--
error: failed to synthesize instance of type class
  OfNat Natural 42
numerals are polymorphic in Lean, but the numeral `42` cannot be used in a context where the expected type is
  Natural
due to the absence of the instance above

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs (error) in
def fortyTwo : Natural := 42

-- can do
def fortyTwo' : Natural := (42 : Nat)

-- use `abbrev` instead
-- type class resolution works

abbrev N : Type := Nat
def fortyTwo'' : N := 42

-- unfoldable definitions are called _reducible_
-- definitions marked with `abbrev` are reducible

-- 1.4 Structures

structure Point (α : Type u) where
  point ::  -- constructor (default: mk)
  x : α
  y : α

def point : Point Nat := Point.point 0 1

example : point = ⟨0, 1⟩ := rfl
example : point = { x:= 0, y := 1 } := rfl

def Point.add (p q : Point α) [Add α] : Point α :=
  { x := p.x + q.x, y := p.y + q.y }

#check (Point.add)
-- Point.add : Point ?m.1 → Point ?m.1 → [Add ?m.1] → Point ?m.1

-- 1.5 Datatypes and Patterns

-- 1.6 Polymorphism

inductive Sign where
  | pos
  | neg

def posOrNeg (s : Sign) (n : Nat) :
    match s with | .pos => Nat | .neg => List Nat :=
  match s with
  | .pos => n
  | .neg => [n]

#check (posOrNeg .pos 42 : Nat)
#check (posOrNeg .neg 42 : List Nat)

-- 1.6.1 Linked Lists

-- 1.6.2 Implicit Arguments

-- 1.6.3 More Built-in Datatypes

-- 1.6.3.1 Option

-- Lean naming convention:
-- suffix ? returns an `Option`
-- suffix ! for a version that crashes when provided invalid input
-- suffix D returns a default value when it would otherwise fail

#check List.head?
-- List.head?.{u} {α : Type u} : List α → Option α

#check List.head!
-- List.head!.{u_1} {α : Type u_1} [Inhabited α] : List α → α

#check List.headD
-- List.headD.{u} {α : Type u} (as : List α) (fallback : α) : α

#eval [].head? (α := Int)
#eval ([] : List Int).head?

-- 1.6.3.2 Prod

namespace Hidden

structure Prod (α : Sort u) (β : Sort v) where
  fst : α
  snd : β

end Hidden

#check (· × ·)
-- fun x1 x2 => x1 × x2 : Type u_1 → Type u_2 → Type (max u_1 u_2)

example : (Nat × String × Int) = (Nat × (String × Int)) := rfl

-- 1.6.3.3 Sum

namespace Hidden

inductive Sum (α : Sort u) (β : Sort v) where
  | inl : α → Sum α β
  | inr : β → Sum α β

end Hidden

#check (· ⊕ ·)
-- fun x1 x2 => x1 ⊕ x2 : Type u_1 → Type u_2 → Type (max u_1 u_2)

-- 1.6.3.4 Unit

namespace Hidden

inductive Unit where
  | unit  -- ()

end Hidden

#check (() : Unit)

-- 1.6.3.5 Empty

namespace Hidden

inductive Empty -- no constructor => unreachable

end Hidden

-- can be used to eliminate pattern matching branches
#eval match (.inl 42 : Sum Nat Empty) with | .inl n => n

-- 1.6.3.6 Naming: Sums, Products, and Units

-- 1.6.4 Messages You May Meet

/--
error: Invalid universe level in constructor `MyType.ctor`: Parameter `α` has type
  Type
at universe level
  2
which is not less than or equal to the inductive type's resulting universe level
  1
-/
#guard_msgs (error) in
inductive MyType : Type where
  | ctor : (α : Type) → α → MyType

/--
error: (kernel) arg #1 of 'MyType.ctor' has a non positive occurrence of the datatypes being declared
-/
#guard_msgs (error) in
inductive MyType : Type where
  | ctor : (MyType → Int) → MyType


/--
error: fail to show termination for
  sameLengthPair
with errors
failed to infer structural recursion:
Not considering parameter α of sameLengthPair:
  it is unchanged in the recursive calls
Not considering parameter β of sameLengthPair:
  it is unchanged in the recursive calls
Cannot use parameter xs:
  failed to eliminate recursive application
    sameLengthPair xs' ys'
Cannot use parameter ys:
  failed to eliminate recursive application
    sameLengthPair xs' ys'


Could not find a decreasing measure.
The basic measures relate at each recursive call as follows:
(<, ≤, =: relation proved, ? all proofs failed, _: no proof attempted)
             xs ys
1) 197:28-50  ?  ?
Please use `termination_by` to specify a decreasing measure.
-/
#guard_msgs (error) in
def sameLengthPair (xs : List α) (ys : List β) : Bool :=
  match (xs, ys) with
  | ([], []) => true
  | (x :: xs', y :: ys') => sameLengthPair xs' ys'
  | _ => false

inductive Nums where
  | one
  | two
  | three

#eval Nums.one
-- Nums.one

/--
error: could not synthesize a `Repr` or `ToString` instance for type
  List Nums
-/
#guard_msgs (error) in
#eval ([.one, .two, .three] : List Nums)

inductive Firewood where
  | birch
  | pine
  | beech
deriving Repr

#eval ([.birch, .pine, .beech] : List Firewood)
-- [Firewood.birch, Firewood.pine, Firewood.beech]

-- 1.6.5 Exercises

-- 1.7 Characters, Strings, and Slices

-- strings are sequences of Unicode code points

#eval "Hello".push '!'
-- "Hello!"

-- 1.7.1 Slices

-- strings are represented by their UTF-8 encoding as an array of bytes with a cached character count

#check (String.Slice : Type)
#check (String.trimAscii : String → String.Slice)
#check (String.Slice.copy: String.Slice → String)

#eval (("small tortoiseshell".drop 6).dropEnd 5).copy
-- "tortoise"

-- 1.7.2 Matching

-- 1.7.3 Messages You May Meet

-- 1.8 Additional Conveniences

-- 1.8.1 Automatic Implicit Parameters

-- 1.8.2 Pattern-Matching Definitions

-- 1.8.3 Local Definitions

-- `let` vs. `let rec`

-- 1.8.4 Type Inference

-- 1.8.5 Simultaneous Matching

def sameLength (xs : List α) (ys : List β) : Bool :=
  match xs, ys with
  | [], [] => true
  | _ :: xs', _ :: ys' => sameLength xs' ys'
  | _, _ => false

-- 1.8.6 Natural Number Patterns

def halve : Nat → Nat
  | 0 | 1 => 0
  | n + 2 => halve n + 1

-- 1.8.7 Anonymous Functions

-- 1.8.8 Namespaces

-- 1.8.9 `if let`

inductive Inline : Type where
  | lineBreak
  | string : String → Inline
  | emph : Inline → Inline
  | strong : Inline → Inline

def Inline.string? (inline : Inline) : Option String :=
  if let Inline.string s := inline then
    some s
  else none

-- 1.8.10 Positional Structure Arguments

-- 1.8.11 String Interpolation

#eval s!"3 * 5 = {3 * 5}"
-- "3 * 5 = 15"
