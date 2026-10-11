/- 6. Interacting with Lean -/

-- 6.1 Messages

-- Errors are produced when an inconsistency prevents the code from being processed
-- e.g. syntax and type errors

-- Warnings describe potential problems with the code
-- e.g. the presence of sorry's

-- Information includes output from commands
-- e.g. #check and #eval

/--
error: Type mismatch
  "Not a number"
has type
  String
but is expected to have type
  Nat
-/
#guard_msgs(error) in
def x : Nat := "Not a number"

/--
error: Aborting evaluation since the expression depends on the 'sorry'
axiom, which can lead to runtime instability and crashes.

To attempt to evaluate anyway despite the risks, use the '#eval!'
command.
---
warning: declaration uses `sorry`
-/
#guard_msgs in
#eval (sorry : Nat)

-- 6.2 Importing Files

-- import Foo.Bar.Baz
-- imports the file Foo/Bar/Baz.olean

-- imports are transitive

-- 6.3 More on Sections

section
variable (x y : Nat)

def double := x + x

#check (double y : Nat)
#check double (2 * x)

attribute [local simp] Nat.add_assoc Nat.add_comm Nat.add_left_comm

theorem t1 : double (x + y) = double x + double y := by
  simp [double]

#check t1 y
#check t1 (2 * x)

theorem t2 : double (x * y) = double x * y := by
  simp [double, Nat.add_mul]

end

-- 6.4 More on Namespaces

namespace Foo
def bar : Nat := 1
end Foo

#check (Foo.bar : Nat)

-- equivalent to defining baz in Foo namespace
def Foo.baz : Nat := 42

-- _root_ is an explicit description of the empty prefix

def String.add (a b : String) := a ++ b

def Bool.add (a b : Bool) := a != b

def add (α β : Type) := Sum α β

section
open Bool
open String

#check (String.add : String → String → String)
#check (Bool.add : Bool → Bool → Bool)
#check (_root_.add : Type → Type → Type)

#eval add "hello " "world"
#eval add true false
#check (add Nat Nat : Type)
end

section
-- protected def
-- prevents the shorter alias from being created when the namespace is opened
-- used to prevent overloading of common names
protected def Foo.foo := 42

open Foo

/-- error: Unknown identifier `foo`-/
#guard_msgs in
#check foo
end

-- scoped opens

-- expose only listed names
section
open Nat (succ gcd) -- e.g. zero is not exposed

#check (succ : Nat → Nat)
#check (gcd : Nat → Nat → Nat)

/-- error: Unknown identifier `zero`-/
#guard_msgs in
#check zero
end

-- expose all but listed names
section
open Nat hiding succ gcd

#check (zero : Nat)

/-- error: Unknown identifier `gcd`-/
#guard_msgs in
#check gcd
end

-- open with aliases
section
open Nat renaming mul → times, add → plus

#eval (Nat.mul 2 3 = times 2 3)
#eval (Nat.add 2 3 = plus 2 3)

/-- error: Unknown identifier `mul`-/
#guard_msgs in
#check mul
end

-- 6.5 Attributes

def isPrefix (l₁ l₂ : List α) : Prop :=
  ∃ t, l₁ ++ t = l₂

section
@[local simp] theorem List.isPrefix_self (as : List α) : isPrefix as as :=
  ⟨ [], by simp ⟩

-- can also assign the attribute after the definition via
-- attribute [local simp] List.isPrefix_self

example : isPrefix [1, 2, 3] [1, 2, 3] := by
  simp
end

/-- error: `simp` made no progress -/
#guard_msgs in
example : isPrefix [1, 2, 3] [1, 2, 3] := by
  simp

-- local instance
section
local instance instLE : LE (List α) :=
  { le := isPrefix }

-- attribute [local instance] instLE

example (as : List α) : as ≤ as :=
  ⟨ [], by simp ⟩
end

/--
error: failed to synthesize instance of type class
  LE (List α)

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
example (as : List α) : as ≤ as :=
  ⟨[], by simp⟩

-- 6.6 More on Impicit Arguments

-- implicit arguments are inserted eagerly
variable (f : Nat → {_ : Nat} → Nat → Nat)

#check (f 1 : Nat → Nat)  -- f 1 is parsed as @f 1 _
#check (f 1 2 : Nat)

#check (@f 1 2 : Nat → Nat)
#check (@f 1 2 3 : Nat)

-- weaker annotation
variable (f : Nat → {{_ : Nat}} → Nat → Nat)

#check (f 1 : Nat → Nat → Nat)  -- f 1 is parsed as @f 1
#check (f 1 2 : Nat)            -- f 1 2 is parsed as @f 1 _ 2

#check (@f 1 2 : Nat → Nat)
#check (@f 1 2 3 : Nat)

-- example

def reflexive {α : Type u} (r : α → α → Prop) : Prop :=
  ∀ (a : α), r a a

def symmetric {α : Type u} (r : α → α → Prop) : Prop :=
  ∀ {{a b : α}}, r a b → r b a

def transitive {α : Type u} (r : α → α → Prop) : Prop :=
  ∀ {{a b c : α}}, r a b → r b c → r a c

def Euclidean {α : Type u} (r : α → α → Prop) : Prop :=
  ∀ {{a b c : α}}, r a b → r a c → r b c

-- reflexive, euclidean relation is symmetric
theorem th1 {α : Type u} {r : α → α → Prop}
    (reflr : reflexive r) (euclr : Euclidean r)
    : symmetric r :=
  fun {a b : α} =>
  fun (h : r a b) =>
  show r b a from euclr h (reflr _)

-- symmetric, euclidean relation is transitive
theorem th2 {α : Type u} {r : α → α → Prop}
    (symmr : symmetric r) (euclr : Euclidean r)
    : transitive r :=
  fun {a b c : α} =>
  fun (rab : r a b) (rbc : r b c) =>
  euclr (symmr rab) rbc

-- reflexive, euclidean relation is transitive
theorem th3 {α : Type u} {r : α → α → Prop}
    (reflr : reflexive r) (euclr : Euclidean r)
    : transitive r :=
 th2 (th1 reflr euclr) euclr

-- 6.7 Notation

-- 6.7.1 Notations and Precedence

section
local infixl:65   " + " => HAdd.hAdd  -- left-associative
local infix:50    " = " => Eq         -- non-associative
local infixr:80   " ^ " => HPow.hPow  -- right-associative
local prefix:100  "-"   => Neg.neg
local postfix:max "⁻¹"  => Inv.inv

-- above notations unfold to:
local notation:65 lhs:65 " + " rhs:66 => HAdd.hAdd lhs rhs
local notation:50 lhs:51 " = " rhs:51 => Eq lhs rhs
local notation:80 lhs:81 " ^ " rhs:80 => HPow.hPow lhs rhs
local notation:100 "-" arg:100 => Neg.neg arg
 -- `max` is a shorthand for precedence 1024:
local notation:1024 arg:1024 "⁻¹" => Inv.inv arg
end

section
local notation:65 a " + " b:66 " + " c:66 => a + b - c
#eval 1 + 2 + 3
end

-- 6.8 Coercions

#check (Int.ofNat : Nat → Int)

variable (m n : Nat)
variable (i j : Int)

#check (i + m : Int)
#check (i + m + j : Int)
#check (i + m + n : Int)

-- 6.9 Displaying Information

-- #check
-- #eval
-- #print

-- 6.10 Setting Options

-- set_option <name> <value>

section

set_option pp.notation false
#check 2 + 2 = 4
-- Eq (HAdd.hAdd 2 2) 4 : Prop

set_option pp.explicit true
#check 2 + 2 = 4
-- @Eq Nat
--   (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
--     (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
--   (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) : Prop

set_option pp.universes true
#check 2 + 2 = 4
-- @Eq.{1} Nat
--   (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
--     (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
--     (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
--   (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) : Prop

#reduce (fun x => x + 2) = (fun x => x + 3)
-- @Eq.{1} (Nat → Nat)
--   (fun x =>
--     @HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) x
--       (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
--   fun x =>
--   @HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) x
--     (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
end

-- 6.11 Using the Library

-- import is transitive, but opening namespaces is not

-- naming conventions

#check Nat.succ_ne_zero
#check Nat.zero_add
#check Nat.mul_one
#check Nat.le_of_succ_le_succ

-- inductive types

#check @Prod.mk   -- constructs a pair
#check @Prod.fst  -- project pair to first
#check @Prod.snd  -- project pair to second
#check @Prod.rec  -- provides a mechanism for defining functions on a pair by components

-- with propositions-as-types correspondence, logical connectives are inductive types

#check @And.intro
#check @And.casesOn
#check @And.left
#check @And.right
#check @Or.inl
#check @Or.inr
#check @Or.elim
#check @Exists.intro
#check @Exists.elim
#check @Eq.refl
#check @Eq.subst

-- 6.12 Auto Bound Implicit Arguments

-- using universe command
universe u v w
def compose {α : Type u} {β : Type v} {γ : Type w}
    (g : β → γ) (f : α → β) (x : α) : γ :=
  g (f x)

-- without universe command
def compose'.{u1, u2, u3}
    {α : Type u1} {β : Type u2} {γ : Type u3}
    (g : β → γ) (f : α → β) (x : α) : γ :=
  g (f x)

-- auto bound implicit arguments
def compose'' (g : β → γ) (f : α → β) (x : α) : γ :=
  g (f x)

#check @compose''
-- @compose'' : {β : Sort u_1} → {γ : Sort u_2} → {α : Sort u_3} → (β → γ) → (α → β) → α → γ

-- turn off via
-- set_option autoImplicit false

-- 6.13 Implicit Lambdas

variable (ρ : Type) (m : Type → Type) [Monad m]
instance : Monad (ReaderT ρ m) where
  pure := ReaderT.pure
  bind := ReaderT.bind

namespace Example
def id1 : {α : Type} → α → α :=
  fun x => x

def listId : List ({α : Type} → α → α) :=
  (fun x => x) :: []

-- implicit lambda introduction has been disabled because we use `@fun`
def id2 : {α : Type} → α → α :=
  @fun α (x : α) => x

def id3 : {α : Type} → α → α :=
  @fun _ x => x

-- implicit lambda introduction has been disabled because we used the binder annotation `{...}`
def id5 : {α : Type} → α → α :=
  fun {_} x => x
end Example

-- 6.14. Sugar for Simple Functions

#check (· + 1)
-- fun x => x + 1 : Nat → Nat

#check (2 - ·)
-- fun x => 2 - x : Nat → Nat

#eval [1, 2, 3, 4, 5].foldl (· * ·) 1
-- 120

def f' (x y z : Nat) := x + y + z
#check (f' · 1 ·)
-- fun x1 x2 => f' x1 1 x2 : Nat → Nat → Nat

#eval [(1, 2), (3, 4), (5, 6)].map (·.1)
-- [1, 3, 5]

#check (Prod.mk · (· + 1))
-- fun x => (x, fun x => x + 1) : ?m.1 → ?m.1 × (Nat → Nat)

-- 6.15 Named Arguments

#eval [1, 2, 3, 4].foldl (init := 0) (· + ·)

example {a b : Nat} {p : Nat → Nat → Nat → Prop}
    (h₁ : p a b b) (h₂ : b = a)
    : p a a b :=
  Eq.subst (motive := (p a · b)) h₂ h₁

-- interactions between named and default arguments

def f'' (x : Nat) (y : Nat := 1) (w : Nat := 2) (z : Nat) :=
  x + y + w - z

example (x z : Nat) : f'' (z := z) x = x + 1 + 2 - z := rfl

example (x z : Nat) : f'' x (z := z) = x + 1 + 2 - z := rfl

example (x y : Nat) : f'' x y = fun z => x + y + 2 - z := rfl

example : f'' = (fun x z => x + 1 + 2 - z) := rfl

example (x : Nat) : f'' x = fun z => x + 1 + 2 - z := rfl

example : f'' (y := 5) = fun x z => x + 5 + 2 - z := rfl

def g {α} [Add α] (a : α) (b? : Option α := none) (c : α) : α :=
  match b? with
  | none   => a + c
  | some b => a + b + c

variable {α} [Add α]

example : g = fun (a c : α) => a + c := rfl

example (x : α) : g (c := x) = fun (a : α) => a + x := rfl

example (x : α) : g (b? := some x) = fun (a c : α) => a + x + c := rfl

example (x : α) : g x = fun (c : α) => x + c := rfl

example (x y : α) : g x y = fun (c : α) => x + y + c := rfl

-- use .. to fill missing explicit args with _

inductive Term where
  | var    (name : String)
  | num    (val : Nat)
  | app    (fn : Term) (arg : Term)
  | lambda (name : String) (type : Term) (body : Term)

def getBinderName : Term → Option String
  | Term.lambda (name := n) .. => some n
  | _ => none

def getBinderType : Term → Option Term
  | Term.lambda (type := t) .. => some t
  | _ => none

example (f : Nat → Nat) (a b c : Nat) : f (a + b + c) = f (a + (b + c)) :=
  congrArg f (Nat.add_assoc ..)
