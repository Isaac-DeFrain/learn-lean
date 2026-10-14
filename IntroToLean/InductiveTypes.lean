/- 7. Inductive Types -/

-- inductive Foo where
--   | constructor₁ : ... → Foo
--   | constructor₂ : ... → Foo
--   ...
--   | constructorₙ : ... → Foo

inductive Foo (α : Type) where
  | foo
  | bar (x : α)
  | baz (foo: Foo α)
deriving Repr

#check (Foo.foo : Foo Nat)
#check (Foo.foo : Foo String)
#check (Foo.bar 42 : Foo Nat)
#check (Foo.bar "hello" : Foo String)
#check (Foo.baz (Foo.bar 42) : Foo Nat)
#check (Foo.baz (Foo.bar "hello") : Foo String)

#eval Foo.bar 42

inductive Weekday where
  | sunday
  | monday
  | tuesday
  | wednesday
  | thursday
  | friday
  | saturday
deriving Repr

namespace Weekday
def next (d : Weekday) : Weekday :=
  match d with
  | sunday    => monday
  | monday    => tuesday
  | tuesday   => wednesday
  | wednesday => thursday
  | thursday  => friday
  | friday    => saturday
  | saturday  => sunday

def previous (d : Weekday) : Weekday :=
  match d with
  | sunday    => saturday
  | monday    => sunday
  | tuesday   => monday
  | wednesday => tuesday
  | thursday  => wednesday
  | friday    => thursday
  | saturday  => friday

theorem next_previous (d : Weekday) : next (previous d) = d := by
  cases d <;> rfl

end Weekday

-- 7.2 Constructors with Arguments

def prod_example (p : Bool × Nat) : Nat :=
  Prod.casesOn (motive := fun _ => Nat) p
    (fun b n => cond b (2 * n) (2 * n + 1))

#eval prod_example (true, 3)
-- 6

#eval prod_example (false, 3)
-- 7

def sum_example (s : Sum Nat Nat) : Nat :=
  Sum.casesOn (motive := fun _ => Nat) s
    (2 * ·)
    (2 * · + 1)

#eval sum_example (Sum.inl 3)
-- 6

#eval sum_example (Sum.inr 3)
-- 7

-- inductive definitions of Prod and Sum
namespace Hidden
inductive Prod (α : Type u) (β : Type v) where
  | mk (fst : α) (snd : β)

-- no projections given
-- #check Hidden.Prod.snd

universe u v
#check (Hidden.Prod : Type u → Type v → Type (max u v))

inductive Sum (α : Type u) (β : Type v) where
  | inl (a : α)
  | inr (b : β)

#check (Hidden.Sum : Type u → Type v → Type (max u v))
end Hidden

-- Prod is purely conjunctive because it only has one constructor
-- structure gives constructor and projections
namespace Hidden'
structure Prod (α : Type u) (β : Type v) where
  mk ::
  fst : α
  snd : β

-- get projections
#check Hidden'.Prod.fst
#check Hidden'.Prod.snd

universe u v
#check (Hidden'.Prod : Type u → Type v → Type (max u v))
end Hidden'

structure Semigroup where
  carrier : Type u
  mul : carrier → carrier → carrier
  mul_assoc : ∀ a b c, mul (mul a b) c = mul a (mul b c)

universe u
#check (Semigroup.{u} : Type (u + 1))

-- dependent product type
namespace Hidden
inductive Sigma {α : Type u} (β : α → Type v) where
  | mk : (a : α) → β a → Sigma β
end Hidden


-- As exercises, we encourage you to develop a notion of composition for partial
-- functions from α to β and β to γ, and show that it behaves as expected.
-- We also encourage you to show that Bool and Nat are inhabited, that the product
-- of two inhabited types is inhabited, and that the type of functions to an inhabited
-- type is inhabited.

def partial_compose (g : β → Option γ) (f : α → Option β) (x : α) : Option γ :=
  match f x with
  | none => none
  | some b => g b

example (f : α → β) (g : β → γ)
    : partial_compose (some ∘ g) (some ∘ f) = some ∘ g ∘ f := rfl

example : Inhabited Nat := Inhabited.mk 42
example : Inhabited Bool := Inhabited.mk true
example {α β : Type} [Inhabited α] [Inhabited β] : Inhabited (Prod α β) :=
  Inhabited.mk (Prod.mk default default)
example {α β : Type} [Inhabited β] : Inhabited (α → β) :=
  Inhabited.mk (fun _ => default)

-- 7.3. Inductively Defined Propositions

-- inductive types can live in any type universe
namespace Hidden
inductive False : Prop

inductive True : Prop where
  | intro

inductive And (a b : Prop) : Prop where
  | intro : a → b → And a b

inductive Or (a b : Prop) : Prop where
  | inl : a → Or a b
  | inr : b → Or a b
end Hidden

-- inductive types in Prop can only eliminate to other types in Prop
-- consistent with: if p : Prop, hp : p, then hp carries no data

-- even existential quantifier is inductive
namespace Hidden
inductive Exists {α : Sort u} (p : α → Prop) : Prop where
  | intro (w : α) (h : p w) : Exists p
end Hidden

-- syntactic sugar
example (p : α → Prop) : (∃ x, p x) = Exists p := rfl

-- inductive subtype {x : α // p x}
namespace Hidden
inductive Subtype {α : Sort u} (p : α → Prop) where
  | mk : (x : α) → p x → Subtype p

#check (Hidden.Subtype.{u} _ : Sort (max 1 u))
end Hidden

namespace Hidden'
structure Subtype {α : Sort u} (p : α → Prop) where
  val : α
  property : p val

#check (Hidden'.Subtype.{u} _ : Sort (max 1 u))
end Hidden'

-- syntactic sugar
example (p : α → Prop) : {x : α // p x} = Subtype p := rfl

-- 7.4 Defining the Natural Numbers

inductive Natural where
  | zero
  | succ : Natural → Natural
deriving Repr

#check Nat.rec
-- Nat.rec.{u} :
--   {motive : Nat → Sort u} →                        -- describes the type of object to construct
--   (zero : motive Nat.zero) →                       -- minor premise
--   (succ : (n : Nat) → motive n → motive n.succ) →  -- minor premise
--   (t : Nat) →                                      -- major premise
--   motive t

-- useful to put such definitions in a namespace
namespace Natural
def add (m n : Natural) : Natural :=
  match n with
  | .zero => m
  | .succ n => .succ (add m n)

instance : Add Natural where
  add := add

theorem add_zero (m : Natural) : m + zero = m := rfl
theorem add_succ (m n : Natural) : m + succ n = succ (m + n) := rfl

-- requires proof by induction
theorem zero_add (n : Natural) : zero + n = n :=
  Natural.recOn (motive := fun x => zero + x = x)
    n
    (show zero + zero = zero from rfl)
    (fun m (h : zero + m = m) =>
      show zero + (succ m) = succ m from
      calc zero + (succ m)
        _ = succ (zero + m) := rfl
        _ = succ m          := by rw [h])

-- with rw
theorem zero_add' (n : Natural) : zero + n = n :=
  Natural.recOn (motive := fun x => zero + x = x) n
    rfl
    (fun _ h => by rw [add_succ, h])

-- with simp
attribute [local simp] add_succ
theorem zero_add'' (n : Natural) : zero + n = n :=
  Natural.recOn n
    rfl
    (fun _ h => by simp [h])

-- left associative by definition
example (m n k : Natural) : m + n + k = (m + n) + k := rfl

-- right associativity of +
theorem add_assoc (m n k : Natural) : m + n + k = m + (n + k) :=
  Natural.recOn k
    rfl
    (fun k (h : m + n + k = m + (n + k)) =>
      show m + n + k.succ = m + (n + k.succ) by
      calc m + n + k.succ
        _ = (m + n + k).succ    := rfl
        _ = (m + (n + k)).succ  := by rw [h])

-- with simp
theorem add_assoc' (m n k : Natural) : m + n + k = m + (n + k) :=
  Natural.recOn k
    rfl
    (fun _ h => by simp [h])

-- commutativity of +

theorem succ_add (m n : Natural) : (m + n).succ = m.succ + n :=
  Natural.recOn n
    rfl
    (fun _ h => by rw [add_succ, h, add_succ])

theorem add_comm (m n : Natural) : m + n = n + m :=
  Natural.recOn n
    (by rw [zero_add, add_zero])
    (fun _ h => by simp [h, succ_add])

end Natural

-- 7.5 Other Recursive Data Types

namespace Hidden

inductive List (α : Type u) where
  | nil  : List α
  | cons (h : α) (t : List α) : List α

namespace List

def append (as bs : List α) : List α :=
  match as with
  | nil       => bs
  | cons a as => cons a (append as bs)

theorem nil_append (as : List α) : append nil as = as :=
  rfl

theorem cons_append (a : α) (as bs : List α) :
    append (cons a as) bs = cons a (append as bs) :=
  rfl

-- Exercises

theorem append_nil (as : List α) :
    append as nil = as :=
  List.recOn as
    rfl
    (fun x l h => by
      calc (cons x l).append nil
        _ = cons x (l.append nil) := rfl
        _ = cons x l              := by rw [h])

theorem append_assoc (as bs cs : Hidden.List α) :
    append (append as bs) cs = append as (append bs cs) :=
  List.recOn as
    rfl
    (fun x l h => by
      calc ((cons x l).append bs).append cs
        _ = (cons x (l.append bs)).append cs  := rfl
        _ = cons x ((l.append bs).append cs)  := rfl
        _ = cons x (l.append (bs.append cs))  := by rw [h])

def length (l : List α) : Nat :=
  match l with
  | nil => 0
  | cons _ t => 1 + length t

theorem length_nil : (nil : List α).length = 0 := rfl
theorem length_cons (x : α) (l : List α) : (cons x l).length = 1 + l.length := rfl

theorem length_append (as bs : List α)
    : length (as.append bs) = length as + length bs :=
  List.recOn as
    (by simp [nil_append, length_nil])
    (fun _ _ h => by simp [cons_append, length_cons, h, Nat.add_assoc])

end List
end Hidden

-- binary tree
inductive BinaryTree where
  | leaf : BinaryTree
  | node : BinaryTree → BinaryTree → BinaryTree

-- countably branching trees
inductive CBTree where
  | leaf : CBTree
  | sup : (Nat → CBTree) → CBTree

namespace CBTree

def succ (t : CBTree) : CBTree :=
  sup (fun _ => t)

def toCBTree : Nat → CBTree
  | 0 => leaf
  | n + 1 => succ (toCBTree n)

def omega : CBTree :=
  sup toCBTree

end CBTree

-- 7.6 Tactics for Inductive Types

example (p : Nat → Prop)
    (hz : p 0) (hs : ∀ n, p (.succ n))
    : ∀ n, p n := by
  intro n
  cases n
  . exact hz  -- case zero
  . apply hs  -- case succ

example (n : Nat) (h : n ≠ 0) : .succ (.pred n) = n := by
  cases n with
  | zero =>
    exact absurd rfl h
  | succ _ =>
    rfl

example (n : Nat) : .pred (.succ n) = n := by
  cases n <;> rfl

-- cases tactic can define data too

def f (n : Nat) : Nat := by
  cases n; exact 3; exact 7

example : f 0 = 3 := rfl
example : f 5 = 7 := rfl

-- cases will revert, split, and then reintroduce dependencies in the context

def Tuple (α : Type) (n : Nat) :=
  { as : List α // as.length = n }

def f' {n : Nat} (t: Tuple α n) : Nat := by
  cases n; exact 3; exact 7

def myTuple : Tuple Nat 3 :=
  ⟨ [0, 1, 2], rfl ⟩

example : f' myTuple = 7 :=
  rfl

-- multiple constructors with args

inductive Foo' where
  | bar1 : Nat → Nat → Foo'
  | bar2 : Nat → Nat → Nat → Foo'

def silly1 (x : Foo') : Nat := by
  cases x with
  | bar1 a b => exact b
  | bar2 c d e => exact e

def silly2 (x : Foo') : Nat := by
  cases x with
  | bar2 c d e => exact e
  | bar1 a b => exact b

-- case will focus on one subgoal

def silly3 (x : Foo') : Nat := by
  cases x
  case bar2 c d e => exact e
  case bar1 a b => exact b

-- using cases with an arbitrary goal expression
-- cases tactic generalizes over the expression

example (p : Nat → Prop) (hz : p 0) (hs : ∀ n, p (.succ n)) (m k : Nat)
    : p (m + 3 * k) := by
  cases m + 3 * k
  . exact hz   -- goal is p 0
  . apply hs   -- goal is a : Nat ⊢ p (succ a)

-- above functionally equivalent to
example (p : Nat → Prop) (hz : p 0) (hs : ∀ n, p (.succ n)) (m k : Nat)
    : p (m + 3 * k) := by
  generalize m + 3 * k = a
  cases a
  . exact hz
  . apply hs

-- cases will not revert any hypotheses that also mention the expression

-- if the expression cased on does not appear in the goal, the cases tactic
-- uses have to put the type of the expression into the context
example (p : Prop) (m n : Nat)
        (h₁ : m < n → p) (h₂ : m ≥ n → p) : p := by
  cases Nat.lt_or_ge m n
  case inl hlt => exact h₁ hlt
  case inr hge => exact h₂ hge

-- above functionally equivalent to
example (p : Prop) (m n : Nat)
        (h₁ : m < n → p) (h₂ : m ≥ n → p) : p := by
  have h : m < n ∨ m ≥ n := Nat.lt_or_ge m n
  cases h
  case inl hlt => exact h₁ hlt
  case inr hge => exact h₂ hge

-- decidability of equality on Nat

#check (Nat.sub_self : ∀ n, n - n = 0)

example (m n : Nat) : m - n = 0 ∨ m ≠ n := by
  cases Decidable.em (m = n) with
  | inl heq => rw [heq]; apply Or.inl; exact Nat.sub_self n
  | inr hne => exact Or.inr hne

-- induction tactic

theorem zero_add (n : Nat) : 0 + n = n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Nat.add_succ, ih]  -- ih is the induction hypothesis

-- using case tactic
example (n : Nat) : 0 + n = n := by
  induction n
  case zero => rfl
  case succ n ih => rw [Nat.add_succ, ih]

example (n : Nat) : 0 + n = n := by
  induction n
  . rfl
  . simp

-- additional examples
namespace Natural
theorem zero_add''' (n : Natural) : zero + n = n := by
  induction n; rfl; case _ h => rw [add_succ, h]

theorem succ_add' (m n : Natural) : (m + n).succ = m.succ + n := by
  induction n; rfl; case _ h => rw [add_succ, h, add_succ]

theorem add_comm' (m n : Natural) : m + n = n + m := by
  induction n
  . rw [zero_add''', add_zero]
  . case _ h => rw [add_succ, h, succ_add']

theorem add_assoc'' (m n k : Natural) : m + n + k = m + (n + k) := by
  induction k <;> simp [*, add_succ, add_zero]

end Natural

-- induction tactic supports user-defined induction principles with multiple targets

-- Nat.mod.inductionOn
--   {motive : Nat → Nat → Sort u}
--   (x y  : Nat)
--   (ind  : ∀ x y, 0 < y ∧ y ≤ x → motive (x - y) y → motive x y)
--   (base : ∀ x y, ¬(0 < y ∧ y ≤ x) → motive x y) :
--   motive x y

example (x : Nat) {y : Nat} (h : y > 0) : x % y < y := by
  induction x, y using Nat.mod.inductionOn with
  | ind x y h₁ ih =>
    rw [Nat.mod_eq_sub_mod h₁.2]
    exact ih h
  | base x y h₁ =>
    have : ¬ 0 < y ∨ ¬ y ≤ x := Iff.mp Decidable.not_and_iff_or_not h₁
    match this with
    | Or.inl h₁ => exact absurd h h₁
    | Or.inr h₁ =>
      have hgt : y > x := Nat.gt_of_not_le h₁
      rw [← Nat.mod_eq_of_lt hgt] at hgt
      assumption

-- match tactic

example : p ∨ q → q ∨ p := by
  intro h
  match h with
  | Or.inl _  => apply Or.inr; assumption
  | Or.inr h2 => apply Or.inl; exact h2

-- intro pattern-matching

example : p ∨ q → q ∨ p := by
  intro
  | Or.inl _  => apply Or.inr; assumption
  | Or.inr h2 => apply Or.inl; exact h2

example : s ∧ q ∧ r → p ∧ r → q ∧ p := by
  intro ⟨_, ⟨hq, _⟩⟩ ⟨hp, _⟩
  exact ⟨hq, hp⟩

-- funext pattern-matching

example :
    (fun (x : Nat × Nat) (y : Nat × Nat) => x.1 + y.2)
    =
    (fun (x : Nat × Nat) (z : Nat × Nat) => z.2 + x.1) := by
  funext (a, b) (c, d)
  show a + d = d + a
  rw [Nat.add_comm]

-- injection tactic

example (m n k : Nat) (h : m.succ.succ = n.succ.succ)
        : n + k = m + k := by
  injection h with h'   -- m.succ.succ = n.succ.succ => m.succ = n.succ
  injection h' with h'' -- m.succ = n.succ => m = n
  rw [h'']

example (m n k : Nat) (h : m.succ.succ = n.succ.succ)
        : n + k = m + k := by
  injections  -- m.succ.succ = n.succ.succ => ... => m = n
  simp [*]

-- injection tactic detects contradicitons that arise when different constructors
-- are set equal to one another and uses them to close the goal

example (m n : Nat) (h : m.succ = 0) : n = n + 7 := by
  injection h

example (m n : Nat) (h : m.succ = 0) : n = n + 7 := by
  contradiction

-- 7.7 Inductive Families

-- an inductive family is an indexed family of types defined via
-- inductive foo : ... → Sort u where
--   | constructor₁ : ... → foo ...
--   | constructor₂ : ... → foo ...
--   ...
--   | constructorₙ : ... → foo ...

-- ordinary inductive type constructs an element of some Sort u
-- inductive family contraucts a function ... → Sort u

namespace Hidden

inductive Vector (α : Type u) : Nat → Type u where
  | nil : Vector α 0
  | cons : α → {n : Nat} → Vector α n → Vector α (n + 1)

#check (Vector.cons 0 Vector.nil : Vector Nat 1)
#check (Vector.cons.{1} Nat Vector.nil : Vector Type 1)

inductive Eq {α : Sort u} : α → α → Prop where
  | refl (a : α) : Eq a a

end Hidden

-- elimination prinicple for Eq
universe v
#check (@Eq.rec : {α : Sort u} → {a : α} →
                  {motive : (x : α) → a = x → Sort v} →
                  motive a rfl →
                  {b : α} → (h : a = b) → motive b h)

-- all the basic axioms for equality follow from the constructor, refl,
-- and the eliminator, Eq.rec

-- Eq.rec is also used to define substitution
theorem subst {α : Type u} {a b : α} {p : α → Prop}
    (h₁ : Eq a b) (h₂ : p a) : p b :=
  Eq.rec (motive := fun x _ => p x) h₂ h₁

-- equivalently with match
theorem subst' {α : Type u} {a b : α} {p : α → Prop}
    (h₁ : Eq a b) (h₂ : p a) : p b :=
  match h₁ with
  | rfl => h₂

-- exercises

variable {α β : Type u} {a b c : α}

theorem symm (h : Eq a b) : Eq b a := by
  cases h; rfl

theorem transitive (h₁ : Eq a b) (h₂ : Eq b c) : Eq a c := by
  cases h₁; exact h₂

theorem congruence (f : α → β) (h : Eq a b) : Eq (f a) (f b) := by
  cases h; rfl

-- 7.8 Axiomatic Details

-- difference between target Prop and non-Prop

-- singleton elimination

-- 7.9 Mutual and Nested Inductive Types

-- mutually defined inductive types
mutual
  inductive Even : Nat → Prop where
  | even_zero : Even 0
  | even_succ : {n : Nat} → Odd n → Even (n + 1)

  inductive Odd : Nat → Prop where
  | odd_succ : {n : Nat} → Even n → Odd (n + 1)
end

theorem one_is_odd : Odd 1 := .odd_succ .even_zero

theorem two_is_even : Even 2 := .even_succ one_is_odd

-- 7.10 Exercises

-- 1. Define other operations on the natural numbers, such as
-- - multiplication
-- - the predecessor function (with pred 0 = 0)
-- - truncated subtraction (with n - m = 0 when m is greater than or equal to n)
-- - exponentiation
-- Then try proving some of their basic properties, building on the theorems we have already proved.

namespace Natural

-- multiplication
def mul (m : Natural)
  | zero => zero
  | succ n => mul m n + m

instance : Mul Natural where
  mul := mul

-- predecessor
def pred
  | zero => zero
  | succ n => n

-- truncated subtraction
def sub (m : Natural)
  | zero => m
  | succ n => (sub m n).pred

instance : Sub Natural where
  sub := sub

def one := zero.succ

-- exponentiation
def exp (m : Natural)
  | zero => one
  | succ n => exp m n * m

theorem succ_add_one (n : Natural) : n.succ = n + one := rfl
theorem mul_zero (n : Natural) : n * zero = zero := rfl
theorem mul_succ (m n : Natural) : m * n.succ = m * n + m := rfl

theorem zero_mul (n : Natural) : zero * n = zero := by
  induction n; rfl; case succ _ h => rw [mul_succ, add_zero, h]

theorem one_mul (n : Natural) : one * n = n := by
  induction n; rfl; case succ _ h => rw [mul_succ, h, succ_add_one]

-- multiply by 1 is self
theorem mul_one (n : Natural) : n * one = n := by
  cases n; rfl; rw [one, mul_succ _, mul_zero, zero_add]

-- distributive properties
theorem left_distrib (m n k : Natural) : m * (n + k) = m * n + m * k := by
  induction k; rfl
  . case succ _ h => rw [add_succ, mul_succ, mul_succ, h, add_assoc]

-- distributive property
theorem right_distrib (m n k : Natural) : (m + n) * k = m * k + n * k := by
  induction k; rfl
  . case succ k h =>
    calc (m + n) * k.succ
      _ = (m + n) * k + (m + n)     := mul_succ (m + n) k
      _ = (m + n) * k + m + n       := by rw [←add_assoc]
      _ = m * k + n * k + m + n     := by rw [h]
      _ = m * k + (n * k + m) + n   := by simp [add_assoc]
      _ = m * k + (m + n * k) + n   := by simp [add_comm]
      _ = (m * k + m + n * k) + n   := by rw [←add_assoc]
      _ = (m * k.succ + n * k) + n  := rfl
      _ = m * k.succ + (n * k + n)  := by simp [add_assoc]

-- (right) associativity of multiplication
theorem mul_assoc (m n k : Natural) : m * n * k = m * (n * k) := by
  induction k; rfl
  . case succ _ h => rw [mul_succ, mul_succ, h, left_distrib]

-- commutativity of multiplication
theorem mul_comm (m n : Natural) : m * n = n * m := by
  induction n
  . rw [mul_zero, zero_mul]
  . case succ n h => rw [succ_add_one, left_distrib, right_distrib, mul_one, one_mul, h]

-- predecessor of successor is self
theorem pred_succ (n : Natural) : n.succ.pred = n := by
  induction n <;> rfl

end Natural

-- 2. Define some operations on lists, like a length function or the reverse function. Prove some properties, such as the following:
-- a. length (xs ++ ys) = length xs + length ys
-- b. length (reverse xs) = length xs
-- c. reverse (reverse xs) = xs

def length (as : List α) :=
  match as with
  | .nil => 0
  | .cons _ t => 1 + length t

def reverse (as : List α) : List α :=
  match as with
  | .nil => []
  | .cons x t => reverse t ++ [x]

#eval (reverse [1,2, 3] = [3, 2, 1])

theorem length_nil : length (.nil : List α) = 0 := rfl
theorem length_cons : length (.cons x t : List α) = 1 + length t := rfl

theorem length_append (as bs : List α) : length (as ++ bs) = length as + length bs := by
  induction as
  . simp [length_nil]
  . case cons _ _ h => simp [List.cons_append, length_cons, h, Nat.add_assoc]

theorem reverse_nil : reverse (.nil : List α) = .nil := rfl
theorem reverse_cons (x : α) (t : List α) : reverse (.cons x t) = reverse t ++ [x] := rfl
theorem reverse_singleton (x : α) : reverse [x] = [x] := rfl
theorem reverse_append_singleton (as : List α) (x : α) : reverse (as ++ [x]) = [x] ++ reverse as := by
  induction as; rfl
  . case cons x t h => simp [reverse_cons, h]

theorem reverse_append (as bs : List α) : reverse (as ++ bs) = reverse bs ++ reverse as := by
  induction as
  . simp [reverse_nil]
  . case cons _ _ h => rw [reverse_cons, ←List.append_assoc, ←h, ←reverse_cons, List.cons_append]

theorem reverse_reverse (as : List α) : reverse (reverse as) = as := by
  induction as; rfl
  . case _ _ h => simp [reverse_cons, reverse_append, reverse_nil, h]

-- 3. Define an inductive data type consisting of terms built up from the following constructors:
-- - const n, a constant denoting the natural number n
-- - var n, a variable, numbered n
-- - plus s t, denoting the sum of s and t
-- - times s t, denoting the product of s and t
-- Recursively define a function that evaluates any such term with respect to an assignment of values to the variables.

namespace NatExpr

inductive NatExpr : Type where
  | const : Nat → NatExpr
  | var : Nat → NatExpr
  | plus : NatExpr → NatExpr → NatExpr
  | times : NatExpr → NatExpr → NatExpr

def eval {assignments : List Nat} (e : NatExpr) : Nat :=
  match e with
  | .const n => n
  | .var n => assignments[n]!
  | .plus e1 e2 => @eval assignments e1 + @eval assignments e2
  | .times e1 e2 => @eval assignments e1 * @eval assignments e2

#reduce (eval (.const 42))
#reduce (eval (assignments := [42]) (.var 0))
#reduce (eval (assignments := [19]) (.plus (.var 0) (.const 23)))
#reduce (eval (assignments := [19, 23]) (.plus (.var 0) (.var 1)))
#reduce (eval (assignments := [6, 7]) (.times (.var 0) (.var 1)))
#reduce (eval (assignments := [6]) (.times (.var 0) (.const 7)))

end NatExpr

-- 4. Similarly, define the type of propositional formulas, as well as functions on the type of such formulas:
-- - an evaluation function
-- - function that measures the complexity of a formula
-- - function that substitutes another formula for a given variable

namespace PropExpr

inductive PropExpr where
  | const : Bool → PropExpr
  | var : Nat → PropExpr
  | or : PropExpr → PropExpr → PropExpr
  | and : PropExpr → PropExpr → PropExpr

def eval {assignments : List Bool} (e : PropExpr) : Bool :=
  match e with
  | .const p => p
  | .var n => assignments[n]!
  | .or e1 e2 => @eval assignments e1 || @eval assignments e2
  | .and e1 e2 => @eval assignments e1 && @eval assignments e2

#eval (eval (assignments := []) (.const True) = True)
#eval (eval (assignments := [True]) (.var 0) = True)
#eval (eval (assignments := [True]) (.or (.var 0) (.const False)) = True)
#eval (eval (assignments := [True, False]) (.or (.var 0) (.var 1)) = True)
#eval (eval (assignments := [True]) (.and (.var 0) (.const False)) = False)
#eval (eval (assignments := [True, False]) (.and (.or (.var 0) (.const True)) (.var 1)) = False)

def complexity (e : PropExpr) : Nat :=
  match e with
  | .const _ => 0
  | .var _ => 1
  | .or e1 e2 | .and e1 e2 => 1 + complexity e1 + complexity e2

#eval (complexity (.const True) = 0)
#eval (complexity (.var 0) = 1)
#eval (complexity (.or (.var 0) (.const False)) = 2)
#eval (complexity (.or (.var 0) (.var 1)) = 3)
#eval (complexity (.and (.var 0) (.const False)) = 2)
#eval (complexity (.and (.or (.var 0) (.const True)) (.var 1)) = 4)

def substitute (index : Nat) (target e : PropExpr) : PropExpr :=
  match e with
  | .const p => .const p
  | .var n => if n = index then target else .var n
  | .or e1 e2 => .or (substitute index target e1) (substitute index target e2)
  | .and e1 e2 => .and (substitute index target e1) (substitute index target e2)

#eval (eval (assignments := []) (substitute 0 (.const True) (.var 0)) = True)
#eval (eval (assignments := [True]) (substitute 1 (.var 0) (.var 1)) = True)
#eval (eval (assignments := []) (substitute 1 (.const False) (.and (.var 1) (.const True))) = False)

end PropExpr
