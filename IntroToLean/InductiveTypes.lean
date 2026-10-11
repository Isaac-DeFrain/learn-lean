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
  Natural.recOn (motive := fun x => zero + x = x) n
    rfl
    (fun _ h => by simp [h])

-- left associative by definition
example (m n k : Natural) : m + n + k = (m + n) + k := rfl

-- right associativity of +
theorem add_assoc (m n k : Natural) : m + n + k = m + (n + k) :=
  Natural.recOn (motive := fun k => m + n + k = m + (n + k)) k
    rfl
    (fun k (h : m + n + k = m + (n + k)) =>
      show m + n + k.succ = m + (n + k.succ) by
      calc m + n + k.succ
        _ = (m + n + k).succ    := rfl
        _ = (m + (n + k)).succ  := by rw [h])

-- with simp
theorem add_assoc'' (m n k : Natural) : m + n + k = m + (n + k) :=
  Natural.recOn (motive := fun k => m + n + k = m + (n + k)) k
    rfl
    (fun _ h => by simp [h])

-- commutativity of +

theorem succ_add (m n : Natural) : (m + n).succ = m.succ + n :=
  Natural.recOn (motive := fun n => (m + n).succ = m.succ + n) n
    rfl
    (fun _ h => by rw [add_succ, h, add_succ])

theorem add_comm (m n : Natural) : m + n = n + m :=
  Natural.recOn (motive := fun n => m + n = n + m) n
    (by rw [zero_add, add_zero])
    (fun _ h => by simp [h, succ_add])

end Natural

-- 7.5 Other Recursive Data Types
