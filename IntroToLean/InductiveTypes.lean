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
    (fun n => 2 * n)
    (fun n => 2 * n + 1)

#eval sum_example (Sum.inl 3)
-- 6

#eval sum_example (Sum.inr 3)
-- 7

namespace Hidden
structure Prod (α : Type u) (β : Type v) where
  mk ::
  fst : α
  snd : β
end Hidden

structure Semigroup where
  carrier : Type u
  mul : carrier → carrier → carrier
  mul_assoc : ∀ a b c, mul (mul a b) c = mul a (mul b c)

universe u
#check (Semigroup.{u} : Type (u + 1))

-- As exercises, we encourage you to develop a notion of composition for partial
-- functions from α to β and β to γ, and show that it behaves as expected.
-- We also encourage you to show that Bool and Nat are inhabited, that the product
-- of two inhabited types is inhabited, and that the type of functions to an inhabited
-- type is inhabited.

def partial_compose (g : β → Option γ) (f : α → Option β) (x : α) : Option γ :=
  match f x with
  | none => none
  | some b => g b

example : Inhabited Nat := Inhabited.mk 42
example : Inhabited Bool := Inhabited.mk true
example {α β : Type} [Inhabited α] [Inhabited β] : Inhabited (Prod α β) :=
  Inhabited.mk (Prod.mk default default)
example {α β : Type} [Inhabited β] : Inhabited (α → β) :=
  Inhabited.mk (fun _ => default)

-- 7.3. Inductively Defined Propositions
