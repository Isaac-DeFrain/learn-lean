/- 10. Type Classes -/

-- principled way to enable ad-hoc polymorphism

namespace Hidden

structure Add (α : Type) where
  add : α → α → α

#check @Add.add
-- @Add.add : {α : Type} → Add α → α → α → α

def double (a : Add α) (x : α) : α :=
  a.add x x

#eval double { add := Nat.add } 10
-- 20

end Hidden

-- _type class resolution_ synthesizes desired instance of an implicit instance

namespace TC

class Add (α : Type) where
  add : α → α → α

#check @Add.add
-- @Add.add : {α : Type} → [self : Add α] → α → α → α

-- [self : Add α] is an _instance implicit_ argument

-- register instances

instance : Add Nat where
  add := Nat.mul

instance : Add Float where
  add := Float.add

#eval Add.add 10 2
-- 20

def double [Add α] (x : α) : α :=
  Add.add x x

#eval double 2.
-- 4.000000

end TC

-- type classes can depend on each other in complicated ways

instance [Add α] : Add (Array α) where
  add := Array.zipWith (· + ·)

#eval Add.add #[1, 2] #[3, 4]
-- #[4, 6]

#eval #[1, 2] + #[3, 4]
-- #[4, 6]

namespace TC

class Inhabited (α : Type u) where
  default : α

#check @Inhabited.default
-- @Inhabited.default : {α : Type u_1} → [self : Inhabited α] → α

instance : Inhabited Bool where
  default := true

instance : Inhabited Nat where
  default := 42

instance : Inhabited Unit where
  default := ()

instance : Inhabited Prop where
  default := True

#eval (Inhabited.default : Nat)
-- 42

#eval (default : Unit)
-- ()

end TC

-- 10.1 Chaining Instances

instance [Inhabited α] [Inhabited β] : Inhabited (α × β) where
  default := (default, default)

#eval (default : Nat × Bool)
-- (0, false)

instance [Inhabited β] : Inhabited (α → β) where
  default := fun _ => default

-- exercise: default instances of List and Sum

instance : Inhabited (List α) where
  default := []

instance [Inhabited α] : Inhabited (Sum α β) where
  default := .inl default

instance [Inhabited β] : Inhabited (Sum α β) where
  default := .inr default

-- triggers type class resolution

#check @inferInstance
-- @inferInstance : {α : Sort u_1} → [i : α] → α

example : (inferInstance : Inhabited (Nat × Nat)).default = (default, default) := rfl

#print inferInstance
-- @[reducible] def inferInstance.{u} : {α : Sort u} → [i : α] → α :=
-- fun {α} [i : α] => i

-- 10.2 ToString

#check @ToString.toString
-- @toString : {α : Type u_1} → [self : ToString α] → α → String

structure Person where
  name : String
  age  : Nat

instance : ToString Person where
  toString p := p.name ++ "@" ++ toString p.age

#eval toString { name := "Leo", age := 542 : Person }
-- "Leo@542"

#eval toString ({ name := "Daniel", age := 18 : Person }, "hello")
-- "(Daniel@18, hello)"

-- 10.3 Numerals

-- numerals can denote an element of any type that implements the type class OfNat

structure Rational where
  num : Int
  den : Nat
  inv : den ≠ 0

instance : OfNat Rational n where
  ofNat := { num := n, den := 1, inv := by decide }

instance : ToString Rational where
  toString r := s!"{r.num}/{r.den}"

#eval (2 : Rational)
-- 2/1

#eval (2 : Nat)
-- 2

-- raw natural numbers are not polymorphic

#check nat_lit 2
-- 2 : Nat

-- OfNat instance is parametric on the numeral

class Monoid (α : Type u) where
  unit : α
  op : α → α → α

instance [m : Monoid α] : OfNat α (nat_lit 1) where
  ofNat := m.unit

def getUnit [Monoid α] : α :=
  1

example [m : Monoid α] : 1 = m.unit := rfl

-- 10.4 Output Parameters

/--
error: typeclass instance problem is stuck, it is often due to metavariables
  Inhabited (Nat × ?m.2)
-/
#guard_msgs (error) in
#eval (inferInstance : Inhabited (Nat × _))

-- can view the parameter of the type class Inhabited as an _input value_
-- for the type class synthesizer

namespace TC

class HMul (α : Type u) (β : Type v) (γ : outParam (Type w)) where
  hMul : α → β → γ

export HMul (hMul)

instance : HMul Nat Nat Nat where
  hMul := Nat.mul

instance : HMul Int Int Int where
  hMul := Int.mul

instance [HMul α β γ] : HMul α (Array β) (Array γ) where
  hMul a bs := bs.map (hMul a ·)

#eval hMul 4 3
-- 12

#eval hMul 4 #[1, 2, 3]
-- #[4, 8, 12]

#eval hMul (-1) (2 : Int)
-- -2

#eval hMul (-2) #[-1, 4]
-- #[2, -8]

#eval hMul 2 #[#[1, 2], #[3, 4]]
-- #[#[2, 4], #[6, 8]]

-- output parameters are ignored during instance synthesis

-- semi-output parameters
-- like input parametes, are considered when selecting instances
-- like output parameters, can be used to instantiate unknown values

end TC

-- 10.5 Default Instances

namespace Ex1

class HMul (α : Type u) (β : Type v) (γ : outParam (Type w)) where
  hMul : α → β → γ

export HMul (hMul)

instance : HMul Int Int Int where
  hMul := Int.mul

def xs : List Int := [1, 2, 3]

/--
error: typeclass instance problem is stuck
  HMul Int ?m.2 (?m.11 y)

Note: Lean will not try to resolve this typeclass instance problem because the second type argument to `HMul` is a metavariable. This argument must be fully determined before Lean will try to resolve the typeclass.

Hint: Adding type annotations and supplying implicit arguments to functions can give Lean more information for typeclass resolution. For example, if you have a variable `x` that you intend to be a `Nat`, but Lean reports it as having an unresolved type like `?m`, replacing `x` with `(x : Nat)` can get typeclass resolution un-stuck.
-/
#guard_msgs (error) in
#eval fun y => xs.map (hMul · y)

end Ex1

-- [default_instance] attribute instructs Lean to use the instance on pending type class synthesis problems

namespace Ex2

class HMul (α : Type u) (β : Type v) (γ : outParam (Type w)) where
  hMul : α → β → γ

export HMul (hMul)

@[default_instance]
instance : HMul Int Int Int where
  hMul := Int.mul

def xs : List Int := [1, 2, 3]

#check fun y => xs.map (hMul · y)
-- fun y => List.map (fun x => hMul x y) xs : Int → List Int

end Ex2

namespace TCPriority1

structure Rational where
  num : Int
  den : Nat
  inv : den ≠ 0

@[default_instance 200] -- has higher priority than OfNat Nat
instance instOfNatRational : OfNat Rational n where
  ofNat := { num := n, den := 1, inv := by decide }

instance : ToString Rational where
  toString r := s!"{r.num}/{r.den}"

#eval 2
-- 2/1

end TCPriority1

-- priorities are useful for controlling the interaction between different default instances

-- e.g. when elaborating xs.map (2 * ·), we want the homogeneous instance for multiplication
-- to have higher priority than the default instance for OfNat α 2

namespace TCPriority2
class OfNat (α : Type u) (n : Nat) where
  ofNat : α

attribute [default_instance 300] instOfNatNat -- higher priority than OfNat Rational

class HMul (α : Type u) (β : Type v) (γ : outParam (Type w)) where
  hMul : α → β → γ

class Mul (α : Type u) where
  mul : α → α → α

@[default_instance 10]
instance [i : Mul α] : HMul α α α where
  hMul := i.mul

instance : Mul Nat where mul := Nat.mul

infixl:70 " <*> " => HMul.hMul

#check (fun {α β} [HMul α β _] (x : α) (y : β) => x <*> y)

#eval [1, 2, 3].map (2 <*> ·) -- uses Mul Nat instance
-- [2, 4, 6]

#eval [1, 2, 3].map (HMul.hMul 2 ·) -- uses Mul Nat instance
-- [2, 4, 6]

end TCPriority2

-- 10.6 Local Instances

-- instance scoped only to current section/namespace/file

structure Point where
  x : Nat
  y : Nat

section

local instance : Add Point where
  add a b := { x := a.x + b.x, y := a.y + b.y }

#check (fun p q => p + q : Point → Point → Point)

end -- instance `Add Point` is not active anymore

/--
error: failed to synthesize instance of type class
  HAdd Point Point ?m.5

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
def triple (p : Point) :=
  p + p + p

-- can also disable an instance using the `attribute` command

instance addPoint : Add Point where
  add a b := { x := a.x + b.x, y := a.y + b.y }

#check (fun p q => p + q : Point → Point → Point)

attribute [-instance] addPoint

/--
error: failed to synthesize instance of type class
  HAdd Point Point ?m.5

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
def triple (p : Point) :=
  p + p + p

-- it is recommended to use instance erasure only for diagnosing problems

-- 10.7 Scoped Instances

-- instances scoped to section/namespace/file and can be opened

namespace Point

scoped instance : Add Point where
  add p q := { x := p.x + q.x, y := p.y + q.y }

def double (p : Point) :=
  p + p

end Point -- instance `Add Point` is not active anymore

/--
error: failed to synthesize instance of type class
  HAdd Point Point ?m.3

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs (error) in
#check fun (p : Point) => p + p + p

namespace Point

-- instance `Add Point` is active again
#check (fun p q => p + q : Point → Point → Point)

end Point

-- open Point     -- activates instance `Add Point` and `double`
open scoped Point -- activates instance `Add Point` but not `double`

#check (fun p q => p + q : Point → Point → Point)

/--
error: Unknown identifier `double`
-/
#guard_msgs (error) in
#check double

-- 10.8 Decidable Propositions

-- roughly, an element of `Prop` is called _decidable_ if we can "decide" whether it is true or false
-- distinction is only useful in constructive mathematics; classically, every proposition is decidable

namespace Hidden

class inductive Decidable (p : Prop) where
  | isFalse (h : ¬p)
  | isTrue (h : p)

-- logically, having an element `t : Decidable p` is stronger than having `t : p ∨ ¬p`
-- it enables us to define values of an arbitrary type depending on the truth value of `p`

-- e.g. for `if p then a else b` to make sense, `p` must be decidable
-- syntax sugar for
def ite {α : Sort u}
    (c : Prop) [h : Decidable c]
    (t e : α) : α :=
  Decidable.casesOn (motive := fun _ => α) h (fun _ => e) (fun _ => t)

-- dependent ite
def dite {α : Sort u}
    (c : Prop) [h : Decidable c]
    (t : c → α)   -- can assume `hc : c` in "then" branch
    (e : ¬c → α)  -- can assume `hnc : ¬c` in "else" branch
    : α :=
  Decidable.casesOn (motive := fun _ => α) h e t

end Hidden

-- cannot prove that all propostions are decidable
-- can prove decidability of basic operations like equality and comparisions on Nat and Int

-- propositional connectives preserve deciability

#check @instDecidableAnd
-- @instDecidableAnd : {p q : Prop} → [dp : Decidable p] → [dq : Decidable q] → Decidable (p ∧ q)

#check @instDecidableOr
-- @instDecidableOr : {p q : Prop} → [dp : Decidable p] → [dq : Decidable q] → Decidable (p ∨ q)

#check @instDecidableNot
-- @instDecidableNot : {p : Prop} → [dp : Decidable p] → Decidable ¬p

namespace DecidablePredicatesOnNat

def step (a b x : Nat) : Nat :=
  if x < a ∨ x > b then 0 else 1

-- elaborator infers the decidability of `x < a ∨ x > b` by applying appropriate instances
set_option pp.explicit true
#print step
-- def DecidablePredicatesOnNat.step : Nat → Nat → Nat → Nat :=
-- fun a b x =>
--   @ite Nat (Or (@LT.lt Nat instLTNat x a) (@GT.gt Nat instLTNat x b))
--     (@instDecidableOr (@LT.lt Nat instLTNat x a) (@GT.gt Nat instLTNat x b) (x.decLt a) (b.decLt x))
--     (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))

end DecidablePredicatesOnNat

-- all propositions are decidable in classical logic
namespace ClassicalDecidability

-- priority low ensures that Lean will favor other instances and fall back on
-- `propDecidable` only after other attemps to infer decidability have failed
noncomputable scoped
instance (priority := low) propDecidable (a : Prop) : Decidable a :=
  open Classical (choice em) in
  choice <| match em a with
    | .inl h => ⟨isTrue h⟩
    | .inr h => ⟨isFalse h⟩

end ClassicalDecidability

-- decide tactic uses the Decidable instance to solve simple goals
-- decide function uses the Decidable instance to compute corresponding Bool

example : 10 < 5 ∨ 1 > 0 := by decide
example : ¬(True ∧ False) := by decide
example : 2 * 21 = 42 := by decide

theorem ex : True ∧ 2 = 1 + 1 := by decide
#print ex
-- theorem ex : True ∧ 2 = 1 + 1 :=
-- of_decide_eq_true (id (Eq.refl true))

#check @of_decide_eq_true
-- @of_decide_eq_true : ∀ {p : Prop} [inst : Decidable p], decide p = true → p

#check @decide
-- decide : (p : Prop) → [h : Decidable p] → Bool

-- 10.9 Managing Type Class Inference

-- supply an expression which Lean can infer by type class inference
@[instance_reducible] def foo : Add Nat := inferInstance
@[instance_reducible] def bar : Inhabited (Nat → Nat) := inferInstance

example : foo.add = Nat.add := rfl
example : bar.default = fun _ => 0 := rfl

-- more concisely
#check (inferInstance : Add Nat)
#check (inferInstance : Inhabited (Nat → Nat))

-- if an instance is buried in a definition, we can declare one explicitly

def Set (α : Type u) := α → Prop

/--
error: failed to synthesize instance of type class
  Inhabited (Set α)

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
example : Inhabited (Set α) := inferInstance

instance : Inhabited (Set α) :=
  inferInstanceAs (Inhabited (α → Prop))

example : Inhabited (Set α) := inferInstance

-- request a trace of the type class instance search
-- set_option trace.Meta.synthInstance true

-- limit search memory allocations (in thousands); 0 means no limit
-- set_option synthInstance.maxHeartbeats 10000

-- limit number of instances used to construct a solution to the type class synthesis procedure
-- set_option synthInstance.maxSize 400

-- can change the order in which type class instances are tried by assigning _priority_

class Foo where
  a : Nat
  b : Nat

instance (priority := default + 1) i1 : Foo where
  a := 1
  b := 1

instance i2 : Foo where
  a := 2
  b := 2

example : Foo.a = 1 := rfl

attribute [-instance] i1

example : Foo.a = 2 := rfl

instance i3 : Foo where
  a := 3
  b := 3

example : Foo.a = 3 := rfl

-- 10.10 Coercions using Type Classes

-- most basic kind of coercion maps elements of one type to another type
example (n : Nat) : Int := n

-- Lean allows three kinds of coercions:
-- 1. from a family of types to another family of types
-- 2. from a family of types to class of sorts
-- 3. from a family of types to the class of function types

-- coercions are implemented on top of the type class resolution framework

-- 1. coercion from α to β
instance : Coe Bool Prop where
  coe b := b = true -- decidable proposition

#eval if true then 5 else 3
-- 5

#eval if false then 5 else 3
-- 3

-- define a coercion from List α to Set α
def Set.empty {α : Type u} : Set α := fun _ => False
def Set.mem (a : α) (s : Set α) : Prop := s a
def Set.singleton (a : α) : Set α := fun x => x = a
def Set.union (a b : Set α) : Set α := fun x => a x ∨ b x

notation "{ " a " }" => Set.singleton a
infix:55 " ∪ " => Set.union

def List.toSet : List α → Set α
  | [] => Set.empty
  | a :: as => {a} ∪ as.toSet

instance : Coe (List α) (Set α) where
  coe a := a.toSet

def s : Set Nat := {1}
#check s ∪ [2, 3]
-- s ∪ [2, 3].toSet : Set Nat

-- force coercion with ↑ making intent clear
#check let x := ↑[2, 3]; s ∪ x
-- let x := [2, 3].toSet;
-- s ∪ x : Set Nat

#check let x := [2, 3]; s ∪ x
-- let x := [2, 3];
-- s ∪ x.toSet : Set Nat

-- dependent coercions

-- cannot coerce arbitrary propositions to Bool, but can coerce decidable ones
instance (p : Prop) [Decidable p] : CoeDep Prop p Bool where
  coe := decide p

-- Lean will chain (non-dependent) coercions together as needed
-- type class `CoeT` is the transitive closure of `Coe`

-- 2. coercion from α to Type u
-- of the form `c : (x₁ : A₁) → ⋯ → (xₙ : Aₙ) → F x₁ ... xₙ → Type u`
-- where `F` is a family of types

-- allows us to write `s : t` whenever `t` is a type of the form `F a₁ ... aₙ`
-- coercion allows us to view the elements of `F a₁ ... aₙ` as types

structure Semigroup where
  carrier : Type u
  mul : carrier → carrier → carrier
  mul_assoc (a b c : carrier) : mul (mul a b) c = mul a (mul b c)

instance (S : Semigroup) : Mul S.carrier where mul := S.mul

#check Semigroup.carrier
-- Semigroup.carrier.{u} (self : Semigroup) : Type u

-- if we declare this function to be a coercion, we can write `a : S` instead of `a : S.carrier`

instance : CoeSort Semigroup (Type u) where
  coe s := s.carrier

example (S : Semigroup) (a b c : S) : (a * b) * c = a * (b * c) := S.mul_assoc a b c

-- 3. corecion from α to a function
-- of the form `c : (x₁ : A₁) → ... → (xₙ : Aₙ) → (y : F x₁ ... xₙ) → (z : B) → C`
-- where `F` is a family of types, `B` and `C` depend on `x₁, ..., xₙ, y`

-- allows us to write `t s` whenever `t` is an element of `F a₁ ... aₙ` and `s : B`
-- coercion allows us to view the elements of `F a₁ ... aₙ` as functions

structure Morphism (S1 S2 : Semigroup) where
  mor : S1 → S2
  resp_mul : ∀ (a b : S1), mor (a * b) = mor a * mor b

#check @Morphism.mor
-- @Morphism.mor : {S1 : Semigroup} → {S2 : Semigroup} → Morphism S1 S2 → S1.carrier → S2.carrier

instance (S1 S2 : Semigroup) :
    CoeFun (Morphism S1 S2) (fun _ => S1 → S2) where
  coe m := m.mor

-- can write `f x` instead of `f.mor x`
theorem resp_mul {S1 S2 : Semigroup} (f : Morphism S1 S2) (a b : S1)
    : f (a * b) = f a * f b :=
  f.resp_mul a b
-- resp_mul.{u_1, u_2} {S1 : Semigroup} {S2 : Semigroup} (f : Morphism S1 S2) (a b : S1.carrier) :
--   f.mor (a * b) = f.mor a * f.mor b

example (S1 S2 : Semigroup) (f : Morphism S1 S2) (a : S1)
    : f (a * a * a) = f a * f a * f a :=
  calc f (a * a * a)
    _ = f (a * a) * f a := by rw [f.resp_mul]
    _ = f a * f a * f a := by rw [f.resp_mul]
-- _example.{u_1, u_2} (S1 : Semigroup) (S2 : Semigroup) (f : Morphism S1 S2) (a : S1.carrier) :
--   f.mor (a * a * a) = f.mor a * f.mor a * f.mor a
