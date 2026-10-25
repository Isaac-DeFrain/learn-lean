/- 12. Axioms and Computation -/

-- Calculus of Constructions implemented in Lean includes dependent function types,
-- inductive types, and a hierarchy of type universes that starts with an impredicative
-- proof-irrelevant `Prop` at the bottom

-- the use of axioms bears on the computational content of definitions and theorems

-- `noncomputable` is used to mark definitions with no computational content

-- addtional components on top of above mentioned:
-- 1. the axiom of propositional extensionality
-- 2. a quotient construction, which implies function extensionality
-- 3. a choice principle, which produces data from an extensional proposition

-- first two block normalization within Lean, but are compatible with code generation
-- third is not amenable to computational interpretation

-- 12.1 Historical and Philosophical Context

-- constructive: every theorem should have a direct computational interpretation
-- classical: separation between constructive and nonconstructive theories
-- Lean is designed to support both

-- every closed term of type `Nat` evaluates to a numeral, `succ (... (succ zero)...)`

-- proof-irrelevant `Prop` with _irreducible_ theorems represents a step towards classical

-- elements of type `p : Prop` should play no role in computation
-- construction of `prf : p` is irrelevant in that sense

-- we can still define computational objects that incorporate elements of type `Prop`,
-- these elements can help us reason about the effects of computation, but can be ignored
-- when extracting "code" from the term

-- equations `s = t : α` for any type α can be used as casts, to type check terms

-- such casts can block computation, however, computation is still possible under
-- an evaluation scheme that erases propositional content, ignores intermediate typing
-- constraints, and reduces terms to a normal form

-- 12.2 Propositional Extensionality

-- axiom of propositional extensionality
#check propext
-- propext {a b : Prop} : (a ↔ b) → a = b

-- consistent with set-theoretic interpretation in which every element `a : Prop`
-- is either empty or the singleton set `{*}`, for some distinguished element `*`

-- equivalent propositions are equal and hence, can be substituted for one another

variable (a b c d e : Prop)

theorem thm₁ (h : a ↔ b) : (c ∧ a ∧ d → e) ↔ (c ∧ b ∧ d → e) :=
  propext h ▸ Iff.refl _

theorem thm₂ (p : Prop → Prop) (h : a ↔ b) (h₁ : p a) : p b :=
  propext h ▸ h₁

-- 12.3 Function Extensionality

-- theorem of function extensionality
#check funext
-- funext.{u, v}
--    {α : Sort u} {β : α → Sort v}
--    {f g : (x : α) → β x}
--    (h : ∀ (x : α), f x = g x)
--    : f = g

-- meaning of function equality from classical, set-theoretic perspective (extensional)

-- intensional view does not force us to identify functions with same input/output behavior

def Set (α : Type u) := α → Prop

namespace Set

def mem (x : α) (s : Set α) := s x

infix:50 (priority := high) "∈" => mem

theorem setext {s1 s2 : Set α} (h : ∀ x, x ∈ s1 ↔ x ∈ s2) : s1 = s2 :=
  funext (fun x => propext (h x))

def empty : Set α := fun _ => False

notation (priority := high) "∅" => empty

def inter (s1 s2 : Set α) : Set α :=
  fun x => x ∈ s1 ∧ x ∈ s2

infix:70 " ∩ " => inter

theorem inter_self (s : Set α) : s ∩ s = s :=
  setext fun _ => Iff.intro
    (fun ⟨h, _⟩ => h)
    (fun h => ⟨h, h⟩)

theorem inter_empty (s : Set α) : s ∩ empty = empty :=
  setext fun _ => Iff.intro
    (fun ⟨_, h⟩ => h)
    False.elim

theorem empty_inter (s : Set α) : empty ∩ s = empty :=
  setext fun _ => Iff.intro
    (fun ⟨h, _⟩ => h)
    False.elim

theorem inter.comm (s t : Set α) : s ∩ t = t ∩ s :=
  setext fun _ => Iff.intro
    (fun ⟨hs, ht⟩ => ⟨ht, hs⟩)
    (fun ⟨ht, hs⟩ => ⟨hs, ht⟩)

end Set

-- example of how function extensionality blocks computation in the Lean kernel

namespace FunExt

def f (x : Nat) := x
def g (x : Nat) := 0 + x

theorem f_eq_g : f = g :=
  funext fun x => (Nat.zero_add x).symm

def val : Nat :=
  Eq.recOn (motive := fun _ _ => Nat) f_eq_g 0

-- does not reduce to 0
#reduce val
-- f_eq_g ▸ 0

-- evaluates to 0
#eval val
-- 0

end FunExt

-- example of how propositional extensionality does the same thing

namespace PropExt

theorem tt_eq_t : (True ∧ True) = True :=
  propext <| Iff.intro
    (fun ⟨h, _⟩ => h)
    (fun h => ⟨h, h⟩)

def val' : Nat :=
  Eq.recOn (motive := fun _ _ => Nat) tt_eq_t 0

-- does not reduce to 0
#reduce val'
-- tt_eq_t ▸ 0

-- evaluates to 0
#eval val'
-- 0

end PropExt

-- 12.4 Quotients

-- α any type
-- r equivalence relation on α
-- quotient α / r
-- f : α → β function that respects r, i.e. ∀ x y, r x y → f x = f y
-- f lifts to a f' : α / r → β defined by f ⟦x⟧ = f x

-- Lean's std lib extends the Calculus of Constructions with additional constants that perform
-- exactly these constructions, and installs this last equation as a definitional reduction rule

namespace Hidden

universe u v

-- the quotient construction uses an ordinary binary relation

-- quotient type
axiom Quot : {α : Sort u} → (α → α → Prop) → Sort u

-- element of `Quot r`
axiom Quot.mk : {α : Sort u} → (r : α → α → Prop) → α → Quot r

-- every element of `Quot r` is of the form `Quot.mk r a` for some `a : α`
axiom Quot.ind :
    ∀ {α : Sort u} {r : α → α → Prop} {β : Quot r → Prop},
      (∀ a, β (Quot.mk r a)) →
      (q : Quot r) →
      β q

-- every function that respects the relation `r` can be lifted to a function on `Quot r`
axiom Quot.lift :
    {α : Sort u} → {r : α → α → Prop} → {β : Sort u} →
    (f : α → β) →
    (∀ a b, r a b → f a = f b) →
    Quot r →
    β

end Hidden

-- binary (equivalence) relation
def mod7Rel (x y : Nat) : Prop :=
  x % 7 = y % 7

-- the quotient type
#check (Quot mod7Rel : Type)

-- the class of numbers equivalent to 4
#check (Quot.mk mod7Rel 4 : Quot mod7Rel)

def f (x : Nat) : Bool :=
  x % 7 = 0

theorem f_respects (a b : Nat) (h : mod7Rel a b) : f a = f b := by
  simp [mod7Rel, f] at *
  rw [h]

#check (Quot.lift f f_respects : Quot mod7Rel → Bool)

-- the computation principle
example (a : Nat) : Quot.lift f f_respects (Quot.mk mod7Rel a) = f a := rfl

-- `Quot`, `Quot.mk`, `Quot.ind`, and `Quot.lift` are viewed as part of the logical framework

-- makes `Quot` a bona fida quotient
namespace Hidden

-- any two elements related by `r` become identified in the quotient
axiom Quot.sound :
    ∀ {α : Type u} {r : α → α → Prop} {a b : α},
      r a b → Quot.mk r a = Quot.mk r b

end Hidden

#print axioms funext
-- 'funext' depends on axioms: [Quot.sound]

-- to support quotients by equivalence relations, std lib defines a _setoid_
namespace Hidden

class Setoid (α : Sort u) where
  r : α → α → Prop
  iseqv : Equivalence r

instance {α : Sort u} [s : Setoid α] : HasEquiv α :=
  ⟨s.r⟩

namespace Setoid

variable {α : Sort u} [Setoid α]

theorem refl (a : α) : a ≈ a :=
  iseqv.refl a

theorem symm {a b : α} (hab : a ≈ b) : b ≈ a :=
  iseqv.symm hab

theorem trans {a b c : α} (hab : a ≈ b) (hbc : b ≈ c) : a ≈ c :=
  iseqv.trans hab hbc

end Setoid

-- from an instance of the `Setoid` class, we can make a quotient
def Quotient {α : Sort u} (s : Setoid α) :=
  @Quot α s.r

end Hidden

-- specializations of `Quot` for `Setoid`s

#check Quotient
-- Quotient.{u} {α : Sort u} (s : Setoid α) : Sort u

#check Quotient.mk
-- Quotient.mk.{u} {α : Sort u} (s : Setoid α) (a : α) : Quotient s

#check Quotient.ind
-- Quotient.ind.{u} {α : Sort u} {s : Setoid α} {motive : Quotient s → Prop} :
--   (∀ (a : α), motive (Quotient.mk s a)) → ∀ (q : Quotient s), motive q

#check Quotient.lift
-- Quotient.lift.{u, v} {α : Sort u} {β : Sort v} {s : Setoid α} (f : α → β) :
--   (∀ (a b : α), a ≈ b → f a = f b) → Quotient s → β

#check Quotient.sound
-- Quotient.sound.{u} {α : Sort u} {s : Setoid α} {a b : α} : a ≈ b → Quotient.mk s a = Quotient.mk s b

#check Quotient.exact
-- Quotient.exact.{u} {α : Sort u} {s : Setoid α} {a b : α} : Quotient.mk s a = Quotient.mk s b → a ≈ b

-- Quotient.sound with Quotient.exact imply that the elements of the quotient correspond
-- exactly to the equivalence classes of elements of α

-- example using quotients: _unordered_ pairs

-- equivalence relation on α × α
private def eqv (p₁ p₂ : α × α) : Prop :=
  (p₁.1 = p₂.1 ∧ p₁.2 = p₂.2) ∨ (p₁.1 = p₂.2 ∧ p₁.2 = p₂.1)

infix:50 " ∼ " => eqv

-- `eqv` is an equivalence relation

private theorem eqv.refl (p : α × α) : p ∼ p :=
  Or.inl ⟨rfl, rfl⟩

private theorem eqv.symm : ∀ {a b : α × α}, a ∼ b → b ∼ a
  | (a₁, a₂), (b₁, b₂), Or.inl ⟨a₁b₁, a₂b₂⟩ =>
    Or.inl (by simp_all)
  | (a₁, a₂), (b₁, b₂), Or.inr ⟨a₁b₂, a₂b₁⟩ =>
    Or.inr (by simp_all)

private theorem eqv.trans: ∀ {a b c : α × α}, a ∼ b → b ∼ c → a ∼ c
  | (a₁, a₂), (b₁, b₂), (c₁, c₂), Or.inl ⟨a₁b₁, a₂b₂⟩, Or.inl ⟨b₁c₁, c₂b₂⟩ =>
    Or.inl (by simp_all)
  | (a₁, a₂), (b₁, b₂), (c₁, c₂), Or.inl ⟨a₁b₁, a₂b₂⟩, Or.inr ⟨b₁c₂, c₂b₁⟩ =>
    Or.inr (by simp_all)
  | (a₁, a₂), (b₁, b₂), (c₁, c₂), Or.inr ⟨a₁b₂, a₂b₁⟩, Or.inl ⟨b₁c₁, c₂b₂⟩ =>
    Or.inr (by simp_all)
  | (a₁, a₂), (b₁, b₂), (c₁, c₂), Or.inr ⟨a₁b₂, a₂b₁⟩, Or.inr ⟨b₁c₂, c₂b₁⟩ =>
    Or.inl (by simp_all)

private theorem is_eqv : Equivalence (@eqv α) :=
  { refl := eqv.refl, symm := eqv.symm, trans := eqv.trans }

-- unordered product setoid instance
instance uprodSetoid (α : Type u) : Setoid (α × α) where
  r     := eqv
  iseqv := is_eqv

-- unordered pairs
def UProd (α : Type u) : Type u :=
  Quotient (uprodSetoid α)

namespace UProd

def mk {α : Type u} (a b : α) : UProd α :=
  Quotient.mk' (a, b)

notation "{" a ", " b "}" => mk a b

theorem mk_eq_mk (a b : α) : {a, b} = {b, a} :=
  Quotient.sound <| Or.inr ⟨rfl, rfl⟩

-- define the membership proposition

-- membership function which will be lifted to the quotient
private def mem_fn (a : α) : α × α → Prop
  | (a₁, a₂) => a = a₁ ∨ a = a₂

-- auxiliary lemma for proving `mem_fn` respects the equivalence relation
private theorem mem_swap {a : α} :
    ∀ {p : α × α}, mem_fn a p = mem_fn a ⟨p.2, p.1⟩
  | (p₁, p₂) => by
    apply propext
    apply Iff.intro
    repeat intro
      | Or.inl h => exact Or.inr h
      | Or.inr h => exact Or.inl h

-- `mem_fn` respects the equivalence relation
private theorem mem_respects :
    {p₁ p₂ : α × α} → (a : α) → p₁ ∼ p₂ → mem_fn a p₁ = mem_fn a p₂
  | (a₁, a₂), (b₁, b₂), a, Or.inl ⟨a₁b₁, a₂b₂⟩ => by
    simp_all
  | (a₁, a₂), (b₁, b₂), a, Or.inr ⟨a₁b₂, a₂b₁⟩ => by
    simp_all only
    apply mem_swap

-- membership proposition
def mem (a : α) (u : UProd α) : Prop :=
  Quotient.liftOn u (fun p => mem_fn a p) (fun _ _ e => mem_respects a e)

infix:50 (priority := high) "∈" => mem

theorem mem_mk_left (a b : α) : a ∈ {a, b} :=
  Or.inl rfl  -- a = a

theorem mem_mk_right (a b : α) : b ∈ {a, b} :=
  Or.inr rfl  -- b = b

theorem mem_or_mem_of_mem_mk {a b c : α} : c ∈ {a, b} → c = a ∨ c = b := id

end UProd

-- lifts a binary function
#check Quotient.lift₂

-- induction on two variables
#check Quotient.ind₂

-- hints why quotient construction implies function extensionality

-- extensional equality on `(x : α) → β x` is an equivalence relation
-- so we can consider the type `extfun α β` of functions "up to equivalence"
-- application respects this equivalence since if `f₁ ≈ f₂` then `f₁ a = f₂ a`
-- consider `extfun_app : extfun α β → (x : α) → β x` which respects this equivalence
-- lift `extfun_app

def extfun (α : Sort u) (β : α → Sort v) :=
  Quot (fun (f g : (x : α) → β x) => ∀ x, f x = g x)

def extfun_app {α β} (f : extfun α β) (x : α) : β x :=
  Quot.lift (· x) (by intros; simp [*]) f

variable {α : Sort u} {β : α → Sort v}
example (f₁ f₂ : (x : α) → β x) (h : ∀ x, f₁ x = f₂ x) :=
  calc f₁
    _ = extfun_app (.mk _ f₁) := rfl
    _ = extfun_app (.mk _ f₂) := by rw [Quot.sound]; trivial
    _ = f₂ := rfl

-- 12.5 Choice

-- to state the final axiom in the std lib, we need the `Nonempty` type
namespace Hidden

class inductive Nonempty (α : Sort u) : Prop where
  | intro (val : α) : Nonempty α

-- because `Nonempty α` has type `Prop` and its constructor contains data,
-- it can only eliminate to `Prop`

-- `Nonempty α` is equivalent to `∃ x : α, True`
example (α : Sort u) : Nonempty α ↔ ∃ _ : α, True := by
  apply Iff.intro
  . exact fun (.intro val) => ⟨val, trivial⟩
  . exact fun ⟨a, _⟩ => .intro a

-- axiom of choice: magically produces an element of a nonempty type
axiom choice {α : Sort u} : Nonempty α → α

-- in `Classical` namespace

-- axiom of choice is equivalent to the principle of indefinite description
noncomputable def indefiniteDescription {α : Sort u}
    (p : α → Prop) (h : ∃ x, p x) : { x // p x } :=
  choice <| let ⟨x, px⟩ := h; ⟨⟨x, px⟩⟩

-- Lean cannot generate executable code for `indefiniteDescription`

-- functions in `Classical` for decomposing the output of `indefiniteDescription`
variable {α : Sort u} {p : α → Prop}

noncomputable def choose (h : ∃ x : α, p x) : α :=
  (indefiniteDescription p h).val

theorem choose_spec (h : ∃ x : α, p x) : p (choose h) :=
  (indefiniteDescription p h).property

-- `choice` erases the distinction between `Nonempty α` and `Inhabited α`
@[instance_reducible] noncomputable def inhabited_of_nonempty (h : Nonempty α) : Inhabited α :=
  ⟨choice h⟩

end Hidden

-- `propext`, `funext`, and `choice` taken together imply the law of the excluded middle
-- and the decidability of all propositions
-- using those we can strengthen the principle of indefinite description

open Classical (strongIndefiniteDescription)
#check strongIndefiniteDescription
-- strongIndefiniteDescription.{u}
--   {α : Sort u} (p : α → Prop) (h : Nonempty α)
--   : { x // (∃ y, p y) → p x }

-- the data component of this definition is known as Hilbert's epsilon function
noncomputable def epsilon {α : Sort u} [h : Nonempty α] (p : α → Prop) : α :=
  (strongIndefiniteDescription p h).val

theorem epsilon_spec {α : Sort u} {p : α → Prop} (h : ∃ y : α, p y)
    : p (@epsilon _ h.nonempty p) :=
  (strongIndefiniteDescription p h.nonempty).property h

-- 12.6 The Law of the Excluded Middle

-- law of the excluded middle
#check Classical.em
-- Classical.em (p : Prop) : p ∨ ¬p

-- Diaconescu's theorem states that the axiom of choice implies the law of the excluded middle

open Classical (choose choose_spec) in
theorem em (p : Prop) : p ∨ ¬p := by
  let U (x : Prop) : Prop := x = True ∨ p
  let V (x : Prop) : Prop := x = False ∨ p
  have exU : ∃ x, U x := ⟨True, Or.inl rfl⟩
  have exV : ∃ x, V x := ⟨False, Or.inl rfl⟩
  -- if p is true, then every element in Prop is in U and V
  -- if p is false, then U = {True} and V = {False}
  let u : Prop := choose exU
  let v : Prop := choose exV
  have u_def : U u := choose_spec exU
  have v_def : V v := choose_spec exV
  -- each of U and V are disjunct, so u_def and v_def represent four cases
  have not_uv_or_p : u ≠ v ∨ p := by
    match u_def, v_def with
    | .inr h, _ => exact .inr h
    | _, .inr h => exact .inr h
    | .inl hu, .inl hv =>
      apply Or.inl
      simp [hu, hv]
  -- if p is true, by function extensionality and propositional extensionality, then U = V
  have p_implies_uv : p → u = v :=
    fun hp =>
    have hpred : U = V :=
      funext fun x =>
        have hl : (x = True ∨ p) → (x = False ∨ p) :=
          fun _ => .inr hp
        have hr : (x = False ∨ p) → (x = True ∨ p) :=
          fun _ => .inr hp
        show (x = True ∨ p) = (x = False ∨ p) from
          propext <| Iff.intro hl hr
    -- thus u = v
    have h₀ : ∀ exU exV, @choose _ U exU = @choose _ V exV := by
      rw [hpred]; intros; rfl
    show u = v by apply h₀
  show p ∨ ¬p
  match not_uv_or_p with
  | .inl hne => exact .inr (mt p_implies_uv hne)
  | .inr hp => exact .inl hp

-- law of excluded middle implies:
-- - double-negation elimination
-- - proof by cases
-- - proof by contradiction

-- law of exlcuded middle and propositional extensionality imply propositional completeness
theorem propComplete (p : Prop) : p = True ∨ p = False :=
  match em p with
  | .inl hp =>
    .inl (propext <| Iff.intro (fun _ => True.intro) (fun _ => hp))
  | .inr hnp =>
    .inr (propext <| Iff.intro hnp False.elim)

#check Classical.propDecidable
-- Classical.propDecidable (a : Prop) : Decidable a

noncomputable def propDecidable (p : Prop) : Decidable p :=
  Classical.choice <| match em p with
    | .inl hp => ⟨isTrue hp⟩
    | .inr hnp => ⟨isFalse hnp⟩

-- `p ∨ ¬p` can only eliminate to `Prop` but the type `Decidable p` is equivalent to the
-- sum type `Sum p ¬p` which can eliminate to any type

-- example of classical reasoning:
-- if `f : α → β` is injective and `α` is inhabited, then `f` has a left inverse

open Classical

set_option linter.defProp false
noncomputable def leftInv {α β} [Inhabited α] (f : α → β) : β → α :=
  fun b => if ex : (∃ a : α, f a = b) then choose ex else default

theorem leftInv_comp_self {α β} {f : α → β} [Inhabited α]
    (inj : ∀ {a b}, f a = f b → a = b)
    : leftInv f ∘ f = id :=
  funext fun a =>
    have ex : ∃ a₁ : α, f a₁ = f a := ⟨a, rfl⟩
    have feq : f (choose ex) = f a := choose_spec ex
    calc leftInv f (f a)
      _ = choose ex := rfl
      _ = a         := inj feq

-- classically `leftInv f` is a function, but not constructively
