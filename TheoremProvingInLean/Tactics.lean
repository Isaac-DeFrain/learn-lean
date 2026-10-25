/- 5. Tactics -/

-- tactic-style proof vs. term-style proof

-- 5.1 Entering Tactic Mode

-- the following theorem has this goal:
-- p	:	Prop
-- q	:	Prop
-- hp	:	p
-- hq	:	q
-- ⊢ p ∧ q ∧ p

-- term-style
example (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p :=
  And.intro hp (And.intro hq hp)

-- tactic-style
theorem test (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p := by
  apply And.intro
  exact hp
  apply And.intro
  exact hq
  exact hp

-- ctrl+shift+enter for info view
#print test

-- more concise
example (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p := by
  apply And.intro hp
  apply And.intro hq hp

-- multiple tactics on single line
example (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p := by
  apply And.intro hp; exact And.intro hq hp

-- structured
example (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p := by
  apply And.intro
  case right =>
    apply And.intro
    case left => exact hq
    case right => exact hp
  case left => exact hp

-- bullet notation
example (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p := by
  apply And.intro
  . exact hp
  . apply And.intro hq; exact hp

-- 5.2 Basic Tactics

-- intro tactic introduces a hypothesis

example (p q r: Prop) : p ∧ (q  ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by
  apply Iff.intro
  . intro h
    apply h.right.elim
    . intro hq
      apply Or.inl
      apply And.intro
      . exact h.left
      . exact hq
    . intro hr
      apply Or.inr
      apply And.intro
      . exact h.left
      . exact hr
  . intro h
    apply h.elim
    . intro hpq
      apply And.intro
      . exact hpq.left
      . apply Or.inl
        exact hpq.right
    . intro hpr
      apply And.intro
      . exact hpr.left
      . apply Or.inr
        exact hpr.right

-- intro can introduce a variable of any type

example (α : Type) : α → α := by
  intro a; exact a

example (α : Type) : ∀ x : α, x = x := by
  intro a
  exact Eq.refl a

example : ∀ a b c : Nat, a = b → a = c → c = b := by
  intro a b c h₁ h₂
  exact Eq.trans (Eq.symm h₂) h₁

-- apply tactic constructs function applications interactively
-- intro tactic constructs function abstractions interactively

-- intro allows using implicit match

example (p q : α → Prop) : (∃ x, p x ∧ q x) → ∃ x, q x ∧ p x := by
  intro ⟨ w, hpw, hqw ⟩
  exact ⟨ w, hqw, hpw ⟩

example (p q : α → Prop) : (∃ x, p x ∨ q x) → ∃ x, q x ∨ p x := by
  intro
  | ⟨w, Or.inl h⟩ => exact ⟨w, Or.inr h⟩
  | ⟨w, Or.inr h⟩ => exact ⟨w, Or.inl h⟩

-- assumption tactic looks through the assumptions in context of the current goal,
-- and if one matches the conclusion, it applies it

example (x y z w : Nat) (h₁ : x = y) (h₂ : y = z) (h₃ : z = w) : x = w := by
  apply Eq.trans h₁
  apply Eq.trans h₂
  assumption  -- applied h₃

-- assumption unifies metavariables in the conclusion if needed

example (x y z w : Nat) (h₁ : x = y) (h₂ : y = z) (h₃ : z = w) : x = w := by
  apply Eq.trans
  assumption      -- solves x = ?b with h₁
  apply Eq.trans
  assumption      -- solves y = ?h₂.b with h₂
  assumption      -- solves z = w with h₃

-- intros tactic

example : ∀ a b c : Nat, a = b → a = c → c = b := by
  intros
  apply Eq.trans
  apply Eq.symm
  assumption
  assumption

-- unhygienic makes inaccessible names accessible

example : ∀ a b c : Nat, a = b → a = c → c = b := by unhygienic
  intros
  apply Eq.trans
  apply Eq.symm
  exact a_2
  exact a_1

-- rename_i renames the most recent inaccessible names

example : ∀ a b c : Nat, a = b → a = c → c = b := by
  intros
  rename_i _ _ _ h1 h2
  apply Eq.trans
  apply Eq.symm
  exact h2
  exact h1

-- rfl tactic solves goals that are reflexive relations applied to definitionally equal arguments

example (y : Nat) : (fun _ => 0) y = 0 := by
  rfl

-- repeat combinator applies a tactic several times

example : ∀ a b c : Nat, a = b → a = c → c = b := by
  intros
  apply Eq.trans
  apply Eq.symm
  repeat assumption

-- revert tactic is an inverse to intro

example (x : Nat) : x = x := by
  revert x
  intro y
  rfl

example (x y : Nat) (h : x = y) : y = x := by
  revert h
  intro h₁
  -- goal is x y : Nat, h₁ : x = y ⊢ y = x
  apply Eq.symm
  assumption

example (x y : Nat) (h : x = y) : y = x := by
  revert x      -- reverts all subsequent elements that depend on x
  intros
  apply Eq.symm
  assumption

example (x y : Nat) (h : x = y) : y = x := by
  revert x y
  intros
  apply Eq.symm
  assumption

-- generalize

example : 3 = 3 := by
  generalize 3 = x  -- x : Nat ⊢ x = x
  revert x          -- ∀ x : Nat, x = x
  intros            -- y : Nat ⊢ y = y
  rfl

example : 2 + 3 = 5 := by
  generalize h : 3 = x
  rw [← h]

-- 5.3 More Tactics

-- cases tactic can be used to decompose disjunctions

example (p q : Prop) : p ∨ q → q ∨ p := by
  intro h
  cases h with
  | inl hp => apply Or.inr; exact hp
  | inr hq => apply Or.inl; exact hq

-- structured cases

example (p q : Prop) : p ∨ q → q ∨ p := by
  intro h
  cases h
  . apply Or.inr
    assumption
  . apply Or.inl
    assumption

-- unstructured cases

example (p : Prop) : p ∨ p → p := by
  intro h
  cases h
  repeat assumption

-- <;> combinator
-- tac1 <;> tac2 applies tac2 to each subgoal produced by tac1

example (p : Prop) : p ∨ p → p := by
  intro h
  cases h <;> assumption

-- cases tactic can be used to decompose a conjunction

example (p q : Prop) : p ∧ q → q ∧ p := by
  intro h
  cases h
  . constructor <;> assumption

-- rewriting a previous example

example (p q r : Prop) : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by
  apply Iff.intro
  . intro h
    cases h with
    | intro hp hqr =>
      cases hqr
      . apply Or.inl; constructor <;> assumption
      . apply Or.inr; constructor <;> assumption
  . intro h
    cases h with
    | inl hpq =>
      cases hpq with
      | intro hp hq =>
        constructor; assumption; apply Or.inl; assumption
    | inr hpr =>
      cases hpr with
      | intro hp hr =>
        constructor; assumption; apply Or.inr; assumption

-- cases can decompose any element of an inductively defined type

example (p q : Nat → Prop) : (∃ x, p x) → ∃ x, p x ∨ q x := by
  intro h
  cases h
  . constructor; apply Or.inl; assumption

-- exists tactic

example (p q : Nat → Prop) : (∃ x, p x) → ∃ x, p x ∨ q x := by
  intro h
  cases h with
  | intro x px => exists x; apply Or.inl; exact px

example (p q : Nat → Prop) : (∃ x, p x ∧ q x) → ∃ x, q x ∧ p x := by
  intro h
  cases h with
  | intro x hpq =>
    cases hpq with
    | intro hp hq =>
      exists x

-- tactics can be used on data just as on propositions

def swap_pair : α × β → β × α := by
  intro p
  cases p
  constructor <;> assumption

def swap_sum : Sum α β → Sum β α := by
  intro p
  cases p
  . apply Sum.inr; assumption
  . apply Sum.inl; assumption

-- case distinction on natural number

example (P : Nat → Prop)
    (h₀ : P 0) (h₁ : ∀ n, P (Nat.succ n))
    (m : Nat) : P m := by
  cases m
  . exact h₀
  . apply h₁

-- contradicition tactic searches for a contradiciton among the hypotheses

example (p q : Prop) : p ∧ ¬ p → q := by
  intro h
  cases h
  contradiction

-- match can be used in blocks

example (p q r : Prop) : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by
  apply Iff.intro
  . intro h
    match h with
    | ⟨_, Or.inl _⟩ =>
      apply Or.inl; constructor <;> assumption
    | ⟨_, Or.inr _⟩ =>
      apply Or.inr; constructor <;> assumption
  . intro h
    match h with
    | Or.inl ⟨hp, hq⟩ =>
      constructor; exact hp; apply Or.inl; exact hq
    | Or.inr ⟨hp, hr⟩ =>
      constructor; exact hp; apply Or.inr; exact hr

-- can "combine" intro and match

example (p q r : Prop) : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by
  apply Iff.intro
  . intro
    | ⟨_, Or.inl _⟩ =>
      apply Or.inl; constructor <;> assumption
    | ⟨_, Or.inr _⟩ =>
      apply Or.inr; constructor <;> assumption
  . intro
    | Or.inl ⟨hp, hq⟩ =>
      constructor; exact hp; apply Or.inl; exact hq
    | Or.inr ⟨hp, hr⟩ =>
      constructor; exact hp; apply Or.inr; exact hr

-- 5.4 Structuring Tactic Proofs

-- can freely mix term- and tactic-style proofs

example (p q r : Prop) : p ∧ (q ∨ r) → (p ∧ q) ∨ (p ∧ r) := by
  intro h
  exact
    have hp : p := h.left
    have hqr : q ∨ r := h.right
    by
      cases hqr with
      | inl hq => exact Or.inl ⟨hp, hq⟩
      | inr hr => exact Or.inr ⟨hp, hr⟩

-- show tactic declares the type of the goal that is about to be solved

example (p q r : Prop) : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by
  apply Iff.intro
  . intro h
    cases h.right with
    | inl hq =>
      show (p ∧ q) ∨ (p ∧ r)
      exact Or.inl ⟨h.left, hq⟩
    | inr hr =>
      show (p ∧ q) ∨ (p ∧ r)
      exact Or.inr ⟨h.left, hr⟩
  . intro
    | Or.inl hpq =>
      show p ∧ (q ∨ r)
      exact ⟨hpq.left, Or.inl hpq.right⟩
    | Or.inr hpr =>
      show p ∧ (q ∨ r)
      exact ⟨hpr.left, Or.inr hpr.right⟩

-- show tactic can be used to rewrite a goal to something definitionally equivalent

example (n : Nat) : n + 1 = Nat.succ n := by
  show Nat.succ n = Nat.succ n
  rfl

-- have tactic introduces a new subgoal

example (p q r : Prop) : p ∧ (q ∨ r) → (p ∧ q) ∨ (p ∧ r) := by
  intro ⟨hp, hqr⟩
  cases hqr with
  | inl hq =>
    have : p ∧ q := ⟨ hp, hq ⟩
    apply Or.inl
    exact this
  | inr hr =>
    have : p ∧ r := ⟨ hp, hr ⟩
    apply Or.inr
    exact this

-- can omit type and label from have tactic

example (p q r : Prop) : p ∧ (q ∨ r) → (p ∧ q) ∨ (p ∧ r) := by
  intro ⟨hp, hqr⟩
  cases hqr with
  | inl hq =>
    have := And.intro hp hq
    exact Or.inl this
  | inr hr =>
    have := And.intro hp hr
    exact Or.inr this

-- let tactic introduces local definitions

example : ∃ x, x + 2 = 8 := by
  let w := 6
  exists w

-- can use curly braces to nest blocks

example (p q r : Prop) : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by
  apply Iff.intro
  { intro h
    cases h.right
    . exact Or.inl ⟨h.left, ‹q›⟩
    . exact Or.inr ⟨h.left, ‹r›⟩ }
  . intro h
    cases h
    { rename_i hpq
      exact ⟨hpq.left, Or.inl hpq.right⟩ }
    { rename_i hpr
      exact ⟨hpr.left, Or.inr hpr.right⟩ }

-- if the application of theorem foo to a single goal produces four subgoals,
-- one would expect the proof to look like this:
--
--   apply foo
--   . <proof of first goal>
--   . <proof of second goal>
--   . <proof of third goal>
--   . <proof of final goal>
-- or
--
--   apply foo
--   case <tag of first goal>  => <proof of first goal>
--   case <tag of second goal> => <proof of second goal>
--   case <tag of third goal>  => <proof of third goal>
--   case <tag of final goal>  => <proof of final goal>
-- or
--
--   apply foo
--   { <proof of first goal>  }
--   { <proof of second goal> }
--   { <proof of third goal>  }
--   { <proof of final goal>  }

-- 5.5 Tactic Combinators

-- ; sequencing combinator
-- t₁; t₂ applies t₁, then t₂

example (p q : Prop) (hp : p) : p ∨ q := by
  apply Or.inl; assumption

-- by block implicitly sequences

example (p q : Prop) (hp : p) : p ∨ q := by
  apply Or.inl
  assumption

-- <;> parallel sequencing combinator
-- t₁ <;> t₂ applies t₁ to the main goal and t₂ to all resulting subgoals

example (p q : Prop) (hp : p) (hq : q) : p ∧ q := by
  constructor <;> assumption

-- first | t₁ | t₂ | ... | tₙ applies each tᵢ until one succeeds, or else fails

example (p q : Prop) (hp : p) : p ∨ q := by
  first
  | apply Or.inr; assumption  -- fails
  | apply Or.inl; assumption  -- succeeds

example (p q : Prop) (hq : q) : p ∨ q := by
  first
  | apply Or.inr; assumption  -- succeeds
  | apply Or.inl; assumption

-- The following tactics try to solve the left disjunct immediately by assumption;
-- if that fails, it tries to focus on the right disjunct; and if that doesn't work,
-- it invokes the assumption tactic.

example (p q r : Prop) (hp : p) : p ∨ q ∨ r := by
  repeat (first | apply Or.inl; assumption | apply Or.inr | assumption)

example (p q r : Prop) (hq : q) : p ∨ q ∨ r := by
  repeat (first | apply Or.inl; assumption | apply Or.inr | assumption)

example (p q r : Prop) (hr : r) : p ∨ q ∨ r := by
  repeat (first | apply Or.inl; assumption | apply Or.inr | assumption)

example (p q r : Prop) (hp : p) (hq : q) (hr : r) : p ∧ q ∧ r := by
  constructor <;> repeat (first | constructor | assumption)

-- try combinator builds a tactic that always succeeds
-- try t executes t and rports success even if t fails
-- try t := first | t | skip where is a tactic that does nothing (and succeeds)

example (p q r : Prop) (hp : p) (hq : q) (hr : r) : p ∧ q ∧ r := by
  constructor           -- creates two subgoals: left, right
  <;> (try constructor) -- constructor creates two subgoals on right: right.left, right.right; "fails" on left
  <;> assumption        -- solves all subgoals

-- repeat (try t will loop forever because try t never fails

-- all_goals t applies tactic t to all open goals

example (p q r : Prop) (hp : p) (hq : q) (hr : r) : p ∧ q ∧ r := by
  constructor
  all_goals (try constructor)
  all_goals assumption

-- any_goals t succeeds if t applies successfully to at least one subgoal

example (p q r : Prop) (hp : p) (hq : q) (hr : r) : p ∧ q ∧ r := by
  constructor
  any_goals (try constructor)
  any_goals assumption

example (p q r : Prop) (hp : p) (hq : q) (hr : r) :
      p ∧ ((p ∧ q) ∧ r) ∧ (q ∧ r ∧ p) := by
  repeat (any_goals constructor)  -- repeatedly splits conjunctions
  all_goals assumption

example (p q r : Prop) (hp : p) (hq : q) (hr : r) :
      p ∧ ((p ∧ q) ∧ r) ∧ (q ∧ r ∧ p) := by
  repeat (any_goals (first | constructor | assumption))

-- focus t ensures that t only effects the current goal

-- 5.6 Rewriting

-- rw [t] where t is a term whose type asserts an equality

example (k : Nat) (f : Nat → Nat) (h₁ : f 0 = 0) (h₂ : k = 0) : f k = 0 := by
  rw [h₂] -- rewrites goal to: f 0 = 0
  exact h₁

-- term-style
example (k : Nat) (f : Nat → Nat) (h₁ : f 0 = 0) (h₂ : k = 0) : f k = 0 :=
  h₂ ▸ h₁

-- rw on compound expression
example (x y : Nat) (p : Nat → Prop) (q : Prop) (h : q → x = y)
        (h' : p y) (hq : q) : p x := by
  rw [h hq] -- rewrites goal to: p y
  exact h'

-- rw [t] uses an equation in the forward direction by default
-- ←t can be used to instruct the rewrite to use the reverse direction

example (a b : Nat) (f : Nat → Nat) (h₁ : a = b) (h₂ : f a = 0) : f b = 0 := by
  rw [←h₁]  -- replaces b with a in goal to get: f a = 0
  exact h₂

-- when LHS of an identity matches more than one subterm in the pattern,
-- rw tactic chooses the first match it finds when traversing the term
-- additional arguments can be provided to specify the appropriate term

example (a b c : Nat) : a + b + c = a + c + b := by
  rw [Nat.add_assoc]    -- goal: a + (b + c) = a + c + b
  rw [Nat.add_comm b]   -- goal: a + (c + b) = a + c + b
  rw [← Nat.add_assoc]  -- uses the reverse direction to solve the goal

example (a b c : Nat) : a + b + c = a + c + b := by
  rw [Nat.add_assoc]    -- goal: a + (b + c) = a + c + b
  rw [Nat.add_assoc]    -- goal: a + (b + c) = a + (c + b)
  rw [Nat.add_comm b]   -- goal: a + (c + b) = a + (c + b) and solves it via rfl

example (a b c : Nat) : a + b + c = a + c + b := by
  rw [Nat.add_assoc, Nat.add_assoc]
  rw [Nat.add_comm _ b] -- specifies rewrite should take place on the RHS

-- rewriting a hypothesis

example (f : Nat → Nat) (a : Nat) (h : a + 0 = 0) : f a = f 0 := by
  rw [Nat.add_zero] at h  -- rewrites h to: a = 0
  rw [h]                  -- solves the goal with h : a = 0 via rfl

-- rw is not restricted to propositions

def Tuple (α : Type) (n : Nat) :=
  { as : List α // as.length = n }

example (n : Nat) (h : n = 0) (t : Tuple α n) : Tuple α 0 := by
  rw [h] at t
  exact t

-- 5.7 Using the Simplifier

-- simp tactic uses Lean identities tagged with the [simp] attribute to iteratively rewrite

example (x y z : Nat) : (x + 0) * (0 + y * 1 + z * 0) = x * y := by
  simp

example (x y z : Nat) (p : Nat → Prop) (h : p (x * y))
        : p ((x + 0) * (0 + y * 1 + z * 0)) := by
  simp; exact h

section ListExamples
  open List

  example (xs : List Nat)
          : reverse (xs ++ [1, 2, 3]) = [3, 2, 1] ++ reverse xs := by
    simp

  example (xs ys : List α)
          : length (reverse (xs ++ ys)) = length xs + length ys := by
    simp [Nat.add_comm]
end ListExamples

-- simp at h simplifies hypothesis h

example (x y z : Nat) (p : Nat → Prop)
        (h : p ((x + 0) * (0 + y * 1 + z * 0))) : p (x * y) := by
  simp at h; assumption

-- can use "wildcard" * to simplify all hypotheses and the goal

section
  attribute [local simp] Nat.mul_comm Nat.mul_assoc Nat.mul_left_comm
  attribute [local simp] Nat.add_assoc Nat.add_comm Nat.add_left_comm

  example (w x y z : Nat) (p : Nat → Prop)
          (h : p (x * y + z * w * x)) : p (x * w * z + y * x) := by
    simp at *; assumption

  example (x y z : Nat) (p : Nat → Prop)
          (h₁ : p (1 * x + y)) (h₂ : p (x * z * 1))
          : p (y + 0 + x) ∧ p (z * x) := by
    simp at *; constructor <;> assumption
end

-- can supply a list of terms to simp

def f (m n : Nat) : Nat :=
  m + n + m

example (h : 0 = m) : f m n = n := by
  simp [←h, f]

-- simplify with all hypotheses present in the local context

example (k : Nat) (f : Nat → Nat) (h₁ : f 0 = 0) (h₂ : k = 0) : f k = 0 := by
  simp [*]  -- simp [h₁, h₂]

example (u w x y z : Nat) (h₁ : x = y + z) (h₂ : w = u + x)
        : w = z + y + u := by
  simp [*, Nat.add_comm]

-- simplifier can do propositional reasoning

example (p q : Prop) (hp : p) : p ∧ q ↔ q := by
  simp [*]  -- rewrites p ∧ q to q using hp

example (p q : Prop) (hp : p) : p ∨ q := by
  simp [*]  -- rewrites p ∨ q to True using hp

example (p q r : Prop) (hp : p) (hq : q) : p ∧ (q ∨ r) := by
  simp [*]

example (x x' y y' : Nat) (p : Nat → Prop)
        (h₁ : x + 0 = x') (h₂ : y + 0 = y')
        : p (x + y + 0) = p (x' + y') := by
  simp at * -- rewrites goal and hypotheses
  simp [*]  -- solves goal with the rewritten hypotheses

-- simplifier capabilities grow with a library

def mk_symm (xs : List α) :=
  xs ++ xs.reverse

@[simp] theorem reverse_mk_symm (xs : List α)
    : (mk_symm xs).reverse = mk_symm xs := by
  simp [mk_symm]

-- equivalently, we can write instead:
-- attribute [simp] reverse_mk_symm

example (xs ys : List Nat)
    : (xs ++ mk_symm ys).reverse = mk_symm ys ++ xs.reverse := by
  simp  -- uses reverse_mk_symm

example (xs ys : List Nat) (p : List Nat → Prop)
    (h : p (xs ++ mk_symm ys).reverse)
    : p (mk_symm ys ++ xs.reverse) := by
  simp at h -- uses reverse_mk_symm
  assumption

-- simp uses all [simp] theorems by default

example (xs ys : List Nat) (p : List Nat → Prop)
        (h : p (xs ++ mk_symm ys).reverse)
        : p ((mk_symm ys).reverse ++ xs.reverse) := by
  simp [-reverse_mk_symm] at h  -- does not use reverse_mk_symm
  assumption

example (xs ys : List Nat) (p : List Nat → Prop)
        (h : p (xs ++ mk_symm ys).reverse)
        : p ((mk_symm ys).reverse ++ xs.reverse) := by
  simp only [List.reverse_append] at h  -- excludes [simp] theorems
  assumption

-- simp configuration options

example : if x = 0 then y + x = y else x ≠ 0 := by
  simp +contextual  -- uses x = 0 when simplifying y + x = y and x ≠ 0

example : 0 < 1 + x ∧ x + y + 2 ≥ y + 1 := by
  simp +arith

-- 5.8 Split Tactic

-- split tactic generates subgoals for ite and match expressions

def f' (x y z : Nat) : Nat :=
  match x, y, z with
  | 5, _, _ => y
  | _, 5, _ => y
  | _, _, 5 => y
  | _, _, _ => 1

example (x y z : Nat) : x ≠ 5 → y ≠ 5 → z ≠ 5 → z = w → f' x y w = 1 := by
  intros
  simp [f']
  split
  . contradiction
  . contradiction
  . contradiction
  . rfl

-- equivalently

example (x y z : Nat) : x ≠ 5 → y ≠ 5 → z ≠ 5 → z = w → f' x y w = 1 := by
  intros; simp [f']; split <;> first | contradiction | rfl

-- split at h applies split to the hypothesis h

def g (xs ys : List Nat) : Nat :=
  match xs, ys with
  | [a, b], _ => a + b + 1
  | _, [b, _] => b + 1
  | _, _      => 1

example (xs ys : List Nat) (h : g xs ys = 0) : False := by
  simp [g] at h; split at h <;> simp +arith at h

-- 5.9 Extensible Tactics

-- define a new tactic `triv` which simply applies assumption
syntax "triv" : tactic

macro_rules
  | `(tactic| triv) => `(tactic| assumption)

example (hp : p) : p := by triv

-- cannot prove with `triv`
-- example (x : α) : x = x := by triv

-- extend `triv` to also use rfl
macro_rules
  | `(tactic| triv) => `(tactic| rfl)

-- now we can prove with `triv`
example (x : α) : x = x := by triv

-- cannot prove with `triv`
-- example (x : α) (h : p) : x = x ∧ p := by triv

-- add a recursive extension
macro_rules
  | `(tactic| triv) => `(tactic| apply And.intro <;> triv)

example (x : α) (h : p) : x = x ∧ p := by triv

-- 5.10 Exercises

-- 1. revisit previous exercises

-- 2. Use tactic combinators to obtain a one-line proof of the following:
example (p q r : Prop) (hp : p) : (p ∨ q ∨ r) ∧ (q ∨ p ∨ r) ∧ (q ∨ r ∨ p) := by
  constructor <;> first | apply Or.inl; assumption | constructor <;> simp [*]
