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

-- repeat applies a tactic several times

example : ∀ a b c : Nat, a = b → a = c → c = b := by
  intros
  apply Eq.trans
  apply Eq.symm
  repeat assumption

-- revert is an inverse to intro

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
  intros
  rfl

example : 2 + 3 = 5 := by
  generalize h : 3 = x
  rw [← h]

-- 5.3 More Tactics
