/- 11. The Conversion Tactic Mode -/

-- conv tactic allows us to travel inside assumptions and goals, even inside function
-- abstraction and dependent arrows to apply rewriting or simplfying steps

-- 11.1 Basic Navigation and Rewriting

/--
error: unsolved goals
a b c : Nat
⊢ b * c * a = a * (c * b)
-/
#guard_msgs (error) in
example (a b c : Nat) : a * (b * c) = a * (c * b) := by
  rw [Nat.mul_comm] -- applies Nat.mul_comm to first multiplication

example (a b c : Nat) : a * (b * c) = a * (c * b) := by
  conv =>
  -- a : Nat
  -- b : Nat
  -- c : Nat
  -- | a * (b * c) = a * (c * b)
    lhs
    -- a : Nat
    -- b : Nat
    -- c : Nat
    -- | a * (b * c)
    congr
    -- case a
    -- a : Nat
    -- b : Nat
    -- c : Nat
    -- | a
    rfl
    -- case a
    -- a : Nat
    -- b : Nat
    -- c : Nat
    -- | b * c
    rw [Nat.mul_comm]

-- `lhs` navigates to LHS (there is alos `rhs`)
-- `congr` creates as many targets as there are (nondependent and explicit) arguments to the head function

-- rewrite under binders
example : (fun x : Nat => 0 + x) = (fun x => x) := by
  conv =>
    lhs
    intro
    rw [Nat.zero_add]

-- `intro` is the navigates inside the `fun` binder

-- can also use function extensionality
example : (fun x : Nat => 0 + x) = (fun x => x) := by
  funext; rw [Nat.zero_add]

-- or just simp
example : (fun x : Nat => 0 + x) = (fun x => x) := by
  simp

-- 11.2 Pattern Matching

example (a b c : Nat) : a * (b * c) = a * (c * b) := by
  conv in b * c =>
    rw [Nat.mul_comm]

-- equivalently
example (a b c : Nat) : a * (b * c) = a * (c * b) := by
  conv =>
    pattern _ * c
    rw [Nat.mul_comm]

-- 11.3 Structuring Conversion Tactics

example (a b c : Nat) : (0 + a) * (b * c) = a * (c * b) := by
  conv =>
    lhs
    congr
    { rw [Nat.zero_add] }
    . rw [Nat.mul_comm]

-- 11.4 Other Tactics inside Conversion Mode

-- `arg i` enters the i-th nondependent explicit argument

example (a b c : Nat) : a * (b * c) = a * (c * b) := by
  conv =>
    lhs
    arg 2
    rw [Nat.mul_comm]

-- `args` is an alternative name for `congr`
-- `simp` applies the simplifier to the current goal; same options as regular tactic mode

def f (x : Nat) :=
  if x > 0 then x + 1 else x + 2

example (g : Nat → Nat)
    (h₁ : g x = x + 1) (h₂ : x > 0) :
    g x = f x := by
  conv =>
    rhs
    simp [f, h₂]
  exact h₁

-- `enter [1, x, 2, y]` iterates `arg` and `intro` with the given arguments
-- `done` fails if there are unsolved goals
-- `trace_state` displays the current tactic state
-- `whnf` puts term in weak head normal form
-- `tactic => <tactic sequence>` goes back to regular tactic mode

example (g : Nat → Nat → Nat)
    (h₁ : ∀ x, x ≠ 0 → g x x = 1)
    (h₂ : x ≠ 0)
    : g x x + x = 1 + x := by
  conv =>
    lhs
    arg 1
    rw [h₁]
    . skip
    . tactic =>
       exact h₂

-- `apply <term>` is syntax sugar for `tactic => apply <term>`

example (g : Nat → Nat → Nat)
    (h₁ : ∀ x, x ≠ 0 → g x x = 1)
    (h₂ : x ≠ 0)
    : g x x + x = 1 + x := by
  conv =>
    lhs
    arg 1
    rw [h₁]
    . skip
    . apply h₂
