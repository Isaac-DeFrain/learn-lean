/- 8. Induction and Recursion -/

-- induction is the fundamental method of proof

-- define a function by specifying equations it should satisfy
-- prove a theorem by specifying how to handle various cases
-- these descriptions are "compiled" down to primitive recursors by the equation compiler

-- 8.1. Pattern Matching

-- casesOn recursor

def pred : Nat → Nat
  | .zero   => .zero
  | .succ x => x

def isZero : Nat → Bool
  | .zero   => true
  | .succ _ => false

-- equations hold definitionally

example : pred 0 = 0 := rfl
example (x : Nat) : pred x.succ = x := rfl

example : isZero 0 = true := rfl
example (x : Nat) : isZero x.succ = false := rfl

example : pred 7 = 6 := rfl
example (x : Nat) : isZero (x + 3) = false := rfl

-- can use + and 0 since they are [match_pattern]

def pred' : Nat → Nat
  | 0     => 0
  | x + 1 => x

def isZero' : Nat → Bool
  | 0     => true
  | _ + 1 => false

-- pattern matching works on any inductive type

namespace Hidden
def not : Bool → Bool
  | true  => false
  | false => true

theorem not_not : ∀ (b : Bool), not (not b) = b
  | true  => show not (not true) = true from rfl
  | false => show not (not false) = false from rfl
end Hidden

-- can be used to destruct inductively defined propositions

example (p q : Prop) : p ∧ q → q ∧ p
  | .intro h₁ h₂ => .intro h₂ h₁

example (p q : Prop) : p ∨ q → q ∨ p
  | .inl hp => .inr hp
  | .inr hq => .inl hq

-- can involve nested constructors

def sub2 : Nat → Nat
  | 0 | 1 => 0
  | x + 2 => x

example : sub2 0 = 0 := rfl
example : sub2 1 = 0 := rfl
example : sub2 (x+2) = x := rfl
example : sub2 5 = 3 := rfl

-- equation compiler case splits as needed

#print sub2
-- def sub2 : Nat → Nat :=
-- fun x =>
--   match x with
--   | 0 => 0
--   | 1 => 0
--   | x.succ.succ => x

-- can match multiple patterns sequentially

def foo : Nat → Nat → Nat
  | 0,     _     => 0
  | _ + 1, 0     => 1
  | _ + 1, _ + 1 => 2

-- implicit arguments

-- cannot pattern match on α
def tail1 {α : Type u} : List α → List α
  | []      => []
  | _ :: as => as

-- can pattern match on α
def tail2 : {α : Type u} → List α → List α
  | _, []      => []
  | _, _ :: as => as

#print tail1
-- def tail1.{u} : {α : Type u} → List α → List α :=
-- fun {α} x =>
--   match x with
--   | [] => []
--   | head :: as => as

#print tail2
-- def tail2.{u} : {α : Type u} → List α → List α :=
-- fun x x_1 =>
--   match x, x_1 with
--   | α, [] => []
--   | α, head :: as => as

-- 8.2 Wildcards and Overlapping Patterns

-- simulate incomplete pattern matching with Inhabited types via default

-- 8.3 Structural Recusion and Induction

-- the equation compiler processes input of the form
--
-- def foo (a : α) : (b : β) → γ
--   | [patterns₁] => t₁
--   ...
--   | [patternsₙ] => tₙ
--
-- where
-- (a : α) is a sequence of parameters,
-- (b : β) is a sequence of arguments on which pattern matching takes place, and
-- γ is any type, which can depend on a and b

-- a pattern is either:
-- - a variable
-- - a constructor applied to other patterns
-- - an expression that normalizes to one of the above (non-constructors must be marked with [match_pattern])

def add (m : Nat) : Nat → Nat
  | .zero   => m
  | .succ n => .succ (add m n)

-- induction is really a form of recursion in Lean

theorem zero_add : ∀ n, add 0 n = n
  | .zero   => rfl
  | .succ n => congrArg Nat.succ (zero_add n)

theorem zero_add' : ∀ n, add 0 n = n
  | .zero   => by simp [add]
  | .succ n => by simp [add, zero_add]

-- more structural recusion

def fib : Nat → Nat
  | 0   => 1
  | 1   => 1
  | n+2 => fib (n+1) + fib n

example : fib 0 = 1 := rfl
example : fib 1 = 1 := rfl
example : fib (n + 2) = fib (n + 1) + fib n := rfl
example : fib 7 = 21 := rfl

-- more efficient impl
def fibFast (n : Nat) : Nat :=
  (loop n).2
where
  loop : Nat → Nat × Nat
    | 0   => (0, 1)
    | n+1 => let p := loop n; (p.2, p.1 + p.2)

#eval fibFast 100
-- 573147844013817084101

-- equation compiler uses _course-of-values_ recursion

variable (C : Nat → Type u)
#check (@Nat.below C : Nat → Type u)
#reduce @Nat.below C (3 : Nat)
#check (@Nat.brecOn C : (n : Nat) → ((n : Nat) → @Nat.below C n → C n) → C n)

-- the use of course-of-values recursion is one of ways the eqaution compiler
-- uses to justify to the Lean kernel that a function terminates

-- #eval fib n is exponential in n
-- #reduce fib n is efficient because it uses the definition sent to the kernel based on brecOn

-- #eval fib 100 -- too slow
#reduce fib 100
-- 573147844013817084101

#print fib
-- def fib : Nat → Nat :=
-- fun x => Nat.brecOn x fib._f

-- 8.4 Local Recursive Declarations

-- similar to OCaml

def replicate (n : Nat) (a : α) : List α :=
  let rec loop : Nat → List α → List α
    | 0,     as => as
    | m + 1, as => loop m (a :: as)
  loop n []

#check @replicate.loop
-- @replicate.loop : {α : Type u_1} → α → Nat → List α → List α

-- let rec can also be used in proofs

theorem length_replicate (n : Nat) (a : α) : (replicate n a).length = n := by
  let rec aux (n : Nat) (as : List α)
      : (replicate.loop a n as).length = n + as.length := by
    match n with
    | 0     => simp [replicate.loop]
    | n + 1 => simp +arith [replicate.loop, aux n]
  exact aux n []

#check length_replicate.aux

-- equivalently
theorem length_replicate' (n : Nat) (a : α) : (replicate n a).length = n := by
  exact aux n []
where
  aux (n : Nat) (as : List α)
      : (replicate.loop a n as).length = n + as.length := by
    match n with
    | 0     => simp [replicate.loop]
    | n + 1 => simp +arith [replicate.loop, aux n]

#check length_replicate'.aux

-- 8.5 Well-Founded Recursion and Induction

-- std library defines two predicates Acc r a and WellFounded r

variable (α : Sort u)
variable (r : α → α → Prop)

#check (Acc r : α → Prop)
#check (WellFounded r : Prop)

-- accessibility

#check (Acc.intro : (x : α) → (∀ (y : α), r y x → Acc r y) → Acc r x)

-- given any type α, we should be able to assign a value to each accessible
-- element of α, recursively, by assigning values to all its predecessors first

-- r is well-founded if every element of type α is r-accessible

noncomputable                                     -- not supported by code generator
def f {α : Sort u}
    {r : α → α → Prop}                            -- binary relation
    (h : WellFounded r)                           -- proof of well-foundedness
    {C : α → Sort v}                              -- motive
    (F : (x : α) → ((y : α) → r y x → C y) → C x) -- inductive recipe
    : (x : α) → C x :=
  WellFounded.fix h F

-- Lean knows that < (usual order on Nat) is well-founded

theorem div_lemma {x y : Nat} : 0 < y ∧ y ≤ x → x - y < x :=
  fun h => Nat.sub_lt (Nat.lt_of_lt_of_le h.left h.right) h.left

def div.F (x : Nat) (f : (x₁ : Nat) → x₁ < x → Nat → Nat) (y : Nat) : Nat :=
  if h : 0 < y ∧ y ≤ x then
    f (x - y) (div_lemma h) y + 1
  else
    0

noncomputable def div := WellFounded.fix (measure id).wf div.F

-- this definition does not lead to div 8 2 being _definitionally_ equal to 4

/--
error: Tactic `rfl` failed: The left-hand side
  div 8 2
is not definitionally equal to the right-hand side
  4

C : Nat → Type u
α : Sort u
r : α → α → Prop
⊢ div 8 2 = 4 -/
#guard_msgs(error) in
example : div 8 2 = 4 := by rfl

-- instead div 8 2 = 4 only holds _propositionally_

example : div 8 2 = 4 := by
  simp [div, WellFounded.fix, WellFounded.fixF, Acc.rec_eq_recC, div.F, Acc.recC]

-- elaborator accepts the equivalent

def div' (x y : Nat) : Nat :=
  if h : 0 < y ∧ y ≤ x then
    have : x - y < x := Nat.sub_lt (Nat.lt_of_lt_of_le h.1 h.2) h.1
    div' (x - y) y + 1
  else
    0

-- proof that x - y < x is a hint for the decreasing_tactic used in well-founded recursion

-- the defining equation does not hold definitionally but we can prove it using unfold tactic
example (x y : Nat)
    : div' x y = if 0 < y ∧ y ≤ x then div' (x - y) y + 1 else 0 := by
  conv => lhs; unfold div'  -- unfold div' on LHS
  rfl

example : div' 8 2 = 4 := by
  conv => lhs; unfold div'  -- x = 8
  conv => lhs; unfold div'  -- x = 6
  conv => lhs; unfold div'  -- x = 4
  conv => lhs; unfold div'  -- x = 2
  conv => lhs; unfold div'  -- x = 0
  rfl

-- represent natural number as binary
-- need proof that recursion call is decreasing

def natToBin : Nat → List Bool
  | 0     => [false]
  | 1     => [true]
  | n + 2 =>
    have : (n + 2) / 2 < n + 2 := sorry
    natToBin ((n + 2) / 2) ++ [n % 2 != 0]

#eval! natToBin 12

-- Ackermann's function
-- termination is justified by the lexicographical order on Nat × Nat
-- Lean uses type class resolution to synthesize an element of WellFoundedRelation (Nat × Nat)

def ack : Nat → Nat → Nat
  | 0,  y        => y + 1
  | x + 1, 0     => ack x 1
  | x + 1, y + 1 => ack x (ack (x + 1) y)
termination_by x y => (x, y)  -- instructs Lean to use lexicographical order (optional)

instance (priority := low) [SizeOf α] : WellFoundedRelation α :=
  sizeOfWFRel

def takeWhile {α} (p : α → Bool) (as : Array α) : Array α :=
  go 0 #[]
where
  go (i : Nat) (r : Array α) : Array α :=
    if h : i < as.size then
      let a := as[i]
      if p a then
        go (i+1) (r.push a)
      else
        r
    else
      r
  termination_by as.size - i  -- optional since it can be inferred

-- by default, Lean uses the tactic decreasing_tactic to prove termination of recursion
-- can use decreasing_by to force well-founded recursion and provide our own proof

def div'' (x y : Nat) : Nat :=
  if h : 0 < y ∧ y ≤ x then
    div'' (x - y) y + 1
  else
    0
decreasing_by apply div_lemma; assumption

-- termination_by and decreasing_by complement each other
-- termination_by allows us to specify a well-founded relation
-- decreasing_by allows us to provide our own tactic for proving termination

def ack' : Nat → Nat → Nat
  | 0,   y   => y+1
  | x+1, 0   => ack' x 1
  | x+1, y+1 => ack' x (ack' (x+1) y)
termination_by x y => (x, y)
decreasing_by
   -- unfolds well-founded recursion auxiliary definitions
  all_goals simp
  · apply Prod.Lex.left; simp +arith
  · apply Prod.Lex.right; simp +arith
  · apply Prod.Lex.left; simp +arith

section TrustMeBro

set_option linter.defProp false

def unsound (n : Nat) : False :=
  unsound (n + 1)
decreasing_by sorry

#check (unsound 0 : False)
#print axioms unsound

end TrustMeBro

-- 8.6 Functional Induction

-- proofs about functions typically follow the recursive structure of the functino itself

theorem ack_gt_zero : ack m n > 0 := by
  fun_induction ack with
  | case1 x => simp                 -- x : Nat |- x + 1 > 0
  | case2 x ih => exact ih          -- x : Nat, ih : ack x 1 > 0 |- ack x 1 > 0
  | case3 x y ih1 ih2 => exact ih2  -- x y : Nat, ih1 : ack (x + 1) y > 0, ih2 : ack x (ack (x + 1) y) > 0 |- ack x (ack (x + 1) y) > 0

theorem ack_gt_zero' : ack n m > 0 := by
  fun_induction ack <;> simp [*]

def disj : Bool → Bool → Bool → Bool → Bool → Bool
  | true, _, _, _ , _ => true
  | _, true, _, _ , _ => true
  | _, _, true, _ , _ => true
  | _, _, _, true, _  => true
  | _, _, _, _, x  => x

theorem disj_or : disj b1 b2 b3 b4 b5 = (b1 || b2 || b3 || b4 || b5) := by
  fun_cases disj <;> simp_all

-- 8.7 Mutual Recursion
