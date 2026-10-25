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

-- mutually recursive functions
mutual
  def even : Nat → Bool
    | 0     => true
    | n + 1 => odd n

  def odd : Nat → Bool
    | 0     => false
    | n + 1 => even n
end

example : even (n + 1) = odd n := rfl
example : odd (n + 1) = even n := rfl

theorem even_eq_not_odd : ∀ a, even a = not (odd a) := by
  intro a; induction a; rfl
  . simp [even, odd, *]

-- mutually recursive inductive types
mutual
  inductive Even : Nat → Prop where
    | even_zero : Even 0
    | even_succ : ∀ n, Odd n → Even (n + 1)

  inductive Odd : Nat → Prop where
    | odd_succ : ∀ n, Even n → Odd (n + 1)
end

theorem not_odd_zero : ¬ Odd 0 :=
  fun h => nomatch h

theorem even_of_succ_odd : ∀ n, Odd (n + 1) → Even n
  | _, .odd_succ n h => h

theorem odd_of_succ_even : ∀ n, Even (n + 1) → Odd n
  | _, .even_succ n h => h

-- mutually recursive functions to count terms in an inductive type

inductive Term where
  | const : String → Term
  | app : String → List Term → Term

namespace Term

mutual
  def numConsts : Term → Nat
    | const _ => 1
    | app _ ts => numConstsList ts

  def numConstsList : List Term → Nat
    | [] => 0
    | t :: ts => numConsts t + numConstsList ts
end

def sample := app "f" [app "g" [const "x"], const "y"]

#eval numConsts sample
-- 2

mutual
  def replaceConst (a b : String) : Term → Term
    | const c => if a == c then const b else const c
    | app f ts => app f (replaceConstList a b ts)

  def replaceConstList (a b : String) : List Term → List Term
    | [] => []
    | t :: ts => replaceConst a b t :: replaceConstList a b ts
end

mutual
  theorem numConsts_replaceConst (a b : String) (t : Term)
      : numConsts (replaceConst a b t) = numConsts t := by
    match t with
    | const _ =>
      unfold replaceConst; split <;> simp [numConsts]
    | app _ ts =>
      simp [replaceConst, numConsts, numConsts_replaceConstList]

  theorem numConsts_replaceConstList (a b : String) (ts : List Term)
      : numConstsList (replaceConstList a b ts) = numConstsList ts := by
    match ts with
    | [] => rfl
    | t :: ts =>
      simp [replaceConstList, numConstsList, numConsts_replaceConst, numConsts_replaceConstList]
end

end Term

-- 8.8 Dependent Pattern Matching

-- defining a tail function on Vect

inductive Vect (α : Type u) : Nat → Type u
  | nil  : Vect α 0
  | cons : α → {n : Nat} → Vect α n → Vect α (n + 1)
deriving Repr

namespace Vect

-- Vect.casesOn.{u, v}
--   {α : Type v} {motive : (a : Nat) → Vect α a → Sort u}
--   {a : Nat}
--   (t : Vect α a)
--   (nil : motive 0 nil)
--   (cons : (a : α) → {n : Nat} → (a_1 : Vect α n) →
--     motive (n + 1) (cons a a_1)) :
--   motive a t

-- what to return in the nil case?

-- can use an auxilliary function

def tailAux {α} (v : Vect α m) : m = n + 1 → Vect α n :=
  Vect.casesOn v
    (fun h : 0 = n + 1 => Nat.noConfusion h)
    (fun _ (m : Nat) (as : Vect α m) =>
      fun (h : m + 1 = n + 1) =>
        Nat.noConfusion h (fun h1 : m = n => h1 ▸ as))

def tail' {α} (v : Vect α (n + 1)) : Vect α n :=
  tailAux v rfl

-- easy to define using recursive equations
-- equation compilier generates the necessary boilerpplate code

def head {α} : {n : Nat} → Vect α (n + 1) → α
  | _, cons a _ => a

def tail {α} : {n : Nat} → Vect α (n + 1) → Vect α n
  | _, cons _ as => as

theorem eta {α} : ∀ {n : Nat} (v : Vect α (n + 1)), cons (head v) (tail v) = v
  | _, cons .. => rfl

def map {α} (f : α → β) : {n : Nat} → Vect α n → Vect β n
  | 0, nil => nil
  | _, cons a as => cons (f a) (map f as)

def zip {α} : {n : Nat} → Vect α n → Vect β n → Vect (α × β) n
  | 0, nil,       nil       => nil
  | _, cons a as, cons b bs => cons (a, b) (zip as bs)

def zipWith {α} (f : α → β → γ) : {n : Nat} → Vect α n → Vect β n → Vect γ n
  | 0,     nil,       nil       => nil
  | _ + 1, cons a as, cons b bs => cons (f a b) (zipWith f as bs)

#print zipWith
#print zipWith.match_1

-- define zipWith using Vect.recOn, Vect.casesOn, and Vect.noConfusion
def zipWith' {α} (f : α → β → γ) (as : Vect α n) (bs : Vect β n) : Vect γ n :=
  Vect.casesOn (motive := fun n _ => Vect β n → Vect γ n) as
    (fun _ => nil)
    (fun a _ as bs =>
      match bs with
      | cons b bs => cons (f a b) (zipWith' f as bs))
    bs

#eval zipWith' (· ++ ·) (.cons "a" .nil) (.cons "b" .nil)

end Vect

-- 8.9 Inaccessible Patterns

-- mark a subterm as inaccessible via .(t)

inductive ImageOf {α β : Type u} (f : α → β) : β → Type u where
  | imf : (a : α) → ImageOf f (f a)

def inverse {α} {f : α → β} : (b : β) → ImageOf f b → α
  | .(_), .imf a => a

-- another example

def Vect.add {α} [Add α] : {n : Nat} → Vect α n → Vect α n → Vect α n
  | .(_), nil,       nil       => nil
  | .(_), cons a as, cons b bs => cons (a + b) (add as bs)

-- can use auto bound implicits instead

-- 8.10 Match Expressions

-- match can be used anywhere in an expression

variable (p q : Nat → Prop)

example : (∃ x, p x) → (∃ y, q y) → ∃ x y, p x ∧ q y
  | ⟨x, px⟩, ⟨y, qy⟩ => ⟨x, y, px, qy⟩

example (h₀ : ∃ x, p x) (h₁ : ∃ y, q y)
        : ∃ x y, p x ∧ q y :=
  match h₀, h₁ with
  | ⟨x, px⟩, ⟨y, qy⟩ => ⟨x, y, px, qy⟩

example : (∃ x, p x) → (∃ y, q y) → ∃ x y, p x ∧ q y :=
  fun ⟨x, px⟩ ⟨y, qy⟩ => ⟨x, y, px, qy⟩

example (h₀ : ∃ x, p x) (h₁ : ∃ y, q y)
        : ∃ x y, p x ∧ q y :=
  let ⟨x, px⟩ := h₀
  let ⟨y, qy⟩ := h₁
  ⟨x, y, px, qy⟩

-- 8.11 Exercises

-- 1. Open a namespace Hidden to avoid naming conflicts, and use the equation compiler
-- to define addition, multiplication, and exponentiation on the natural numbers. Then
-- use the equation compiler to derive some of their basic properties.

namespace Hidden

def add (m : Nat) : Nat → Nat
  | 0 => m
  | n + 1 => add m n + 1

def mul (m : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => add (mul m n) m

def exp (m : Nat) : Nat → Nat
  | 0 => 1
  | n + 1 => mul (exp m n) m

theorem add_zero (n : Nat) : add n 0 = n := rfl
theorem add_succ (m n : Nat) : add (add m n) 1 = add m (add n 1) := rfl
theorem add_one_is_succ (n : Nat) : add n 1 = n + 1 := rfl
theorem add_assoc (m n k : Nat) : add (add m n) k = add m (add n k) := by
  match k with
  | 0 => rfl
  | k + 1 => simp [←add_one_is_succ, ←add_succ, add_assoc m n k]

theorem zero_add (n : Nat) : add 0 n = n := by
  match n with
  | 0 => rfl
  | n + 1 => rw [←add_one_is_succ, ←add_assoc, zero_add]

theorem add_one_comm (n : Nat) : add n 1 = add 1 n := by
  match n with
  | 0 => rfl
  | n + 1 => rw [←add_one_is_succ, ←add_assoc, add_one_comm n]

theorem add_comm (m n : Nat) : add m n = add n m := by
  match n with
  | 0 => rw [add_zero, zero_add]
  | n + 1 => rw [←add_one_is_succ, add_assoc, ←add_one_comm, ←add_succ m n, ←add_succ n m, add_comm m n]

theorem mul_zero (n : Nat) : mul n 0 = 0 := rfl
theorem mul_succ (m n : Nat) : mul m (add n 1) = add (mul m n) m := rfl

theorem left_distrib (m n k : Nat) : mul m (add n k) = add (mul m n) (mul m k) := by
  match k with
  | 0 => rfl
  | k + 1 => rw [←add_one_is_succ, ←add_succ n k, mul_succ, mul_succ, left_distrib, add_assoc]

theorem right_distrib (m n k : Nat) : mul (add m n) k = add (mul m k) (mul n k) := by
  match k with
  | 0 => rfl
  | k + 1 =>
    rw [←add_one_is_succ, mul_succ, mul_succ, mul_succ, right_distrib]
    rw [add_assoc (mul m k), ←add_assoc (mul n k) m n, add_comm (mul n k) m, add_assoc m, ←add_assoc]

theorem mul_assoc (m n k : Nat) : mul (mul m n) k = mul m (mul n k) := by
  match k with
  | 0 => rfl
  | k + 1 => rw [←add_one_is_succ, mul_succ, mul_succ, left_distrib, mul_assoc]

theorem zero_mul (n : Nat) : mul 0 n = 0 := by
  match n with
  | 0 => rfl
  | n + 1 => rw [←add_one_is_succ, left_distrib, mul, mul_zero, add, zero_mul, zero_add]

theorem one_mul (n : Nat) : mul 1 n = n := by
  match n with
  | 0 => rfl
  | n + 1 => rw [←add_one_is_succ, mul_succ, one_mul]

theorem mul_comm (m n : Nat) : mul m n = mul n m := by
  match n with
  | 0 => rw [zero_mul, mul_zero]
  | n + 1 => rw [←add_one_is_succ, mul_succ, right_distrib, one_mul, mul_comm]

end Hidden

-- 2. Similarly, use the equation compiler to define some basic operations on lists
-- (like the reverse function) and prove theorems about lists by induction (such as the
-- fact that reverse (reverse xs) = xs for any list xs).

namespace Hidden
def reverse {α}: List α → List α
  | [] => []
  | a :: as => reverse as ++ [a]

theorem reverse_append {α} : ∀ (as bs : List α), reverse (as ++ bs) = reverse bs ++ reverse as
  | [], _ => by simp [reverse]
  | a :: as, bs => by simp [reverse, reverse_append]

theorem reverse_reverse {α} : ∀ (as : List α), reverse (reverse as) = as
  | [] => rfl
  | a :: as => by simp [reverse, reverse_append, reverse_reverse]
end Hidden

-- 3. Define your own function to carry out course-of-value recursion on the natural numbers.
-- Similarly, see if you can figure out how to define WellFounded.fix on your own.

namespace Hidden

inductive DVect (motive : Nat → Sort u) : Nat → Type u where
  | nil : DVect motive 0
  | cons : motive n → DVect motive n → DVect motive (n + 1)

def sampleMotive : Nat → Type
  | 0 => String
  | 1 => Bool
  | _ => Nat

def sample : DVect sampleMotive 2 := DVect.cons true (DVect.cons "hello" .nil)

def sampleF (n : Nat) (v : DVect sampleMotive n) : sampleMotive n :=
  match n, v with
  | 0, .nil => ""
  | 1, .cons s .nil => (String.toList s).length % 2 == 0
  | _ + 2, _ => (42 : Nat)

def brecOn {motive : Nat → Sort u} (t : Nat) (F : (n : Nat) → DVect motive n → motive n) : motive t :=
  let rec mkBelow : (n : Nat) → DVect motive n
    | 0 => .nil
    | n + 1 =>
      let prev := mkBelow n
      .cons (F n prev) prev
  F t (mkBelow t)

#reduce brecOn.mkBelow (motive := sampleMotive) sampleF 4

#eval brecOn (motive := sampleMotive) 1 sampleF

end Hidden

-- 4. Following the examples in the section on dependent pattern matching, define a function
-- that will append two vectors. This is tricky; you will have to define an auxiliary function.

namespace Vect

def append {α} (v : Vect α m) (w : Vect α n) : Vect α (n + m) :=
  match v with
  | .nil => (Nat.zero_add n).symm ▸ w
  | .cons a as => (Nat.add_comm n _) ▸ .cons a (append as w)

#check (append .nil .nil : Vect Nat 0)
#check (append (.cons 0 .nil) .nil : Vect Nat 1)
#check (append  .nil (.cons 0 .nil) : Vect Nat 1)
#check (append (.cons "a" .nil) (.cons "b" .nil) : Vect String 2)

end Vect

-- 5. Consider the following type of arithmetic expressions. The idea is that var n is a
-- variable, vₙ, and const n is the constant whose value is n.

inductive Expr where
  | const : Nat → Expr
  | var : Nat → Expr
  | plus : Expr → Expr → Expr
  | times : Expr → Expr → Expr
deriving Repr

open Expr

def sampleExpr : Expr :=
  plus (times (var 0) (const 7)) (times (const 2) (var 1))

-- Here sampleExpr represents (v₀ * 7) + (2 * v₁).

-- Write a function that evaluates such an expression, evaluating each var n to v n.

def eval (v : Nat → Nat) : Expr → Nat
  | const n     => n
  | var n       => v n
  | plus e₁ e₂  => eval v e₁ + eval v e₂
  | times e₁ e₂ => eval v e₁ * eval v e₂

def sampleVal : Nat → Nat
  | 0 => 5
  | 1 => 6
  | _ => 0

-- Try it out. You should get 47 here.
#eval eval sampleVal sampleExpr

-- Implement “constant fusion”, a procedure that simplifies subterms like 5 + 7 to 12.
-- Using the auxiliary function simpConst, define a function “fuse”: to simplify a plus
-- or a times, first simplify the arguments recursively, and then apply simpConst to try
-- to simplify the result.

def simpConst : Expr → Expr
  | plus (const n₁) (const n₂)  => const (n₁ + n₂)
  | times (const n₁) (const n₂) => const (n₁ * n₂)
  | e                           => e

def fuse : Expr → Expr
  | plus e₁ e₂  => plus (simpConst e₁) (simpConst e₂)
  | times e₁ e₂ => times (simpConst e₁) (simpConst e₂)
  | e           => e

theorem simpConst_eq (v : Nat → Nat) : ∀ e : Expr, eval v (simpConst e) = eval v e
  | plus (const _) (const _) => by simp [simpConst, eval]
  | times (const _) (const _) => by simp [simpConst, eval]
  | e => by simp [simpConst]; split <;> rfl

theorem fuse_eq (v : Nat → Nat) : ∀ e : Expr, eval v (fuse e) = eval v e
  | plus e₁ e₂ => by simp [fuse, eval, simpConst_eq]
  | times e₁ e₂ => by simp [fuse, eval, simpConst_eq]
  | e => by simp [fuse]; split <;> simp [eval, simpConst_eq]

-- The last two theorems show that the definitions preserve the value.
