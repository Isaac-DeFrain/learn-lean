/- 3.1 Proposition as Types -/

#check Prop
#check Nat
#check Bool
#check String
#check List
#check Option
#check Sum
#check Sigma
#check Type

#check And
#check Or
#check Not

def Implies (p q : Prop) : Prop := p → q
#check Implies

variable (p q r : Prop)

#check And p q
#check Or (And p q) r

structure Proof (p : Prop) : Type where
  proof : p

#check Proof (Implies (And p q) (And q p))
#check @and_comm p q

-- conflate Proof p with p itself
-- p : Prop, i.e. p is a proposition
-- interpret p as a type
-- t : p, i.e. t has type p
-- interpret t as a proof of p

/- Proof irrelevance:
  if p : Prop is any proposition, Lean's kernel treats any two elements
  t1 t2 : p as being definitionally equal. Even though we treat proofs
  t : p as ordinary objects in the language of dependent type theory,
  they carry no information beyond the fact that p is true. -/

/- 3.2 Working with Propositions as Types -/

variable {p q : Prop}
theorem t1 : p → q → p := fun hp _ => hp
#print t1

variable (p q r : Prop)
theorem t2 (h₁ : q → r) (h₂ : p → q) : p → r :=
  fun hp : p =>
  show r from h₁ (h₂ hp)
#print t2

/- 3.3 Propositional Logic -/

-- standard connectives
variable (p q : Prop)
#check p → q → p ∧ q
#check ¬ p → p ↔ False
#check p ∨ q → q ∨ p

-- 3.3.1 Conjunction

variable (p q : Prop)

#check And.intro
example (hp : p) (hq : q) : p ∧ q := And.intro hp hq
#check fun (hp : p) (hq : q) => And.intro hp hq

#check And.left
example (h : p ∧ q) : p := And.left h

#check And.right
example (h : p ∧ q) : q := And.right h

-- And commutativity
example (h : p ∧ q) : q ∧ p := And.intro (And.right h) (And.left h)

-- And associativity
example (h : p ∧ (q ∧ r)) : (p ∧ q) ∧ r :=
  And.intro
    (And.intro (And.left h) (And.left (And.right h)))
    (And.right (And.right h))

variable (hp : p) (hq : q)
#check (⟨ hp, hq ⟩ : p ∧ q)

variable {u} {T : Type u} (xs : List T)
#check (List.length xs : Nat)
#check (xs.length = List.length xs)

-- flattening nested constructors that associate to the right
example (h : p ∧ q) : p ∧ q ∧ q :=
  ⟨ h.left, ⟨ h.right, h.right ⟩ ⟩
example (h : p ∧ q) : p ∧ q ∧ q :=
  ⟨ h.left, h.right, h.right ⟩

-- 3.3.2 Disjunction

variable (p q : Prop)

#check (Or.intro_left q : p → p ∨ q)
example (hp : p) : p ∨ q := Or.intro_left q hp

#check (Or.intro_right p : q → p ∨ q)
example (hq : q) : p ∨ q := Or.intro_right p hq

#check (Or.elim : (p ∨ q) → (p → r) → (q → r) → r)
example (h : p ∨ q) : q ∨ p :=
  Or.elim h
    (fun hp : p =>
      show q ∨ p from Or.intro_right q hp)
    (fun hq : q =>
      show q ∨ p from Or.intro_left p hq)

-- same proof
example (h : p ∨ q) : q ∨ p :=
  h.elim (Or.inr) (Or.inl)

-- 3.3.3 Negation and Falsity

example : (p → False) = ¬p := rfl

variable (p q : Prop)
example (hpq : p → q) (hnq : ¬q) : ¬p :=
  fun hp : p =>
  show False from hnq (hpq hp)

-- ex falso i.e. anything follows from a contradiction
example (hp : p) (hnp : ¬p) : q := False.elim (hnp hp)
example (hp : p) (hnp : ¬p) : q := absurd hp hnp

variable (p q r : Prop)
example (hnp : ¬p) (hq : q) (hqp : q → p) : r :=
  absurd (hqp hq) hnp

#check (False.elim : False → _)
#check (True.intro : True)

-- 3.3.4 Logical Equivalence

variable (p q : Prop)

#check (@Iff.intro : (a b : Prop) → (a → b) → (b → a) → (a ↔ b))
#check (@Iff.mp : (a b : Prop) → (a ↔ b) → a → b)
#check (@Iff.mpr : (a b : Prop) → (a ↔ b) → b → a)

-- proof of p ∧ q ↔ q ∧ p
theorem and_swap : p ∧ q ↔ q ∧ p :=
  Iff.intro
    (fun h => ⟨ h.2, h.1 ⟩)
    (fun h => ⟨ h.2, h.1 ⟩)

example (h : p ∧ q): q ∧ p := (and_swap p q).mp h

-- proof of p ∨ q ↔ q ∨ p
theorem or_swap : p ∨ q ↔ q ∨ p :=
  Iff.intro
    (fun h => h.elim Or.inr Or.inl)
    (fun h => h.elim Or.inr Or.inl)

example (h : p ∨ q) : q ∨ p := (or_swap p q).mp h

-- 3.4 Introducing Auxiliary Subgoals

variable (p q : Prop)

-- have construct
example (h : p ∧ q) : q ∧ p :=
  have hp : p := h.left
  have hq : q := h.right
  show q ∧ p from And.intro hq hp

-- suffices construct
example (h : p ∧ q) : q ∧ p :=
  have hp : p := h.left
  suffices hq : q from And.intro hq hp
  show q from h.right

-- 3.5 Classical Logic
section
  open Classical

  variable (p q : Prop)

  -- law of excluded middle
  #check (em p : p ∨ ¬p)

  -- double negation elimination
  theorem dne {p : Prop} (h : ¬¬p) : p :=
    Or.elim (em p)
      (fun hp : p => hp)
      (fun hnp : ¬p => absurd hnp h)

  -- dne implies law of excluded middle
  example : p ∨ ¬p :=
    dne
      (fun h : ¬(p ∨ ¬p) =>
        let not_p : ¬p := fun hp : p => h (Or.inl hp)
        show False from h (Or.inr not_p))

  -- De Morgan's law
  example (h : ¬(p ∧ q)) : ¬p ∨ ¬q :=
    Or.elim (em p)
      (fun hp : p => Or.inr
        (show ¬q from fun hq : q => h ⟨hp, hq⟩))
      (fun hnp : ¬p => Or.inl hnp)
end

-- 3.6 Examples of Propositional Validities

-- communtativity
#check (@And.comm p q : p ∧ q ↔ q ∧ p)
#check (@Or.comm p q : p ∨ q ↔ q ∨ p)

-- associativity
#check (@and_assoc p q r : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r))
#check (@or_assoc p q r : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r))

-- distributivity
-- 5. p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r)
-- 6. p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r)

/-
Other properties:

7. (p → (q → r)) ↔ (p ∧ q → r)
8. ((p ∨ q) → r) ↔ (p → r) ∧ (q → r)
9. ¬(p ∨ q) ↔ ¬p ∧ ¬q
10. ¬p ∨ ¬q → ¬(p ∧ q)
11. ¬(p ∧ ¬p)
12. p ∧ ¬q → ¬(p → q)
13. ¬p → (p → q)
14. (¬p ∨ q) → (p → q)
15. p ∨ False ↔ p
16. p ∧ False ↔ False
17. ¬(p ↔ ¬p)
18. (p → q) → (¬q → ¬p)

These require classical reasoning:

19. (p → r ∨ s) → ((p → r) ∨ (p → s))
20. ¬(p ∧ q) → ¬p ∨ ¬q
21. ¬(p → q) → p ∧ ¬q
22. (p → q) → (¬p ∨ q)
23. (¬q → ¬p) → (p → q)
24. p ∨ ¬p
25. ((p → q) → p) → p
-/

-- distributivity
example (p q r : Prop) : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) :=
  Iff.intro
    (fun h : p ∧ (q ∨ r) =>
      have hp : p := h.left
      Or.elim (h.right)
        (fun hq : q =>
          show (p ∧ q) ∨ (p ∧ r) from Or.inl ⟨hp, hq⟩)
        (fun hr : r =>
          show (p ∧ q) ∨ (p ∧ r) from Or.inr ⟨hp, hr⟩))
    (fun h : (p ∧ q) ∨ (p ∧ r) =>
      Or.elim h
        (fun hpq : p ∧ q =>
          have hp : p := hpq.left
          have hq : q := hpq.right
          show p ∧ (q ∨ r) from ⟨hp, Or.inl hq⟩)
        (fun hpr : p ∧ r =>
          have hp : p := hpr.left
          have hr : r := hpr.right
          show p ∧ (q ∨ r) from ⟨hp, Or.inr hr⟩))

-- an example that requires classical reasoning
example (p q : Prop) : ¬(p ∧ ¬q) → (p → q) :=
  fun h : ¬(p ∧ ¬q) =>
  fun hp : p =>
  show q from
    Or.elim (Classical.em q)
      (fun hq : q => hq)
      (fun hnq : ¬q => absurd (And.intro hp hnq) h)

-- 3.7 Exercises

variable (p q r : Prop)

-- commutativity of ∧ and ∨
example : p ∧ q ↔ q ∧ p :=
  Iff.intro
    (fun h : p ∧ q => ⟨ h.right, h.left ⟩)
    (fun h : q ∧ p => ⟨ h.right, h.left ⟩)

example : p ∨ q ↔ q ∨ p :=
  Iff.intro
    (fun h : p ∨ q => h.elim Or.inr Or.inl)
    (fun h : q ∨ p => h.elim Or.inr Or.inl)

-- associativity of ∧ and ∨
example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) :=
  Iff.intro
    (fun h : (p ∧ q) ∧ r => And.intro h.1.1 (And.intro h.1.2 h.2) )
    (fun h : p ∧ (q ∧ r) => And.intro (And.intro h.1 h.2.1) h.2.2)

example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) :=
  Iff.intro
    (fun h : (p ∨ q) ∨ r =>
      h.elim
        (fun hpq : p ∨ q => hpq.elim Or.inl (Or.inr ∘ Or.inl))
        (Or.inr ∘ Or.inr))
    (fun h : p ∨ (q ∨ r) =>
      h.elim
        (Or.inl ∘ Or.inl)
        (fun hqr : q ∨ r => hqr.elim (Or.inl ∘ Or.inr) Or.inr))

-- distributivity
example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) :=
  Iff.intro
    (fun h : p ∧ (q ∨ r) =>
      have hp : p := h.left
      have hqr : q ∨ r := h.right
      show (p ∧ q) ∨ (p ∧ r) from
        hqr.elim (Or.inl ∘ And.intro hp) (Or.inr ∘ And.intro hp))
    (fun h : (p ∧ q) ∨ (p ∧ r) =>
      h.elim
        (fun hpq : p ∧ q =>
          have hp : p := hpq.left
          have hq : q := hpq.right
          show p ∧ (q ∨ r) from ⟨ hp, Or.inl hq ⟩)
        (fun hpq : p ∧ r =>
          have hp : p := hpq.left
          have hr : r := hpq.right
          show p ∧ (q ∨ r) from ⟨ hp, Or.inr hr ⟩))

example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) :=
  Iff.intro
    (fun h : p ∨ (q ∧ r) =>
      h.elim
        (fun hp : p => ⟨ Or.inl hp, Or.inl hp ⟩)
        (fun hqr : q ∧ r => ⟨ Or.inr hqr.left, Or.inr hqr.right ⟩))
    (fun h : (p ∨ q) ∧ (p ∨ r) =>
      have hpq : p ∨ q := h.left
      have hpr : p ∨ r := h.right
      show p ∨ (q ∧ r) from
        hpq.elim
          Or.inl
          (fun hq : q =>
            hpr.elim
              Or.inl
              (Or.inr ∘ And.intro hq)))

-- other properties
example : (p → (q → r)) ↔ (p ∧ q → r) :=
  Iff.intro
    (fun h : p → (q → r) =>
      fun hpq : p ∧ q => h hpq.left hpq.right)
    (fun h : p ∧ q → r =>
      fun hp : p =>
        fun hq : q => h ⟨ hp, hq ⟩)

example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) :=
  Iff.intro
    (fun h : (p ∨ q) → r =>
      ⟨ fun hp : p => h (Or.inl hp), fun hq : q => h (Or.inr hq) ⟩)
    (fun h : (p → r) ∧ (q → r) =>
      fun hpq : p ∨ q => hpq.elim h.left h.right)

example : ¬(p ∨ q) ↔ ¬p ∧ ¬q :=
  Iff.intro
    (fun h : ¬(p ∨ q) => ⟨ h ∘ Or.inl, h ∘ Or.inr ⟩)
    (fun h : ¬p ∧ ¬q =>
      fun hpq : p ∨ q => hpq.elim h.left h.right)

example : ¬p ∨ ¬q → ¬(p ∧ q) :=
  fun h : ¬p ∨ ¬q =>
    fun hpq : p ∧ q => h.elim (absurd hpq.left) (absurd hpq.right)

example : ¬(p ∧ ¬p) :=
  fun h : p ∧ ¬p => absurd h.left h.right

example : p ∧ ¬q → ¬(p → q) :=
  fun h : p ∧ ¬q =>
    fun hpq : p → q => absurd (hpq h.left) h.right

example : ¬p → (p → q) :=
  fun h : ¬p =>
    fun hp : p => absurd hp h

example : (¬p ∨ q) → (p → q) :=
  fun h : ¬p ∨ q =>
    fun hp : p =>
      h.elim (absurd hp) id

example : p ∨ False ↔ p :=
  Iff.intro
    (fun h : p ∨ False =>
      h.elim id False.elim)
    Or.inl

example : p ∧ False ↔ False :=
  Iff.intro And.right False.elim

example : (p → q) → (¬q → ¬p) :=
  fun h : p → q =>
    fun hnq : ¬q =>
      fun hp : p => absurd (h hp) hnq

variable (p q r : Prop)

example : (p → q ∨ r) → ((p → q) ∨ (p → r)) :=
  (fun h : (p → q ∨ r) =>
    Classical.byContradiction
      (fun f : ¬((p → q) ∨ (p → r)) =>
        have hnpqr : ¬(p → q) ∧ ¬(p → r) := not_or.mp f
        have hnpq : ¬(p → q) := hnpqr.left
        have hnpr : ¬(p → r) := hnpqr.right
        have hpnq : p ∧ ¬q := not_imp.mp hnpq
        have hpnr : p ∧ ¬r := not_imp.mp hnpr
        have hnqr : ¬(q ∨ r) := not_or_intro hpnq.right hpnr.right
        absurd (h hpnq.left) hnqr) )

example : ¬(p ∧ q) → ¬p ∨ ¬q :=
  fun h : ¬(p ∧ q) =>
    Classical.byContradiction
      (fun f : ¬(¬p ∨ ¬q) =>
        have hpq : ¬¬p ∧ ¬¬q := not_or.mp f
        have hp : p := dne hpq.left
        have hq : q := dne hpq.right
        absurd ⟨ hp, hq ⟩ h )

example : ¬(p → q) → p ∧ ¬q :=
  fun h : ¬(p → q) =>
    Classical.byContradiction
      (fun f : ¬(p ∧ ¬q) =>
        have hnpnnq : ¬p ∨ ¬¬q := Classical.not_and_iff_not_or_not.mp f
        have hnpq : ¬p ∨ q := hnpnnq.elim Or.inl (Or.inr ∘ dne)
        have hpq : p → q :=
          hnpq.elim
            (fun hnp : ¬p =>
              fun hp : p => absurd hp hnp)
            (fun hq : q => fun _ => hq)
        absurd hpq h )

example : (p → q) → (¬p ∨ q) :=
  fun h : p → q =>
    Classical.byContradiction
      (fun f : ¬(¬p ∨ q) =>
        have hnnpnq : ¬¬p ∧ ¬q := not_or.mp f
        have hpnq : p ∧ ¬q := ⟨ dne hnnpnq.left, hnnpnq.right ⟩
        absurd (h hpnq.left) hpnq.right )

example : (¬q → ¬p) → (p → q) :=
  fun h : ¬q → ¬p =>
    Classical.byContradiction
      (fun f : ¬(p → q) =>
        have hpnq : p ∧ ¬q := not_imp.mp f
        have hnq : ¬q := hpnq.right
        absurd hpnq.left (h hnq) )

example : p ∨ ¬p :=
  Classical.byContradiction
    (fun h : ¬(p ∨ ¬p) =>
      have hnpnnp : ¬p ∧ ¬¬p := not_or.mp h
      have hnpp : ¬p ∧ p := ⟨ hnpnnp.left, dne hnpnnp.right ⟩
      have hpnp : p ∧ ¬p := and_comm.mp hnpp
      absurd hpnp and_not_self )

example : ((p → q) → p) → p :=
  fun h : (p → q) → p =>
    Classical.byContradiction
      (fun hnp : ¬p =>
        let hpq : p → q := fun hp : p => absurd hp hnp
        absurd (h hpq) hnp )

-- Prove ¬(p ↔ ¬p) without using classical logic.
example : ¬(p ↔ ¬p) :=
  fun h : p ↔ ¬p =>
    have hpnp : p → ¬p := h.mp
    have hnpp : ¬p → p := h.mpr
    have hnp : ¬p :=
      fun hp : p => absurd hp (hpnp hp)
    have hp : p := hnpp hnp
    show False from absurd hp hnp
