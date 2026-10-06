/- 4. Quantifiers and Equality -/

-- 4.1 The Universal Quantifier

/-
introduction rule

Given a proof of p x, in a context where x : α is arbitrary,
we obtain a proof ∀ x : α, p x.

Given a term t : β x, in a context where x : α is arbitrary,
we have (fun x : α => t) : (x : α) → β x.
-/

/-
elimination rule

Given a proof of ∀ x : α, p x and any term t : α,
we obtain a proof of p t.

Given a term s : (x : α) → β x and any term t : α,
we have s t : β t.
-/

example (α : Type) (p q : α → Prop) :
    (∀ x : α, p x ∧ q x) → ∀ y : α, p y :=
  fun h : ∀ x : α, p x ∧ q x =>
    fun y : α =>
      show p y from (h y).left

-- alpha equivalent expressions are equivalent
example (α : Type) (p q : α → Prop) :
    (∀ x : α, p x ∧ q x) → ∀ x : α, p x :=
  fun h : ∀ x : α, p x ∧ q x =>
    fun x : α =>
      show p x from (h x).left

-- relation r is transitive
variable (α : Type) (r : α → α → Prop)
variable (trans_r : ∀ {x y z}, r x y → r y z → r x z)

variable (a b c : α)
variable (hab : r a b) (hbc : r b c)

#check (@trans_r : ∀ x y z, r x y → r y z → r x z)
#check (@trans_r a b c : r a b → r b c → r a c)
#check (@trans_r a b c hab : r b c → r a c)
#check (@trans_r a b c hab hbc : r a c)

#check trans_r
#check (trans_r : r a b → r b c → r a c)
#check (trans_r hab : r b c → r a c)
#check (trans_r hab hbc : r a c)

-- example of elementary reasoning with an equivalence relation

variable (α : Type) (r : α → α → Prop)

variable (refl_r : ∀ x, r x x)
variable (symm_r : ∀ {x y}, r x y → r y x)
variable (trans_r : ∀ {x y z}, r x y → r y z → r x z)

example (a b c d : α) (hab : r a b) (hcb : r c b) (hcd : r c d) : r a d :=
  trans_r (trans_r hab (symm_r hcb)) hcd

-- typing dependent arrow types
variable (α : Sort u) (β : Sort v)
#check ((x : α) → β : Sort (imax u v))

-- Prop is impredicative
variable (β : Prop)
#check ((x : α) → β : Prop)

-- 4.2 Equality

-- equality is an equivalence relation
#check (@Eq.refl.{u} α : ∀ a : α, a = a)
#check (@Eq.symm.{u} α : ∀ a b : α, a = b → b = a)
#check (@Eq.trans.{u} α : ∀ a b c : α, a = b → b = c → a = c)

example (α : Type) (a b c d : α) (hab : a = b) (hcb : c = b) (hcd : c = d) : a = d :=
  Eq.trans (Eq.trans hab (Eq.symm hcb)) hcd

-- equavlently using projection notation
example (α : Type) (a b c d : α) (hab : a = b) (hcb : c = b) (hcd : c = d) : a = d :=
  (hab.trans hcb.symm).trans hcd

-- terms in CoC have a computational interpretation
example {α β : Type} (f : α → β) (a : α) : (fun x => f x) a = f a := Eq.refl _
example {α β : Type} (a : α) (b : β) : (a, b).1 = a := Eq.refl _
example : 2 + 3 = 5 := Eq.refl _

-- equivalently using rfl
example {α β : Type} (f : α → β) (a : α) : (fun x => f x) a = f a := rfl
example {α β : Type} (a : α) (b : β) : (a, b).1 = a := rfl
example : 2 + 3 = 5 := rfl

-- substitution principle
example {α : Type} (a b : α) (p : α → Prop) (h1 : a = b) (h2 : p a) : p b :=
  Eq.subst h1 h2

-- equivalently
example {α : Type} (a b : α) (p : α → Prop) (h1 : a = b) (h2 : p a) : p b :=
  h1 ▸ h2

variable (α : Type)
variable (a b : α)
variable (f g : α → Nat)
variable (h₁ : a = b)
variable (h₂ : f = g)

example : f a = f b := congrArg f h₁
example : f a = g a := congrFun h₂ a
example : f a = g b := congr h₂ h₁

variable (a b c : Nat)

example : a + 0 = a := Nat.add_zero a
example : 0 + a = a := Nat.zero_add a
example : a * 1 = a := Nat.mul_one a
example : 1 * a = a := Nat.one_mul a
example : a + b = b + a := Nat.add_comm a b
example : a + b + c = a + (b + c) := Nat.add_assoc a b c
example : a * b = b * a := Nat.mul_comm a b
example : a * b * c = a * (b * c) := Nat.mul_assoc a b c
example : a * (b + c) = a * b + a * c := Nat.mul_add a b c
example : a * (b + c) = a * b + a * c := Nat.left_distrib a b c
example : (a + b) * c = a * c + b * c := Nat.add_mul a b c
example : (a + b) * c = a * c + b * c := Nat.right_distrib a b c

example (x y : Nat) :
    (x + y) * (x + y) = x * x + y * x + x * y + y * y :=
  have h1 : (x + y) * (x + y) = (x + y) * x + (x + y) * y :=
    Nat.left_distrib _ _ _
  have h2 : (x + y) * (x + y) = x * x + y * x + (x + y) * y :=
    Nat.right_distrib _ _ _ ▸ h1
  have h3 : (x + y) * (x + y) = x * x + y * x + (x * y + y * y) :=
    (Nat.right_distrib _ _ _ ▸ h2.symm).symm
  Nat.add_assoc _ _ _ ▸ h3

-- 4.3 Computational Proofs

variable (a b c d e : Nat)

theorem T
    (h1 : a = b)
    (h2 : b = c + 1)
    (h3 : c = d)
    (h4 : e = 1 + d) :
    a = e :=
  calc
    a = b      := h1
    _ = c + 1  := h2
    _ = d + 1  := h3 ▸ Eq.refl _
    _ = 1 + d  := Nat.add_comm _ _
    _ = e      := Eq.symm h4

-- equivalently using simp and rw tactics
theorem T'
    (h1 : a = b)
    (h2 : b = c + 1)
    (h3 : c = d)
    (h4 : e = 1 + d) :
    a = e :=
  calc
    a = b      := by rw [h1]
    _ = c + 1  := by rw [h2]
    _ = d + 1  := by rw [h3]
    _ = 1 + d  := by rw [Nat.add_comm]
    _ = e      := by rw [h4]

-- reduce number of steps by applying sequences of rw's
theorem T''
    (h1 : a = b)
    (h2 : b = c + 1)
    (h3 : c = d)
    (h4 : e = 1 + d) :
    a = e :=
  calc
    a = d + 1  := by rw [h1, h2, h3]
    _ = e      := by rw [Nat.add_comm, h4]

-- simp tactic rewrites goal by applying given identities in any order
theorem T'''
    (h1 : a = b)
    (h2 : b = c + 1)
    (h3 : c = d)
    (h4 : e = 1 + d) :
    a = e :=
  by simp [h1, h4, h3, Nat.add_comm, h2]

-- calc supports any transitive relation
variable (a b c d : Nat)
example (h1 : a = b) (h2 : b ≤ c) (h3 : c + 1 < d) : a < d :=
  calc
    a = b     := h1
    _ < b + 1 := Nat.lt_succ_self b
    _ ≤ c + 1 := Nat.succ_le_succ h2
    _ < d     := h3

def divides (x y : Nat) : Prop :=
  ∃ k : Nat, x * k = y

theorem divides_trans (h1 : divides x y) (h2 : divides y z) : divides x z :=
  let ⟨ k1, d1 ⟩ := h1
  let ⟨ k2, d2 ⟩ := h2
  ⟨ k1 * k2, by rw [Nat.mul_comm k1 k2, Nat.mul_left_comm, d1, Nat.mul_comm, d2] ⟩

theorem divides_mul (x : Nat) (k : Nat) : divides x (k * x) :=
  ⟨ k, by rw [Nat.mul_comm] ⟩

instance : Trans divides divides divides where
  trans := divides_trans

infix:50 " | " => divides

example (h1: divides x y) (h2 : y = z) : divides x (2 * z) :=
  calc
    x | y     := h1
    _ = z     := h2
    _ | 2 * z := divides_mul _ _

example {x y : Nat} : (x + y) * (x + y) = x * x + y * x + x * y + y * y :=
  calc
    (x + y) * (x + y) = (x + y) * x + (x + y) * y  :=
      by rw [Nat.mul_add]
    _ = x * x + y * x + (x * y + y * y)            :=
      by rw [Nat.add_mul, Nat.add_mul]
    _ = x * x + y * x + x * y + y * y              :=
      by rw [←Nat.add_assoc]

example {x y : Nat} : (x + y) * (x + y) = x * x + y * x + x * y + y * y :=
  by simp [Nat.mul_add, Nat.add_mul, Nat.add_assoc]

-- 4.4 Existential Quantifier

-- introduction

example : ∃ x : Nat, x > 0 :=
  have h : 1 > 0 := Nat.zero_lt_succ _
  Exists.intro _ h

example (x : Nat) (h : x > 0) : ∃ y, y < x :=
  Exists.intro 0 h

example (x y z : Nat) (hxy : x < y) (hyz : y < z) :
    ∃ w, x < w ∧ w < z :=
  Exists.intro y (And.intro hxy hyz)

-- using anonymous constructor notation
example : ∃ x : Nat, x > 0 :=
  have h : 1 > 0 := Nat.zero_lt_succ _
  ⟨ _, h ⟩

example (x : Nat) (h : x > 0) : ∃ y, y < x :=
  ⟨ 0, h ⟩

example (x y z : Nat) (hxy : x < y) (hyz : y < z) :
    ∃ w, x < w ∧ w < z :=
  ⟨ y, hxy, hyz ⟩

section
  variable (g : Nat → Nat → Nat)

  theorem gex1 (hg : g 0 0 = 0) : ∃ x, g x x = x := ⟨0, hg⟩
  theorem gex2 (hg : g 0 0 = 0) : ∃ x, g x 0 = x := ⟨0, hg⟩
  theorem gex3 (hg : g 0 0 = 0) : ∃ x, g 0 0 = x := ⟨0, hg⟩
  theorem gex4 (hg : g 0 0 = 0) : ∃ x, g x x = 0 := ⟨0, hg⟩

  set_option pp.explicit true  -- display implicit arguments

  #print gex1
  #print gex2
  #print gex3
  #print gex4
end

-- elimination

variable (α : Type) (p q : α → Prop)
example (h : ∃ x, p x ∧ q x) : ∃ x, q x ∧ p x :=
  Exists.elim h
    (fun w =>
      fun hw : p w ∧ q w =>
        show ∃ x, q x ∧ p x from ⟨w, hw.right, hw.left⟩)

-- using match/let for elimination

example (h : ∃ x, p x ∧ q x) : ∃ x, q x ∧ p x :=
  let ⟨ w, (hw : p w ∧ q w) ⟩ := h
  ⟨ w, hw.right, hw.left ⟩

def IsEven (a : Nat) : Prop := ∃ b, a = 2 * b

theorem even_plus_even (h1 : IsEven a) (h2: IsEven b) : IsEven (a + b) :=
  match h1, h2 with
  | ⟨ ca, ha ⟩, ⟨ cb, hb ⟩ =>
    Exists.intro (ca + cb) (
      calc a + b
           _ = 2 * ca + 2 * cb  := by rw [ha, hb]
           _ = 2 * (ca + cb)    := by rw [Nat.mul_add])

theorem even_plus_even' (h1 : IsEven a) (h2: IsEven b) : IsEven (a + b) :=
  match h1, h2 with
  | ⟨ ca, ha ⟩, ⟨ cb, hb ⟩ =>
    ⟨ ca + cb, by rw [ha, hb, Nat.mul_add] ⟩

variable (p : α → Prop)

example (h : ¬ ∀ x, ¬ p x) : ∃ x, p x :=
  Classical.byContradiction
    (fun h1 : ¬ ∃ x, p x =>
      have h2 : ∀ x , ¬ p x :=
        fun x =>
        fun h3 : p x =>
        have h4 : ∃ x, p x := ⟨ x, h3 ⟩
        show False from h1 h4
      show False from h h2)

-- Exercises

variable (α : Type) (p q : α → Prop)
variable (r : Prop)

example : (∃ _ : α, r) → r :=
  fun h : ∃ _, r =>
  let ⟨ _, hw ⟩ := h
  hw

example (a : α) : r → (∃ _ : α, r) :=
  fun h : r =>
  ⟨ a, h ⟩

example : (∃ x, p x ∧ r) ↔ (∃ x, p x) ∧ r :=
  Iff.intro
    (fun h : ∃ x, p x ∧ r =>
      let ⟨ w, hw ⟩ := h
      have l : ∃ x, p x := Exists.intro w hw.left
      ⟨ l, hw.right ⟩)
    (fun h : (∃ x, p x) ∧ r =>
      let ⟨ w, hw ⟩ := h.left
      Exists.intro w ⟨ hw, h.right ⟩ )

example : (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) :=
  Iff.intro
    (fun ⟨ w, (hw : p w ∨ q w) ⟩ =>
      Or.elim hw
        (fun hp => Or.inl (Exists.intro w hp))
        (fun hq => Or.inr (Exists.intro w hq)) )
    (fun h : (∃ x, p x) ∨ (∃ x, q x) =>
      h.elim
        (fun ⟨ w, hw ⟩ =>
          Exists.intro w (Or.inl hw))
        (fun ⟨ w, hw ⟩ =>
          Exists.intro w (Or.inr hw)) )

example : (∀ x, p x) ↔ ¬ (∃ x, ¬ p x) :=
  Iff.intro
    (fun h : ∀ x, p x =>
      fun h1 : ∃ x, ¬ p x =>
        let ⟨ w, hw ⟩ := h1
        absurd (h w) hw)
    (fun h : ¬ (∃ x, ¬ p x) =>
      fun x =>
        Classical.byContradiction
          (fun h1 : ¬ p x =>
            let h2: ∃ x, ¬ p x := ⟨ x, h1 ⟩
            absurd h2 h))

example : (∃ x, p x) ↔ ¬ (∀ x, ¬ p x) :=
  Iff.intro
    (fun ⟨ w, h ⟩ =>
      fun h1 : ∀ x, ¬ p x =>
        absurd h (h1 w))
    (fun h : ¬ ∀ x, ¬ p x =>
      Classical.byContradiction
        (fun h1 : ¬ ∃ x, p x =>
          have h2 : ∀ x, ¬ p x :=
            fun x =>
              fun hx : p x =>
                absurd ⟨ x, hx ⟩ h1
          absurd h2 h))

example : (¬ ∃ x, p x) ↔ (∀ x, ¬ p x) :=
  Iff.intro
    (fun h : ¬ ∃ x, p x =>
      fun x =>
        fun hx : p x =>
          absurd ⟨ x, hx ⟩ h)
    (fun h : ∀ x, ¬ p x =>
      fun ⟨ w, (hw : p w) ⟩ =>
        absurd hw (h w))

example : (¬ ∀ x, p x) ↔ (∃ x, ¬ p x) :=
  Iff.intro
    (fun h : ¬ ∀ x, p x =>
      Classical.byContradiction
        (fun h1 : ¬ ∃ x, ¬ p x =>
          have h2 : ∀ x, p x :=
            fun x =>
              Classical.byContradiction
                (fun hx : ¬ p x =>
                  absurd ⟨ x, hx ⟩ h1)
          absurd h2 h) )
    (fun ⟨ w, (hw : ¬ p w) ⟩ =>
      fun h : ∀ x, p x =>
        absurd (h w) hw )

example : (∀ x, p x → r) ↔ (∃ x, p x) → r :=
  Iff.intro
    (fun h : ∀ x, p x → r =>
      fun ⟨ w, (hw : p w) ⟩ => (h w) hw )
    (fun h : (∃ x, p x) → r =>
      fun x =>
        fun hx : p x => h ⟨ x, hx ⟩)

example (a : α) : (∃ x, p x → r) ↔ (∀ x, p x) → r :=
  Iff.intro
    (fun ⟨ w, (hw : p w → r) ⟩ =>
      fun h1 : ∀ x, p x => hw (h1 w))
    (fun h : (∀ x, p x) → r =>
      Classical.byCases
        (fun ha : ∀ x, p x =>
          show ∃ x, p x → r from ⟨ a, fun _ => h ha ⟩)
        (fun hna : ¬ ∀ x, p x =>
          Classical.byContradiction
            (fun h1 : ¬ ∃ x, p x → r =>
              have h2 : ∀ x, p x :=
                fun x =>
                  Classical.byContradiction
                    (fun h3 : ¬ p x =>
                      have h4 : ∃ x, p x → r := ⟨ x, fun hp => absurd hp h3 ⟩
                      absurd h4 h1)
              absurd h2 hna)))

example (a : α) : (∃ x, r → p x) ↔ (r → ∃ x, p x) :=
  Iff.intro
    (fun ⟨ w, (hw : r → p w) ⟩ =>
      fun x => ⟨ w, (hw x) ⟩)
    (fun h : r → ∃ x, p x =>
      show ∃ x, r → p x from
        Classical.byCases
          (fun ⟨ w, (hw : p w) ⟩ => ⟨ w, fun _ => hw ⟩)
          (fun hnep : ¬ ∃ x, p x =>
            have hnr : ¬r :=
              Classical.byContradiction
                (fun x : ¬¬r => absurd (h (Classical.not_not.mp x)) hnep)
            have h1 : r → p a := fun x => absurd x hnr
            ⟨ a, h1 ⟩))
