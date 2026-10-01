-- Errata

-- These are term/combinator definitions (Prop-valued by design).
set_option linter.defProp false

-- Existential quantifier as a Church encoding
def sig (u : Prop) (v : u → Prop) : Prop :=
  ∀ w : Prop, (∀ x : u, v x → w) → w

-- Existential introduction (pair/pack)
def D' (u : Prop) (v : u → Prop) (x : u) (y : v x)
    (w : Prop) (z : ∀ x : u, v x → w) : w :=
  z x y

-- Existential quantifier projection (elimination)
def proj (u : Prop) (v : u → Prop) (w : Prop)
    (z : ∀ x : u, v x → w) (y : sig u v) : w :=
  y w z

axiom u : Prop
axiom v : u → Prop
axiom w : Prop
axiom x : u
axiom y : v x
axiom z : ∀ x : u, v x → w

#check sig
#check sig u v
#check D'
#check D' u v
#check D' u v x y w z
#check proj
#check proj u v
#check proj u v w z (D' u v x y)
