-- Errata - Existential quantifier

-- Existential quantifier as a Church encoding
def sig (u : Type) (v : u → Type) : Type 1 :=
  ∀ w : Type, (∀ x : u, v x → w) → w

-- Existential introduction (pair/pack)
def D' (u : Type) (v : u → Type) (x : u) (y : v x)
    (w : Type) (z : ∀ x : u, v x → w) : w :=
  z x y

-- Existential quantifier projection
def proj (u : Type) (v : u → Type) (w : Type)
    (z : ∀ x : u, v x → w) (y : sig u v) : w :=
  y w z

variable (u : Type)
variable (v : u → Type)
variable (w : Type)
variable (x : u)
variable (y : v x)
variable (z : ∀ x : u, v x → w)

-- Sanity checks
#check sig
#check sig u v
#check D'
#check D' u v
#check D' u v x y w z
#check proj
#check proj u v

-- pg. 213, line 10
#check (proj u v w z (D' u v x y) : w)

-- pg. 213, line 12
example : proj u v w z (D' u v x y) = z x y := rfl

-- Book definition of projection does not type-check
/--
error: Application type mismatch: The argument
  w
has type
  Type
of sort `Type 1` but is expected to have type
  u
of sort `Type` in the application
  y w
-/
#guard_msgs (error) in
example (u : Type) (v : u → Type) (w : Type)
    (z : ∀ x : u, v x → w) (y : ∀ x : u, v x) : w :=
  y w z
