/- 9. Structures and Records -/

-- non-recursive inductive type that has only one constructor is called a _structure_ or _record_
--
-- examples: Prod, Sigma
--
-- projection functions

#check Prod.fst
#check Prod.snd

#check Sigma.fst
#check Sigma.snd

-- 9.1 Declaring Structures

structure Point (α : Type u) where
  mk ::
  x : α
  y : α

-- type
#check Point

-- eliminator
#check Point.rec

-- constructor
#check Point.mk

-- projections
#check Point.x
#check Point.y

namespace Point

def p : Point Nat := Point.mk 10 20
def q : Point Nat := Point.mk 1 2

#eval p.x
#eval p.y

example (a b : α) : x (mk a b) = a := rfl
example (a b : α) : y (mk a b) = b := rfl

def add (p q : Point α) [Add α] : Point α :=
  mk (p.x + q.x) (p.y + q.y)

#eval p.add q

example {p q : Point α} [Add α] : p.add q = add p q := rfl

def smul (a : α) (p : Point α) [Mul α] : Point α :=
  mk (a * p.x) (a * p.y)

#eval p.smul 3

example {a : α} {p : Point α} [Mul α] : p.smul a = smul a p := rfl

end Point

-- 9.2 Objects

set_option linter.checkUnivs false
structure MyStruct where
  {α : Type u}
  {β : Type v}
  a : α
  b : β

#check { b := true, a := 42 : MyStruct }
-- { α := Nat, β := Bool, a := 42, b := true } : MyStruct

-- record update

#eval { Point.p with x := 42 }

-- 9.3 Inheritance

-- can extend existing structures with new fields

inductive Color where
  | red | green | blue

structure ColorPoint (α : Type u) extends Point α where
  color : Color

#check { x := 1, y := 2, color := .red : ColorPoint Nat }

-- multiple inheritance

structure RGBValue where
  red : Nat
  green : Nat
  blue : Nat

structure RedGreenPoint {α : Type u} extends Point α, RGBValue where
  no_blue : blue = 0

#check { x := 1, y := 2, red := 3, green := 4, blue := 0, no_blue := rfl : RedGreenPoint }

example {rgp : @RedGreenPoint Nat} : rgp.blue = 0 := rgp.no_blue
