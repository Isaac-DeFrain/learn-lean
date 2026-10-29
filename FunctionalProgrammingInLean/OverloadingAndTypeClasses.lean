/- 3. Overloading and Type Classes -/

-- 3.1 Positive Numbers

inductive Pos : Type where
  | one : Pos
  | succ : Pos → Pos

instance : Inhabited Pos where
  default := .one

instance OfNatPos : OfNat Pos n where
  ofNat :=
    let rec ofNat : Nat → Pos
    | 0 => panic! "Pos must come positive natural number"
    | 1 => .one
    | n + 1 => .succ (ofNat n)
    ofNat n

def Pos.toNat : Pos → Nat
  | .one => 1
  | .succ n => toNat n + 1

instance : Add Pos where
  add m n := OfNat.ofNat (m.toNat + n.toNat)

instance : Mul Pos where
  mul m n := OfNat.ofNat (m.toNat * n.toNat)

-- 3.1.6 Exercises

-- 3.1.6.2 Even Numbers
-- Define a datatype that represents only even numbers.
-- Define instances of Add, Mul, and ToString that allow it to be used conveniently.

inductive Even : Type where
  | zero
  | mul2 : Nat → Even

def Even.toNat : Even → Nat
  | zero => 0
  | mul2 k => 2 * k

instance : Add Even where
  add :=
    let rec add : Even → Even → Even
      | .zero, .zero => .zero
      | .zero, n | n, .zero => n
      | .mul2 m, .mul2 n => .mul2 (m + n)
    add

instance : Mul Even where
  mul :=
    let rec mul : Even → Even → Even
      | .zero, _ | _, .zero => .zero
      | .mul2 m, .mul2 n => .mul2 (2 * m * n)
    mul

instance : ToString Even where
  toString :=
    let rec toString : Even → String
      | .zero => "0"
      | .mul2 n => s!"{2 * n}"
    toString

-- 3.1.6.3 HTTP Requests
-- An HTTP request begins with an identification of a HTTP method, such as GET or POST,
-- along with a URI and an HTTP version. Define an inductive type that represents an
-- interesting subset of the HTTP methods, and a structure that represents HTTP responses.
-- Responses should have a ToString instance that makes it possible to debug them. Use a
-- type class to associate different IO actions with each HTTP method, and write a test
-- harness as an IO action that calls each method and prints the result.

inductive URI where

inductive HTTPVersion where
  | one
  | two

inductive HTTPRequest where
  | GET (uri : URI) (version : HTTPVersion)
  | POST (uri : URI) (version : HTTPVersion) (body : String)

structure HTTPResponse where
  uri : URI
  version : HTTPVersion
  status : Nat
  body : String

-- 3.2 Type Classes and Polymorphism

-- 3.2.1 Checking Polymorphic Functions' Types

#check IO.println
-- IO.println.{u_1} {α : Type u_1} [ToString α] (s : α) : IO Unit

#check (IO.println)
-- IO.println : ?m.1 → IO Unit

-- `?m.1` is a metavariable

#check @IO.println
-- @IO.println : {α : Type u_1} → [ToString α] → α → IO Unit

-- 3.2.2 Defining Polymorphic Functions with Instance Implicits

def List.sumOfContents [Add α] [Zero α] : List α → α
  | [] => 0
  | x :: xs => x + xs.sumOfContents

#eval [1, 2, 3, 4].sumOfContents
-- 10

-- instances can take instance implicit arguments

structure PPoint (α : Type) where
  x : α
  y : α

instance [Add α] : Add (PPoint α) where
  add p q := { x := p.x + q.x, y := p.y + q.y }

-- 3.2.3 Methods and Implicit Arguments

-- a type class declaration results in the following:
-- - a structure type to contain the impl of each overloaded op
-- - a namespace with the same name as the class
-- - for each method, a function in the namespace that retrieves its impl from an instance

-- 3.2.4 Exercises

-- 3.2.4.1 Even Number Literals
-- Write an instance of `OfNat` for the even number datatype from the previous section's
-- exercises that uses recursive instance search.

instance [Inhabited Even] : OfNat Even n where
  ofNat := if n % 2 == 0 then .mul2 (n / 2) else panic! s!"{n} is odd"

-- 3.2.4.2. Recursive Instance Search Depth
-- There is a limit to how many times the Lean compiler will attempt a recursive instance
-- search. This places a limit on the size of even number literals defined in the previous
-- exercise. Experimentally determine what the limit is.

section

set_option synthInstance.maxSize 2

instance : Inhabited Even where default := .zero

/--
info: 2
-/
#guard_msgs (info) in
#eval (2 : Even)

/--
PANIC at instOfNatEvenOfInhabited FunctionalProgrammingInLean.OverloadingAndTypeClasses:137:49: 3 is odd
-/
#guard_msgs (substring := true) in
#eval (3 : Even)

/--
info: 42
-/
#guard_msgs (info) in
#eval (42 : Even)

end

-- 3.3 Controlling Instance Search

-- 3.3.1 Heterogeneous Overloadings

instance : HAdd Nat Pos Pos where
  hAdd :=
    let rec hAdd : Nat → Pos → Pos
      | 0, p => p
      | n + 1, p => .succ (hAdd n p)
    hAdd

instance : HAdd Pos Nat Pos where
  hAdd :=
    let rec hAdd : Pos → Nat → Pos
      | p, 0 => p
      | p, n + 1 => .succ (hAdd p n)
    hAdd

instance : ToString Pos where toString p := s!"{p.toNat}"

#eval (3 : Pos) + (2 : Nat)
#eval (3 : Nat) + (2 : Pos)

-- 3.3.2 Output Parameters

class HPlus (α : Type u) (β : Type v) (γ : outParam (Type (max u v))) where
  hPlus : α → β → γ

instance [HAdd α β γ] : HPlus α β γ where hPlus := HAdd.hAdd

#eval HPlus.hPlus (3 : Pos) (2 : Nat)
#eval HPlus.hPlus (3 : Nat) (2 : Pos)

-- 3.3.3 Default Instances

#check HPlus.hPlus (3 : Nat)
-- HPlus.hPlus 3 : ?m.2 → ?m.3

@[default_instance]
instance [Add α] : HPlus α α α where hPlus := Add.add

#check HPlus.hPlus (3 : Nat)
-- HPlus.hPlus 3 : Nat → Nat

-- default instances can be given priorities

-- 3.3.4 Exercises
-- Define an instance of `HMul (PPoint α) α (PPoint α)` that multiplies both projections
-- by the scalar. It should work for any type α for which there is a Mul α instance. For
-- example,
-- #eval {x := 2.5, y := 3.7 : PPoint Float} * 2.0
-- should yield { x := 5.000000, y := 7.400000 }

instance [Mul α] : HMul (PPoint α) α (PPoint α) where
  hMul p a := { x := p.x * a, y := p.y * a }

#eval {x := 2.5, y := 3.7 : PPoint Float} * 2.0
-- { x := 5.000000, y := 7.400000 }

-- 3.4 Arrays and Indexing

-- index accessors are governed by a type class

-- 3.4.1 Arrays

def arr : Array String := #["a", "b"]

#eval arr[0]
-- "a"

/--
error: failed to prove index is valid, possible solutions:
  - Use `have`-expressions to prove the index is valid
  - Use `a[i]!` notation instead, runtime check is performed, and 'Panic' error message is produced if index is not valid
  - Use `a[i]?` notation instead, result is an `Option` type
  - Use `a[i]'h` notation instead, where `h` is a proof that index is valid
⊢ 3 < arr.size
-/
#guard_msgs (error) in
#eval arr[3]

-- 3.4.2 Non-empty Lists

structure NonEmptyList (α : Type u) where
  head : α
  tail : List α

def NonEmptyList.get? : NonEmptyList α → Nat → Option α
  | {head, ..}, 0 => some head
  | {tail, ..}, n + 1 => tail[n]?

-- make an `abbrev` so tactics can use as evidence
abbrev NonEmptyList.inBounds (as : NonEmptyList α) (i : Nat) : Prop :=
  i ≤ as.tail.length

def neList : NonEmptyList String :=
  { head := "a", tail := ["b", "c"]}

example : neList.inBounds 2 := by decide
example : ¬neList.inBounds 3 := by decide

def NonEmptyList.get (as : NonEmptyList α) (i : Nat) (ok : as.inBounds i) :=
  match i with
  | 0 => as.head
  | n + 1 => as.tail[n]

-- 3.4.3 Overloading Indexing

-- `GetElem` type class

instance : GetElem (NonEmptyList α) (Nat) α NonEmptyList.inBounds where
  getElem := NonEmptyList.get

#eval neList[2]
-- "c"

-- index List with Pos
instance : GetElem (List α) Pos α (fun list n => list.length > n.toNat) where
  getElem as i _ := as[i.toNat]

-- index PPoint with Bool
instance : GetElem (PPoint α) Bool α (fun _ _ => True) where
  getElem p b _ := if not b then p.x else p.y

-- 3.5 Standard Classes

-- 3.5.1 Arithmetic

-- Expression   Desugaring
-- x + y        HAdd.hAdd x y
-- x - y        HSub.hSub x y
-- x * y        HMul.hMul x y
-- x / y        HDiv.hDiv x y
-- x % y        HMod.hMod x y
-- x ^ y        HPow.hPow x y
-- x            Neg.neg x

-- 3.5.2 Bitwise Operators

-- instances for fixed-width types such as `UInt8`, `UInt16`, `UInt32`, `UInt64`, and `USize`

-- Expression   Desugaring
-- x &&& y      HAnd.hAnd x y
-- x ||| y      HOr.hOr x y
-- x ^^^ y      HXor.hXor x y
-- ~~~x         Complement.complement x
-- x >>> y      HSiftRight.hSiftRight x y
-- x <<< y      HShiftLeft.hShiftLeft x y

-- 3.5.3 Equality and Ordering

-- Boolean equality - function
#check BEq.beq
-- BEq.beq.{u} {α : Type u} [self : BEq α] : α → α → Bool

/--
error: failed to synthesize instance of type class
  BEq (Nat → Nat)

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs (error) in
#eval (fun n => n + 1) == (Nat.succ ·)

-- Propositional equality -mathematical statement
#check Eq
-- Eq.{u_1} {α : Sort u_1} : α → α → Prop

-- can state and prove function equality propositionally
example : (fun n => n + 1) = (Nat.succ ·) := rfl

-- decidable propositions:
-- - equality and inequality of natural numbers
-- - equality of strings
-- - conjunctions, disjuctions, negations of decidable propositions

#check 2 < 4
-- 2 < 4 : Prop

#eval 2 < 4
-- true

#check Decidable.decide
-- Decidable.decide (p : Prop) [h : Decidable p] : Bool

-- the following propositions, usually decidable, are overloaded with type classes:

-- Expression   Desugaring
-- x < y        LT.lt x y
-- x ≤ y        LE.le x y
-- x > y        LT.lt y x
-- x ≥ y        LE.le y x

instance : LT Pos where
  lt x y := LT.lt x.toNat y.toNat

instance : LE Pos where
  le x y := LE.le x.toNat y.toNat

-- use `inferInstance` for decidability

instance {x y : Pos} : Decidable (x < y) :=
  (inferInstance : Decidable (x.toNat < y.toNat))

instance {x y : Pos} : Decidable (x ≤ y) :=
  (inferInstance : Decidable (x.toNat ≤ y.toNat))

instance : Ord Pos where
  compare x y := Ord.compare x.toNat y.toNat

-- 3.5.4 Hashing

#check Hashable.hash
-- Hashable.hash.{u} {α : Sort u} [self : Hashable α] : α → UInt64

-- if x == y then hash x == hash y
example : Hashable.hash (true && false) == Hashable.hash false := rfl

-- `mixHash : UInt64 → UInt64 → UInt64`

instance : Hashable Pos where
  hash :=
    let rec hash : Pos → UInt64
      | .one => 0
      | .succ p => mixHash 1 (hash p)
    hash

-- recursive instance search

instance [Hashable α] : Hashable (NonEmptyList α) where
  hash ne := mixHash (hash ne.head) (hash ne.tail)

-- binary trees
-- recursion and recursive instance search

inductive BinTree (α : Type) where
  | leaf
  | branch : BinTree α → α → BinTree α → BinTree α
deriving Repr

def BinTree.eq [BEq α] : BinTree α → BinTree α → Bool
  | leaf, leaf => true
  | branch l1 x1 r1, branch l2 x2 r2 =>
    x1 == x2 && eq l1 l2 && eq r1 r2
  | _, _ => false

instance [BEq α] : BEq (BinTree α) where
  beq := BinTree.eq

def BinTree.hash [Hashable α] : BinTree α → UInt64
  | leaf => 0
  | branch l x r =>
    mixHash 1 <| mixHash (hash l) <| mixHash (Hashable.hash x) (hash r)

instance [Hashable α] : Hashable (BinTree α) where
  hash := BinTree.hash

-- 3.5.5 Deriving Standard Classes

-- add `deriving C1, ...` at the end of the definition
-- or
-- declare `deriving instance C1, ... for T`

deriving instance BEq, Hashable for Pos
deriving instance BEq, Hashable for NonEmptyList

-- instances can be derived for at least the following classes:
-- `Inhabited`
-- `BEq`
-- `Repr`
-- `Hashable`
-- `Ord`

-- the collection of derivable classes can be extended

-- 3.5.6 Appending

#check HAppend
-- HAppend.{u, v, w} (α : Type u) (β : Type v) (γ : outParam (Type w)) : Type (max (max u v) w)

-- homogeneous append
instance : Append (NonEmptyList α) where
  append xs ys := { head := xs.head, tail := xs.tail ++ ys.head :: ys.tail }

#eval neList ++ neList
-- { head := "a", tail := ["b", "c", "a", "b", "c"] }

instance : HAppend (NonEmptyList α) (List α) (NonEmptyList α) where
  hAppend ne l := { head := ne.head, tail := ne.tail ++ l }

#eval neList ++ ["d"]
-- { head := "a", tail := ["b", "c", "d"] }

-- 3.5.7 Functors

#check Functor
-- Functor.{u, v} (f : Type u → Type v) : Type (max (u + 1) v)

#eval Functor.map (· + 5) [1, 2, 3]
-- [6, 7, 8]

#eval (· + 5) <$> [1, 2, 3]
-- [6, 7, 8]

-- example Functor instances

instance : Functor NonEmptyList where
  map f ne := { head := f ne.head, tail := f <$> ne.tail }

instance : Functor PPoint where
  map f p := { x := f p.x, y := f p.y }

-- default method definitions (implemented in class) can be overridden by instance

-- Functor instances should respect id and function composition

theorem NonEmptyList.respectsId {ne : NonEmptyList α} : id <$> ne = ne := by
  simp [Functor.map]

theorem NonEmptyList.respectsComp {ne : NonEmptyList α} {f : α → β} {g : β → γ}
    : (g ∘ f) <$> ne = g <$> f <$> ne := by
  simp [Functor.map]

theorem PPoint.respectsId {p : PPoint α} : id <$> p = p := by
  simp [Functor.map]

theorem PPoint.respectsComp {p : PPoint α} {f : α → β} {g : β → γ}
    : (g ∘ f) <$> p = g <$> f <$> p := by
  simp [Functor.map]

-- 3.5.9 Exercises

-- Write an instance of `HAppend (List α) (NonEmptyList α) (NonEmptyList α)` and test it.

instance : HAppend (List α) (NonEmptyList α) (NonEmptyList α) where
  hAppend l ne := match l with
    | [] => ne
    | h :: t => { head := h, tail := t ++ ne.head :: ne.tail }

#eval ["0"] ++ neList
-- { head := "0", tail := ["a", "b", "c"] }

-- Implement a `Functor` instance for the binary tree datatype.

instance : Functor BinTree where
  map f :=
    let rec map {α β} (f : α → β) : BinTree α → BinTree β
      | .leaf => .leaf
      | .branch l x r => .branch (map f l) (f x) (map f r)
    map f

#eval (· + 1) <$> BinTree.branch .leaf 0 .leaf
-- BinTree.branch (BinTree.leaf) 1 (BinTree.leaf)

-- 3.6 Coercions
