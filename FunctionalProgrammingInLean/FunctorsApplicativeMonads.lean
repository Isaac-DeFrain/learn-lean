/- 5. Functors, Applicative Functors, and Monads -/

import FunctionalProgrammingInLean.Monads

-- `Functor` describes data containers in which the data can be transformed
-- `Monad` describes an encoding of programs with side effects

-- every monad is a functor
-- every monad is an applicative functor
-- every applicative functor is a functor

#print Functor
-- class Functor.{u, v} (f : Type u → Type v) : Type (max (u + 1) v)
-- number of parameters: 1
-- fields:
--   Functor.map : {α β : Type u} → (α → β) → f α → f β
--   Functor.mapConst : {α β : Type u} → α → f β → f α :=
--     fun {α β} => Functor.map ∘ Function.const β
-- constructor:
--   Functor.mk.{u, v} {f : Type u → Type v} (map : {α β : Type u} → (α → β) → f α → f β)
--     (mapConst : {α β : Type u} → α → f β → f α) : Functor f

#print Applicative
-- class Applicative.{u, v} (f : Type u → Type v) : Type (max (u + 1) v)
-- number of parameters: 1
-- parents:
--   Applicative.toFunctor : Functor f
--   Applicative.toPure : Pure f
--   Applicative.toSeq : Seq f
--   Applicative.toSeqLeft : SeqLeft f
--   Applicative.toSeqRight : SeqRight f
-- fields:
--   Functor.map : {α β : Type u} → (α → β) → f α → f β :=
--     fun {α β} x y => pure x <*> y
--   Functor.mapConst : {α β : Type u} → α → f β → f α :=
--     fun {α β} => Functor.map ∘ Function.const β
--   Pure.pure : {α : Type u} → α → f α
--   Seq.seq : {α β : Type u} → f (α → β) → (Unit → f α) → f β
--   SeqLeft.seqLeft : {α β : Type u} → f α → (Unit → f β) → f α :=
--     fun {α β} a b => Function.const β <$> a <*> b ()
--   SeqRight.seqRight : {α β : Type u} → f α → (Unit → f β) → f β :=
--     fun {α β} a b => Function.const α id <$> a <*> b ()
-- constructor:
--   Applicative.mk.{u, v} {f : Type u → Type v} [toFunctor : Functor f] [toPure : Pure f] [toSeq : Seq f]
--     [toSeqLeft : SeqLeft f] [toSeqRight : SeqRight f] : Applicative f
-- field notation resolution order:
--   Applicative, Functor, Pure, Seq, SeqLeft, SeqRight

#print Monad
-- class Monad.{u, v} (m : Type u → Type v) : Type (max (u + 1) v)
-- number of parameters: 1
-- parents:
--   Monad.toApplicative : Applicative m
--   Monad.toBind : Bind m
-- fields:
--   Functor.map : {α β : Type u} → (α → β) → m α → m β :=
--     fun {α β} f x => x >>= pure ∘ f
--   Functor.mapConst : {α β : Type u} → α → m β → m α :=
--     fun {α β} => Functor.map ∘ Function.const β
--   Pure.pure : {α : Type u} → α → m α
--   Seq.seq : {α β : Type u} → m (α → β) → (Unit → m α) → m β :=
--     fun {α β} f x => do
--       let y ← f
--       y <$> x ()
--   SeqLeft.seqLeft : {α β : Type u} → m α → (Unit → m β) → m α :=
--     fun {α β} x y => do
--       let a ← x
--       let _ ← y ()
--       pure a
--   SeqRight.seqRight : {α β : Type u} → m α → (Unit → m β) → m β :=
--     fun {α β} x y => do
--       let _ ← x
--       y ()
--   Bind.bind : {α β : Type u} → m α → (α → m β) → m β
-- constructor:
--   Monad.mk.{u, v} {m : Type u → Type v} [toApplicative : Applicative m] [toBind : Bind m] : Monad m
-- field notation resolution order:
--   Monad, Applicative, Bind, Functor, Pure, Seq, SeqLeft, SeqRight

-- 5.1 Structures and Inheritance

structure MythicalCreature where
  large : Bool
deriving Repr

#check (⟨true⟩ : MythicalCreature)

#check MythicalCreature.mk
-- MythicalCreature.mk (large : Bool) : MythicalCreature

#check MythicalCreature.large
-- MythicalCreature.large (self : MythicalCreature) : Bool

structure Monster extends MythicalCreature where
  weakness : String
deriving Repr

def troll : Monster where
  large := true
  weakness := "sunlight"

-- inheritance is implemented using composition

#check Monster.mk
-- Monster.mk (toMythicalCreature : MythicalCreature) (weakness : String) : Monster

#eval troll.large
#eval troll.weakness
#check (troll.toMythicalCreature : MythicalCreature)

-- moving up the inheritance hierarchy is not the same as upcasting

def MythicalCreature.small (c : MythicalCreature) : Bool := !c.large

#eval troll.small

-- 5.1.1 Multiple Inheritance

structure Helper extends MythicalCreature where
  assistance : String
  payment : String
deriving Repr

def nisse : Helper where
  large := false
  assistance := "household tasks"
  payment := "porridge"

structure MonsterousAssistant extends Monster, Helper where
deriving Repr

def domesticatedTroll : MonsterousAssistant :=
  { troll with assistance := "heavy labor", payment := "goats" }

-- first specified path to the ancestor is taken to solve the "diamond problem"

#check MonsterousAssistant.mk
-- MonsterousAssistant.mk (toMonster : Monster) (assistance payment : String) : MonsterousAssistant

-- simply extracts the Monster
#print MonsterousAssistant.toMonster
-- @[reducible] def MonsterousAssistant.toMonster : MonsterousAssistant → Monster :=
-- fun self => self.1

-- no Helper to extract
#print MonsterousAssistant.toHelper
-- @[reducible] def MonsterousAssistant.toHelper : MonsterousAssistant → Helper :=
-- fun self => { toMythicalCreature := self.toMythicalCreature, assistance := self.assistance, payment := self.payment }

-- @[reducible] attribute has the same effect as writing `abbrev`

-- 5.1.1.1 Default Declarations

inductive Size where
  | small
  | medium
  | large
deriving BEq

structure SizedCreature extends MythicalCreature where
  size : Size
  large := size == .large -- parent inherits `large` value from child

-- default is only used when no alternative is declared

def nonsenseCreature : SizedCreature where
  large := false
  size := .large

-- if child structure should not deviate from the parent, options:
-- 1. document the relationship, as is done for `BEq` and `Hashable`
-- 2. define a proposition that the fields are related appropriately, and design the API
--    to require evidence that the proposition is true where it matters
-- 3. do not use inheritance

-- example of 2.

structure SensibleSizedCreature extends SizedCreature where
  sizesMatch : large = (size == .large)

/--
error: Tactic `decide` proved that the proposition
  nonsenseCreature.large = (nonsenseCreature.size == Size.large)
is false
-/
#guard_msgs (error) in
#check ({ nonsenseCreature with sizesMatch := by decide } : SensibleSizedCreature)

def sensibleCreature : SizedCreature where
  large := false
  size := .medium

#check ({ sensibleCreature with sizesMatch := by decide } : SensibleSizedCreature)

-- 5.1.1.2 Type Class Inheritance

class A where
  a : Nat

class B extends A where
  b : String

instance : B := { a := 0, b := "hello" }

-- 5.2 Applicative Functors

-- `Applicative f` extends `Functor f`, `Pure f`, `Seq f`, `SeqLeft f`, and `SeqRight f`

#print Pure
-- class Pure.{u, v} (f : Type u → Type v) : Type (max (u + 1) v)
-- number of parameters: 1
-- fields:
--   Pure.pure : {α : Type u} → α → f α
-- constructor:
--   Pure.mk.{u, v} {f : Type u → Type v} (pure : {α : Type u} → α → f α) : Pure f

#print Seq
-- class Seq.{u, v} (f : Type u → Type v) : Type (max (u + 1) v)
-- number of parameters: 1
-- fields:
--   Seq.seq : {α β : Type u} → f (α → β) → (Unit → f α) → f β
-- constructor:
--   Seq.mk.{u, v} {f : Type u → Type v} (seq : {α β : Type u} → f (α → β) → (Unit → f α) → f β) : Seq f

#print SeqLeft
-- class SeqLeft.{u, v} (f : Type u → Type v) : Type (max (u + 1) v)
-- number of parameters: 1
-- fields:
--   SeqLeft.seqLeft : {α β : Type u} → f α → (Unit → f β) → f α
-- constructor:
--   SeqLeft.mk.{u, v} {f : Type u → Type v} (seqLeft : {α β : Type u} → f α → (Unit → f β) → f α) : SeqLeft f

#print SeqRight
-- class SeqRight.{u, v} (f : Type u → Type v) : Type (max (u + 1) v)
-- number of parameters: 1
-- fields:
--   SeqRight.seqRight : {α β : Type u} → f α → (Unit → f β) → f β
-- constructor:
--   SeqRight.mk.{u, v} {f : Type u → Type v} (seqRight : {α β : Type u} → f α → (Unit → f β) → f β) : SeqRight f

-- an _applicative functor_ is a functor that has two additional operations: `pure` and `seq`

#check Applicative.toPure.pure

#check Applicative.toSeq.seq
-- `seq` is like `map` except the function is itself contained in a datatype: `f (α → β) → (Unit → f α) → f β`

-- having the function under the type `f` allows the `Applicative` instance to control
-- how the function is applied, while `Functor.map` unconditionally applies a function

-- second arg has a type that begins with `Unit →` to allow the definition of `seq` to
-- short-circuit in cases where the function will never be applied

instance : Applicative Option where
  pure := some
  seq
    | none, _ => none
    | some f, x => f <$> x ()

instance : Applicative (Except ε) where
  pure := .ok
  seq
    | .error e, _ => .error e
    | .ok f, x => f <$> x ()

-- successive uses of monad bind are like a sequence of statements in an imperative language
-- bind is powerful enough to implement control structures like conditionals and loops

-- `Applicative` captures function application in a language that has side effects

example [Seq s] (e1 : s (α → β)) : e1 <*> e2 = Seq.seq e1 (fun () => e2) := rfl

#check (some Nat.add <*> some 19 : Option (Nat → Nat))
#eval some Nat.add <*> some 19 <*> some 23
-- some 42

-- example of non-applicative functor

structure Pair (α β : Type u) where
  fst : α
  snd : β

instance : Functor (Pair α) where
  map f x := ⟨ x.fst, f x.snd ⟩

-- obeys Functor contract
example (p : Pair α β) : id <$> p = p := rfl
example (p : Pair α β) : g <$> f <$> p = (g ∘ f) <$> p := rfl

-- cannot define an instance of `Applicative` because of `pure`

-- 5.2.1 A Non-Monadic Applicative

-- validation of user input - want to return a list of errors at the end

-- 5.2.1.1 User Input

structure RawInput where
  name : String
  birthYear : String


-- The business logic to be implemented is the following:
-- 1. The name may not be empty
-- 2. The birth year must be numeric and non-negative
-- 3. The birth year must be greater than 1900, and less than or equal to the year
--    in which the form is validated

-- 5.2.1.2 Subtypes

#print Subtype
-- structure Subtype.{u} {α : Sort u} (p : α → Prop) : Sort (max 1 u)
-- number of parameters: 2
-- fields:
--   Subtype.val : α
--   Subtype.property : p self.val
-- constructor:
--   Subtype.mk.{u} {α : Sort u} {p : α → Prop} (val : α) (property : p val) : Subtype p

example : {x : α // p x} = Subtype p := rfl

-- positive numbers with all the benefits of Nat impl
abbrev FastPos : Type := {x : Nat // x > 0}

def one : FastPos := ⟨1, by decide⟩

instance : OfNat FastPos (n + 1) where
  ofNat := ⟨n + 1, by simp⟩

-- users of a library with subtypes have to prove that properties hold

-- `{x // p x}` usually requires proposition `p x` to be decidable

def Nat.asFastPos? (n : Nat) : Option FastPos :=
  if h : n > 0 then
    some ⟨n, h⟩
  else none

-- 5.2.1.3 Validated Input

structure CheckedInput (thisYear : Nat) : Type where
  name : {n // n ≠ ""}
  birthYear : {y // y > 1900 ∧ y ≤ thisYear}
deriving Repr

deriving instance Repr for NonEmptyList

inductive Validate (ε α : Type) : Type where
  | ok : α → Validate ε α
  | errors : NonEmptyList ε → Validate ε α
deriving Repr

instance : Functor (Validate ε) where
  map f
    | .ok x => .ok (f x)
    | .errors errs => .errors errs

-- errors accumulate

instance : Applicative (Validate ε) where
  pure := .ok
  seq f x :=
    match f with
    | .ok f => f <$> x ()
    | .errors errs =>
      match x () with
      | .ok _ => .errors errs
      | .errors errs' => .errors (errs ++ errs')

def Field := String

def reportError (f : Field) (msg : String) : Validate (Field × String) α :=
  .errors { head := (f, msg), tail := [] }

def checkName (name : String) : Validate (Field × String) {n // n ≠ ""} :=
  if h : name ≠ "" then
    pure ⟨name, h⟩
  else
    reportError "name" "Required"

def Validate.andThen (val : Validate ε α)
    (next : α → Validate ε β) : Validate ε β :=
  match val with
  | .ok x => next x
  | .errors errs => .errors errs

def checkYearIsNat (year : String) : Validate (Field × String) Nat :=
  match year.trimAscii.toNat? with
  | none => reportError "birth year" "Must be digits"
  | some year => pure year

def checkBirthYear (thisYear year : Nat)
    : Validate (Field × String) {y // y > 1900 ∧ y ≤ thisYear} :=
  if h : year > 1900 then
    if h' : year ≤ thisYear then
      pure ⟨year, by simp [*]⟩
    else reportError "birth year" s!"Must be no later than {thisYear}"
  else reportError "birth year" "Must be after 1900"

def checkInput (year : Nat) (input : RawInput)
    : Validate (Field × String) (CheckedInput year) :=
  pure CheckedInput.mk <*>
    checkName input.name <*>
      (checkYearIsNat input.birthYear).andThen
        (checkBirthYear year ·)

#eval checkInput 2026 {name := "David", birthYear := "1984"}
-- Validate.ok { name := "David", birthYear := 1984 }

#eval checkInput 2026 {name := "", birthYear := ""}
-- Validate.errors { head := ("name", "Required"), tail := [("birth year", "Must be digits")] }

#eval checkInput 2026 {name := "Isaac", birthYear := "2027"}
-- Validate.errors { head := ("birth year", "Must be no later than 2026"), tail := [] }
