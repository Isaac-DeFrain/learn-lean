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

-- errors accumulate - this would be incompatible with a monad instance
instance : Applicative (Validate ε) where
  pure := .ok
  seq f x :=
    match f with
    | .ok f => f <$> x ()
    | .errors errs =>
      match x () with
      | .ok _ => .errors errs
      | .errors errs' => .errors (errs ++ errs')

abbrev Field := String

def reportError (f : Field) (msg : String) : Validate (Field × String) α :=
  .errors { head := (f, msg), tail := [] }

def checkName (name : String) : Validate (Field × String) {n // n ≠ ""} :=
  if h : name ≠ "" then
    pure ⟨name, h⟩
  else
    reportError "name" "Required"

-- resembles `Bind.bind` but `Validate ε` cannot be turned into a monad because
-- it would have a bad interaction between `seq` and `bind`
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

-- 5.3 The Applicative Contract

class ApplicativeContract (f : Type u → Type v) [Applicative f] where
  pure_identity : ∀ x : f α, pure id <*> x = x
  pure_seq_noop : ∀ x g, (pure g : f (α → β)) <*> pure x = pure (g x)
  pure_ordering : ∀ x (u : f (α → β)), u <*> pure x = pure (· x) <*> u
  respects_comp :
    ∀ (u : f (β → γ)) (v : f (α → β)) w, pure (· ∘ ·) <*> u <*> v <*> w = u <*> (v <*> w)

instance : ApplicativeContract Option where
  pure_identity _ := by simp [Seq.seq]
  pure_seq_noop _ _ := by simp [Seq.seq]
  pure_ordering _ g := by simp [Seq.seq]; cases g <;> rfl
  respects_comp u v _ := by simp [Seq.seq]; cases u <;> cases v <;> simp

-- 5.3.1 All Applicatives are Functors

class FunctorContract (f : Type u → Type v) [Functor f] where
  map_identity : ∀ x : f α, id <$> x = x
  map_composition :
    ∀ (x : f α) (g : α → β) (h : β → γ), (h ∘ g) <$> x = h <$> g <$> x

instance [Applicative f] : Functor f where
  map f x := pure f <*> x

instance [Applicative f] [ApplicativeContract f] : FunctorContract f where
  map_identity _ := by
    simp [Functor.map, ApplicativeContract.pure_identity]
  map_composition x g h := by
    simp [Functor.map, ←ApplicativeContract.respects_comp (pure h) (pure g) x]
    simp [ApplicativeContract.pure_seq_noop]

-- 5.3.2 All Monads are Applicative Functors

class MonadContract (m : Type u → Type v) [Monad m] where
  left_identity : ∀ x (f : α → m β), pure x >>= f = f x
  right_identity : ∀ x : m α, x >>= pure = x
  bind_identity :
    ∀ x (f : α → m β) (g : β → m γ), x >>= f >>= g = x >>= (fun x => (f x) >>= g)

instance (priority := high) [Monad m] : Applicative m where
  pure := pure
  seq f x := do
    let f ← f
    let x ← x ()
    pure (f x)

instance [Monad m] [MonadContract m] : ApplicativeContract m where
  pure_identity _ := by
    simp [Seq.seq, MonadContract.left_identity, MonadContract.right_identity]
  pure_seq_noop _ _ := by
    simp [Seq.seq, MonadContract.left_identity]
  pure_ordering _ _ := by
    simp [Seq.seq, MonadContract.left_identity]
  respects_comp _ _ _ := by
    simp [Seq.seq, MonadContract.left_identity, MonadContract.bind_identity]

-- 5.3.3 Additional Stipulations

-- the interaction between `seq` and `bind` should always be as in the above instance
-- this is the problem with implementing `Monad (Validate ε)`:

-- say we have

def notFun : Validate String (Nat → String) :=
  .errors { head := "First error", tail := [] }

def notArg : Validate String Nat :=
  .errors { head := "Second error", tail := [] }

#eval notFun <*> notArg
-- Validate.errors { head := "First error", tail := ["Second error"] }

-- but if we implement
instance : Monad (Validate ε) where
  pure := pure
  bind
    | .ok x, f => f x
    | .errors errs, _ => .errors errs

-- we only capture the first error with the bind impl of seq
#eval notFun <*> notArg
-- Validate.errors { head := "First error", tail := [] }

-- 5.4 Alternatives

-- 5.4.1 Recovery from Failure

-- an alternative set of business rules that implement conventions from a legacy system
-- might be the following:
-- 1. All human users must provide a birth year that is four digits.
-- 2. Users born prior to 1970 do not need to provide names, due to incomplete older records.
-- 3. Users born on or after 1970 must provide names.
-- 3. Companies should enter "FIRM" as their year of birth and provide a company name.

abbrev NonEmptyString := {s : String // s ≠ ""}

inductive LegacyCheckedInput where
  | humanBefore1970 :
    (birthYear : {y // y > 999 ∧ y < 1970}) →
    String →
    LegacyCheckedInput
  | humanAfter1970 :
    (birthYear : {y // y ≥ 1970}) →
    NonEmptyString →
    LegacyCheckedInput
  | company : NonEmptyString → LegacyCheckedInput
deriving Repr

-- recover from failure while preserving errors

def Validate.orElse (a : Validate ε α) (b : Unit → Validate ε α) : Validate ε α :=
  match a with
  | .ok a => .ok a
  | .errors errs =>
    match b () with
    | .ok b => b
    | .errors errs' => .errors (errs ++ errs')

example [OrElse t] (e1 e2 : t) : (e1 <|> e2) = OrElse.orElse e1 (fun () => e2) := rfl

instance : OrElse (Validate ε α) where
  orElse := .orElse

-- build validator for `LegacyCheckedInput` from a validator for each constructor

-- check that a Boolean condition holds without recording any evidence of this fact in a type
def checkThat (cond : Bool) (field : Field) (msg : String)
    : Validate (Field × String) Unit :=
  if cond then pure () else reportError field msg

def checkCompany' (input : RawInput) : Validate (Field × String) LegacyCheckedInput :=
  pure (fun () => .company) <*>
    checkThat (input.birthYear == "FIRM") "birth year" "FIRM if a company" <*>
    checkName input.name

example [SeqRight t] (e1 e2 : t α)
    : (e1 *> e2) = SeqRight.seqRight e1 (fun () => e2) := rfl

-- default impl of `SeqRight` for `Seq + Pure`
instance [Seq t] [Pure t] : SeqRight t where
  seqRight x y := pure (fun _ x => x) <*> x <*> y ()

-- simplify `checkCompany'` with `*>`

def checkCompany (input : RawInput) : Validate (Field × String) LegacyCheckedInput :=
  checkThat (input.birthYear == "FIRM") "birth year" "FIRM if a company" *>
    .company <$> checkName input.name

-- general-purpose tool for checking subtypes
def checkSubtype {α : Type} (v : α) (p : α → Prop) [Decidable (p v)] (err : ε)
    : Validate ε {x // p x} :=
  if h : p v then
    pure ⟨v, h⟩
  else
    .errors { head := err, tail := [] }

def checkHumanBefore1970 (input : RawInput) : Validate (Field × String) LegacyCheckedInput :=
  (checkYearIsNat input.birthYear).andThen fun y =>
    .humanBefore1970 <$>
      checkSubtype y (fun y => y > 999 ∧ y < 1970) ("birth year", "less than 1970") <*>
      pure input.name

def checkHumanAfter1970 (input : RawInput) : Validate (Field × String) LegacyCheckedInput :=
  (checkYearIsNat input.birthYear).andThen fun y =>
    .humanAfter1970 <$>
      checkSubtype y (· ≥ 1970) ("birth year", "greater than 1970") <*>
      checkName input.name

def checkLegacyInput (input : RawInput) : Validate (Field × String) LegacyCheckedInput :=
  checkCompany input <|> checkHumanBefore1970 input <|> checkHumanAfter1970 input

#eval checkLegacyInput ⟨"Johnny's Troll Groomers", "FIRM"⟩
-- Validate.ok (LegacyCheckedInput.company "Johnny's Troll Groomers")

#eval checkLegacyInput ⟨"Johnny", "1963"⟩
-- Validate.ok (LegacyCheckedInput.humanBefore1970 1963 "Johnny")

#eval checkLegacyInput ⟨"", "1963"⟩
-- Validate.ok (LegacyCheckedInput.humanBefore1970 1963 "")

#eval checkLegacyInput ⟨"", "1970"⟩
-- Validate.errors
--   { head := ("birth year", "FIRM if a company"),
--     tail := [("birth year", "less than 1970"), ("name", "Required")] }

-- 5.4.2 The `Alternative` Class

-- types supprting failure and recovery

#print OrElse
-- class OrElse.{u} (α : Type u) : Type u
-- number of parameters: 1
-- fields:
--   OrElse.orElse : α → (Unit → α) → α
-- constructor:
--   OrElse.mk.{u} {α : Type u} (orElse : α → (Unit → α) → α) : OrElse α

-- applicative functors with additional operators for failure and recovery
#print Alternative
-- class Alternative.{u, v} (f : Type u → Type v) : Type (max (u + 1) v)
-- number of parameters: 1
-- parents:
--   Alternative.toApplicative : Applicative f
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
--   Alternative.failure : {α : Type u} → f α
--   Alternative.orElse : {α : Type u} → f α → (Unit → f α) → f α
-- constructor:
--   Alternative.mk.{u, v} {f : Type u → Type v} [toApplicative : Applicative f] (failure : {α : Type u} → f α)
--     (orElse : {α : Type u} → f α → (Unit → f α) → f α) : Alternative f
-- field notation resolution order:
--   Alternative, Applicative, Functor, Pure, Seq, SeqLeft, SeqRight

-- Alternative => OrElse
instance [Alternative t] : OrElse (t α) where
  orElse := Alternative.orElse

instance : Alternative Option where
  failure := none
  orElse
    | none, y => y ()
    | some x, _ => some x

-- `Many` is an instance of `Alternative`

def Many.orElse : Many α → (Unit → Many α) → Many α
  | .none, m => m ()
  | .more x xs, m => .more x (fun () => (xs ()).orElse m)

instance : Alternative Many where
  failure := .none
  orElse := .orElse

#print guard
-- def guard.{v} : {f : Type → Type v} → [Alternative f] → (p : Prop) → [Decidable p] → f Unit :=
-- fun {f} [Alternative f] p [Decidable p] => if p then pure () else failure

-- `guard` can be used to cancel entire branches of computation in monadic programs

def Many.countdown : Nat → Many Nat
  | 0 => .none
  | n + 1 => .more n (fun () => countdown n)

def evenDivisors (n : Nat) : Many Nat := do
  let k ← .countdown (n + 1)
  guard (k % 2 = 0) -- even
  guard (n % k = 0) -- divisor
  pure k

#eval (evenDivisors 20).takeAll
-- [20, 10, 4, 2]

-- 5.4.3 Exercises

-- 5.4.3.1 Improve Validation Friendliness

-- The errors returned from `Validate` programs that use `<|>` can be difficult to read,
-- because inclusion in the list of errors simply means that the error can be reached
-- through _some_ code path. A more structured error report can be used to guide the user
-- through the process more accurately:

-- - Replace the `NonEmptyList` in `Validate.errors` with a bare type variable, and then
--   update the definitions of the `Applicative (Validate ε)` and `OrElse (Validate ε α)`
--   instances to require only that there be an `Append ε` instance available.

-- - Define a function `Validate.mapErrors : Validate ε α → (ε → ε') → Validate ε' α` that
--   transforms all the errors in a validation run.

-- - Using the datatype `TreeError` to represent errors, rewrite the legacy validation system
--   to track its path through the three alternatives.

-- - Write a function `report : TreeError → String` that outputs a user-friendly view of the
--   `TreeError`'s accumulated warnings and errors.

namespace Hidden

inductive Validate (ε α : Type) : Type where
  | ok : α → Validate ε α
  | errors : ε → Validate ε α

instance : Functor (Validate ε) where
  map f
    | .ok x => .ok (f x)
    | .errors errs => .errors errs

-- errors accumulate
instance [Append ε] : Applicative (Validate ε) where
  pure := .ok
  seq
    | .ok f, x => f <$> x ()
    | .errors errs, x =>
      match x () with
      | .ok _ => .errors errs
      | .errors errs' => .errors (errs ++ errs')

instance [Append ε] : OrElse (Validate ε α) where
  orElse
    | .ok x, _ => .ok x
    | .errors errs, y =>
      match y () with
      | .ok y => .ok y
      | .errors errs' => .errors (errs ++ errs')

def Validate.mapErrors : Validate ε α → (ε → ε') → Validate ε' α
  | .ok x, _ => .ok x
  | .errors errs, f => .errors (f errs)

deriving instance Repr for Field

inductive TreeError where
  | field : Field → String → TreeError
  | path : String → TreeError → TreeError
  | both : TreeError → TreeError → TreeError
deriving Repr

instance : Append TreeError where
  append := .both

abbrev Path := Option String

def checkSubtype {α : Type} (v : α) (p : α → Prop) [Decidable (p v)] (err : ε) [Append ε]
    : Validate ε {x // p x} :=
  if h : p v then
    pure ⟨v, h⟩
  else
    .errors err

def report : TreeError → String
  | .field f s => s!"{f}: {s}"
  | .path p err =>
    match err with
    | .field f s => s!"--- {p} ---\n{f}: {s}"
    | .both e1 e2 => s!"--- {p} ---\n{report e1}\n{report e2}"
    | .path .. => unreachable!
  | .both e1 e2 => s!"{report e1}\n{report e2}"

def printReport : Validate TreeError α → IO Unit
  | .ok _ => pure ()
  | .errors errs => do IO.println <| report errs

def Validate.andThen : Validate ε α → (α → Validate ε β) → Validate ε β
  | .ok x, next => next x
  | .errors errs, _ => .errors errs

def reportError (path : Path) (f : Field) (msg : String) : Validate TreeError α :=
  match path with
  | none => .errors <| .field f msg
  | some path => .errors <| .path path <| .field f msg

def checkYearIsNat (year : String) : Validate TreeError Nat :=
  match year.trimAscii.toNat? with
  | none => reportError none "birth year" "Must be digits"
  | some year => pure year

def checkName (name : String) : Validate TreeError {n // n ≠ ""} :=
  if h : name ≠ "" then
    pure ⟨name, h⟩
  else
    reportError none "name" "Required"

def checkThat (cond : Bool) (path : Path) (field : Field) (msg : String)
    : Validate TreeError Unit :=
  if cond then pure () else reportError path field msg

def checkCompany (input : RawInput) : Validate TreeError LegacyCheckedInput :=
  checkThat (input.birthYear == "FIRM") "Company" "birth year" "FIRM if a company" *>
    .company <$> checkName input.name

def checkHumanBefore1970 (input : RawInput) : Validate TreeError LegacyCheckedInput :=
  (checkYearIsNat input.birthYear).andThen fun y =>
    .humanBefore1970 <$>
      checkSubtype y (fun y => y > 999 ∧ y < 1970)
        (.path "Human before 1970" <| .field "birth year" "less than 1970") <*>
      pure input.name

def checkHumanAfter1970 (input : RawInput) : Validate TreeError LegacyCheckedInput :=
  (checkYearIsNat input.birthYear).andThen fun y =>
    .humanAfter1970 <$>
      checkSubtype y (· ≥ 1970)
        (.path "Human after 1970" <| .field "birth year" "greater than 1970") <*>
      checkName input.name

def checkLegacyInput (input : RawInput) : Validate TreeError LegacyCheckedInput :=
  checkCompany input <|> checkHumanBefore1970 input <|> checkHumanAfter1970 input

#eval checkLegacyInput ⟨"Johnny's Troll Groomers", "FIRM"⟩
-- Hidden.Validate.ok (LegacyCheckedInput.company "Johnny's Troll Groomers")

#eval checkLegacyInput ⟨"Johnny", "1963"⟩
-- Hidden.Validate.ok (LegacyCheckedInput.humanBefore1970 1963 "Johnny")

#eval checkLegacyInput ⟨"", "1963"⟩
-- Hidden.Validate.ok (LegacyCheckedInput.humanBefore1970 1963 "")

#eval checkLegacyInput ⟨"", "1970"⟩ |> printReport
-- --- Company ---
-- birth year: FIRM if a company
-- name: Required
-- --- Human before 1970 ---
-- birth year: less than 1970
-- name: Required

end Hidden
