-- # 6. Monad Transformers

-- ## 6.1 Combining IO and Reader

-- Reader monad is useful when there is some notion of "current configuration"

-- `doug` - `tree`-like command line app

-- ### 6.1.1 Implementation

-- `doug` passes a config downwards as it recursively traverses the directory structure

-- config:
-- `useASCII` - determines whether to use Unicode box-drawing chars or ASCII chars
-- `currentPrefix` - contains a string to prepend to each directory in output

-- see ./Doug.lean

structure Config where
  useASCII : Bool := false
  currentPrefix : String := ""

-- ### 6.1.2 Using a Custom Monad

-- passing config around is verbose and error-prone, type system cannot catch errors
-- use reader monad instance instead

def ConfigIO' (α : Type) : Type := Config → IO α

-- ConfigIO is not universe polymorphic because IO is not universe polymorphic

-- This custom monad has a number of advantages over passing configs manually:
-- 1. It is easier to ensure that configs are passed down unchanged, except when changes
--    are desired
-- 2. The concern of passing the config onwards is more clearly separated from the concern
--    of printing directory contents
-- 3. As the program grows, there will be more and more intermediate layers that do nothing
--    with configs except propagate them, and these layers don't need to be rewritten as the
--    config logic changes

-- However, there are also some clear downsides:
-- 1. As the program evolves and the monad requires more features, each of the basic operators
--    such as `locally` and `currentConfig` will need to be updated
-- 2. Wrapping ordinary IO actions in `runIO` is noisy and distracts from the flow of the program
-- 3. Writing monad instances by hand is repetitive, and the technique for adding a reader effect
--    to another monad is a design pattern that requires documentation and communication overhead

-- moand transformers address all of these downsides
-- a monad transformer takes a monad as an arg and returns a new monad

-- monad transformers consist of:
-- 1. A definition of the transformer itself, which is typically a function from types to types
-- 2. A Monad instance that assumes the inner type is already a monad
-- 3. An operator to “lift” an action from the inner to the transformed monad, akin to `runIO`

-- ### 6.1.3 Adding a Read to any Monad

#print ReaderT
-- @[implicit_reducible] def ReaderT.{u, v} : Type u → (Type u → Type v) → Type u → Type (max u v) :=
-- fun ρ m α => ρ → m α

-- `ρ` is the environment that is accessible to the reader
-- `m` is the monad that is being transformed, such as IO
-- `α` is the type of values being returned by the monadic computation. Both `α` and `ρ` are
--     in the same universe because the operator that retrieves the environment in the monad
--     will have type `m ρ`.

abbrev ConfigIO (α : Type) : Type := ReaderT Config IO α

-- generic form of obtaining the environment out of the reader
def read [Monad m] : ReaderT ρ m ρ := pure

-- no every monad that provides a reader is built with ReaderT

#print MonadReader
-- class MonadReader.{u, v} (ρ : outParam (Type u)) (m : Type u → Type v) : Type v
-- number of parameters: 2
-- fields:
--   MonadReader.read : m ρ
-- constructor:
--   MonadReader.mk.{u, v} {ρ : outParam (Type u)} {m : Type u → Type v} (read : m ρ) : MonadReader ρ m

-- `ρ` is an output parameter because any given monad typically only provides a single type of
-- environment through a reader

-- same as monad instance for `ConfgIO`
instance [Monad m] : Monad (ReaderT ρ m) where
  pure x := fun _ => pure x
  bind action next := fun cfg => do next (← action cfg) cfg

-- when Lean encounters a mismatch in monad types, it automatically attempts to use a type
-- class called `MonadLift` to transform the actual monad into the expected one
-- similar to coercions

-- translates from the monad `m` to the monad `n`
#print MonadLift
-- class MonadLift.{u, v, w} (m : semiOutParam (Type u → Type v)) (n : Type u → Type w) : Type (max (max (u + 1) v) w)
-- number of parameters: 2
-- fields:
--   MonadLift.monadLift : {α : Type u} → m α → n α
-- constructor:
--   MonadLift.mk.{u, v, w} {m : semiOutParam (Type u → Type v)} {n : Type u → Type w}
--     (monadLift : {α : Type u} → m α → n α) : MonadLift m n

instance : MonadLift m (ReaderT ρ m) where
  monadLift action := fun _ => action

-- originally defined to override config
def locally (change : Config → Config) (action : ConfigIO α) : ConfigIO α :=
  action ∘ change

-- use instance of `MonadWithReader` instead

-- ### 6.1.4 Exercises

-- #### 6.1.4.1 Controlling the Display of DotFiles
-- Files whose names begin with a dot character ('.') typically represent files that should
-- usually be hidden, such as source-control metadata and configuration files. Modify `doug`
-- with an option to show or hide filenames that begin with a dot. This option should be
-- controlled with a `-a` command-line option.

-- see ./Doug.lean

-- #### 6.1.4.2 Starting Directory as Argument

-- see ./Doug.lean

-- ### 6.2 A Monad Construction Kit

-- each monad transformer consists of:
-- 1. a defintion or datatype `T` that takes a monad as an argument
-- 2. a monad instance for `T m` that relies on a monad instance for `m`
-- 3. a MonadLift instance that translates actions of type `m α` into actions of type `T m α`

-- also
-- 1. `LawfulMonad m` should imply `LawfulMonad (T m)`
-- 2. `monadLift (pure x : m α)` should be equivalent to `pure x : T m α`
-- 3. `monadLift (x >>= f : m α)` should be the same as `(monadLift x : m α) >>= fun y => monadLift (f y)`

-- many monad transformers also define type classes in the style of `MonadReader` that
-- describe the actual effects available in the monad

-- 6.2.1 Failure with `OptionT`

#print OptionT
-- @[implicit_reducible] def OptionT.{u, v} : (Type u → Type v) → Type u → Type v :=
-- fun m α => m (Option α)

structure UserInfo where
  name : String
  favBeetle : String

def getUserInput : OptionT IO String := do
  let input ← (← IO.getStdin).getLine
  let trimmed := input.trimAscii
  if trimmed.isEmpty then
    failure
  else
    pure trimmed.copy

def getUserInfo : OptionT IO UserInfo := do
  IO.println "What is your name?"
  let name ← getUserInput
  IO.println "What is your favorite beetle"
  let favBeetle ← getUserInput
  pure ⟨name, favBeetle⟩

def interact : IO Unit := do
  match ← getUserInfo with
  | none => IO.eprintln "Missing info"
  | some ⟨name, favBeetle⟩ =>
    IO.println s!"Hello {name}, whose favorite beetle is {favBeetle}"

-- #### 6.2.1.1 The Monad Instance

-- Lean selects the wrong monad instance so we need to provide `: m (Option _)`
instance [Monad m] : Monad (OptionT m) where
  pure x := (pure <| some x : m (Option _))
  bind action next := (do
    match ← action with
    | none => pure none
    | some x => next x : m (Option _))

-- to avoid this noise, we use `OptionT.mk` instead

instance [Monad m] : Monad (OptionT m) where
  pure x := .mk ∘ pure <| some x
  bind action next := .mk do
    match ← action with
    | none => pure none
    | some x => next x

-- check monad contract

instance [Monad m] [LawfulMonad m] : LawfulMonad (OptionT m) where
  bind_pure_comp f x := by
    simp [Bind.bind, Pure.pure, Functor.map, OptionT.mk]
    apply bind_congr
    intro a
    cases a <;> rfl
  bind_map f x := by
    simp [Bind.bind, Functor.map, OptionT.mk]
    apply bind_congr
    intro a
    cases a <;> rfl
  pure_bind x f := by
    simp [Bind.bind, Pure.pure, OptionT.mk]
  bind_assoc x f g := by
    simp [Bind.bind, OptionT.mk]
    apply bind_congr
    intro a
    cases a <;> simp
  seqLeft_eq x y := by
    simp [Functor.map, Seq.seq, OptionT.bind, OptionT.mk, OptionT.pure]
    apply bind_congr
    intro a
    cases a <;> simp [OptionT.bind, OptionT.mk]; rfl
  seqRight_eq x y := by
    simp [Functor.map, Seq.seq, OptionT.bind, OptionT.mk, OptionT.pure]
    apply bind_congr
    intro a
    cases a <;> simp
    refine (bind_pure (m := m) y.run).symm.trans ?_
    apply bind_congr
    intro b
    cases b <;> rfl
  map_const := rfl
  id_map x := by
    simp [Functor.map, OptionT.bind, OptionT.mk, OptionT.pure]
    apply Eq.symm
    refine (bind_pure (m := m) x.run).symm.trans ?_
    apply bind_congr
    intro b
    cases b <;> rfl
  pure_seq g x := by
    simp [Functor.map, Seq.seq, Pure.pure, OptionT.bind, OptionT.mk, OptionT.pure]

-- #### 6.2.1.2 An `Alternative` Instance

-- convenient to use `OptionT` through the `Alternative` type class

instance [Monad m] : Alternative (OptionT m) where
  failure := .mk <| pure none
  orElse x y := .mk do
    match ← x with
    | some res => pure (some res)
    | none => y ()

-- #### 6.2.1.3 Lifting

-- lifting an action from monad `m` to `OptionT m` requires wrapping the result in `some`

instance [Monad m] : MonadLift m (OptionT m) where
  monadLift action := do
    pure ∘ some <| ← action

-- 6.2.2 Exceptions

#print ExceptT
-- @[implicit_reducible] def ExceptT.{u, v} : Type u → (Type u → Type v) → Type u → Type v :=
-- fun ε m α => m (Except ε α)

-- helpers to guide the type checker to the correct monad instances

#print ExceptT.mk
-- def ExceptT.mk.{u, v} : {ε : Type u} → {m : Type u → Type v} → {α : Type u} → m (Except ε α) → ExceptT ε m α :=
-- fun {ε} {m} {α} x => x

#print ExceptT.run
-- def ExceptT.run.{u, v} : {ε : Type u} → {m : Type u → Type v} → {α : Type u} → ExceptT ε m α → m (Except ε α) :=
-- fun {ε} {m} {α} x => x

-- almost identical to `OptionT` except it propogates a specific error
instance [Monad m] : Monad (ExceptT ε m) where
  pure := .mk ∘ pure ∘ .ok
  bind result next := .mk do
    match ← result with
    | .error e => pure <| .error e
    | .ok x => next x

-- unlike `Option`, `Except` is not typically used as a data structure, but rather as a control
-- structure with its `Monad` instance so it is reasonsable to lift `Except ε` actions into
-- `ExceptT ε m` as well as `m` actions

-- lift exception into `ExceptT ε m`, just wrap in `m`'s `pure`
instance [i : Monad m] : MonadLift (Except ε) (ExceptT ε m) where
  monadLift := .mk ∘ i.pure

-- lift `m` into `ExceptT ε m`, do not have exceptions, just map over with `Except.ok`
instance [Monad m] : MonadLift m (ExceptT ε m) where
  monadLift action := .mk <| .ok <$> action

-- #### 6.2.2.1 Type Classes for Exceptions

-- exception handling consists of two operations:
-- 1. ability to throw an exception
-- 2. ability to recover from an exception

#print MonadExcept
-- class MonadExcept.{u, v, w} (ε : outParam (Type u)) (m : Type v → Type w) : Type (max (max u (v + 1)) w)
-- number of parameters: 2
-- fields:
--   MonadExcept.throw : {α : Type v} → ε → m α
--   MonadExcept.tryCatch : {α : Type v} → m α → (ε → m α) → m α
-- constructor:
--   MonadExcept.mk.{u, v, w} {ε : outParam (Type u)} {m : Type v → Type w} (throw : {α : Type v} → ε → m α)
--     (tryCatch : {α : Type v} → m α → (ε → m α) → m α) : MonadExcept ε m

-- unlike `ExceptT`, `MonadExcept` imposes no constraints on the universe levels of `ε` and `α`
-- beacuse exceptions are never used inside `m`

-- example of program that uses `MonadExcept`: division service
-- frontend: supplies user interface based on strings, handles errors
-- backend: does the division, handles errors

inductive Err where
  | divByZero
  | notANumber : String → Err

-- backend checks for zero and divides if it can
def divBackend [Monad m] [MonadExcept Err m] (n k : Int) : m Int :=
  if k == 0 then
    throw .divByZero
  else pure (n / k)

-- frontend helper
def asNumber [Monad m] [MonadExcept Err m] (s : String) : m Int :=
  match s.toInt? with
  | none => throw <| .notANumber s
  | some i => pure i

def divFrontend [Monad m] [MonadExcept Err m] (n k : String) : m String :=
  try
    pure <| toString <| ← divBackend (← asNumber n) (← asNumber k)
  catch
      | .divByZero => pure "Division by zero!"
      | .notANumber s => pure s!"Not a number: \"{s}\""

-- useful `MonadExcept` instances for types that may not seem like exceptions at first glance

-- e.g. instance of `MonadExcept Unit Option`
def throwIfEmpty [ToString α] (xs : List α) : Option String :=
  try
    xs[0]?.map toString
  catch
    | () => some s!"Empty"

#eval throwIfEmpty ([] : List Nat)
-- some "Empty"

#eval throwIfEmpty [42]
-- some "42"

-- ### 6.2.3 State

#print StateT
-- @[implicit_reducible] def StateT.{u, v} : Type u → (Type u → Type v) → Type u → Type (max u v) :=
-- fun σ m α => σ → m (α × σ)

instance [Monad m] : Monad (StateT σ m) where
  pure x := fun s => pure (x, s)
  bind x f := fun s => do
    let (y, s') ← x s
    f y s'

#print MonadState
-- class MonadState.{u, v} (σ : outParam (Type u)) (m : Type u → Type v) : Type (max (u + 1) v)
-- number of parameters: 2
-- fields:
--   MonadState.get : m σ
--   MonadState.set : σ → m PUnit
--   MonadState.modifyGet : {α : Type u} → (σ → α × σ) → m α
-- constructor:
--   MonadState.mk.{u, v} {σ : outParam (Type u)} {m : Type u → Type v} (get : m σ) (set : σ → m PUnit)
--     (modifyGet : {α : Type u} → (σ → α × σ) → m α) : MonadState σ m

-- example program counts the number of diacritic-free English vowels and consonants
-- in a string of letters

structure LetterCounts where
  vowels : Nat
  consonants : Nat
deriving Repr

inductive LetterCounts.Err where
  | notALetter : Char → Err
deriving Repr

def vowels :=
  let lowerVowels := "aeiouy"
  lowerVowels ++ lowerVowels.map (·.toUpper)

def consonants :=
  let lowerConsonants := "bcdfghjklmnpqrstvwxz"
  lowerConsonants ++ lowerConsonants.map (·.toUpper)

-- easy to confuse which state to `set`
-- instead of `get`/`set`, use `modify`
def countLetters (str : String) : StateT LetterCounts (Except LetterCounts.Err) Unit :=
  let rec loop (chars : List Char) := do
    match chars with
    | [] => pure ()
    | c :: cs =>
      if c.isAlpha then
        if vowels.contains c then
          modify fun st => {st with vowels := st.vowels + 1}
        else if consonants.contains c then
          modify fun st => {st with consonants := st.consonants + 1}
        else  -- modified or non-English letter
          pure ()
      else throw <| .notALetter c
      loop cs
  loop str.toList

#print modify
-- def modify.{u, v} : {σ : Type u} → {m : Type u → Type v} → [MonadState σ m] → (σ → σ) → m PUnit :=
-- fun {σ} {m} [MonadState σ m] f => modifyGet fun s => (PUnit.unit, f s)

#print MonadState
-- class MonadState.{u, v} (σ : outParam (Type u)) (m : Type u → Type v) : Type (max (u + 1) v)
-- number of parameters: 2
-- fields:
--   MonadState.get : m σ
--   MonadState.set : σ → m PUnit
--   MonadState.modifyGet : {α : Type u} → (σ → α × σ) → m α
-- constructor:
--   MonadState.mk.{u, v} {σ : outParam (Type u)} {m : Type u → Type v} (get : m σ) (set : σ → m PUnit)
--     (modifyGet : {α : Type u} → (σ → α × σ) → m α) : MonadState σ m

-- ### 6.2.4 `Of` Classes and `The` Functions

-- for more complex monad with multiple types of state or exceptions, the output parameters of
-- `StateT`, `ReaderT`, and `ExceptT` make it impossible to target multiple types or state or
-- exceptions in the same `do`-block

-- `...` with semi-output parameter type: `...Of`

#print MonadStateOf
-- class MonadStateOf.{u, v} (σ : semiOutParam (Type u)) (m : Type u → Type v) : Type (max (u + 1) v)
-- number of parameters: 2
-- fields:
--   MonadStateOf.get : m σ
--   MonadStateOf.set : σ → m PUnit
--   MonadStateOf.modifyGet : {α : Type u} → (σ → α × σ) → m α
-- constructor:
--   MonadStateOf.mk.{u, v} {σ : semiOutParam (Type u)} {m : Type u → Type v} (get : m σ) (set : σ → m PUnit)
--     (modifyGet : {α : Type u} → (σ → α × σ) → m α) : MonadStateOf σ m

#print MonadReaderOf
-- class MonadReaderOf.{u, v} (ρ : semiOutParam (Type u)) (m : Type u → Type v) : Type v
-- number of parameters: 2
-- fields:
--   MonadReaderOf.read : m ρ
-- constructor:
--   MonadReaderOf.mk.{u, v} {ρ : semiOutParam (Type u)} {m : Type u → Type v} (read : m ρ) : MonadReaderOf ρ m

#print MonadExceptOf
-- class MonadExceptOf.{u, v, w} (ε : semiOutParam (Type u)) (m : Type v → Type w) : Type (max (max u (v + 1)) w)
-- number of parameters: 2
-- fields:
--   MonadExceptOf.throw : {α : Type v} → ε → m α
--   MonadExceptOf.tryCatch : {α : Type v} → m α → (ε → m α) → m α
-- constructor:
--   MonadExceptOf.mk.{u, v, w} {ε : semiOutParam (Type u)} {m : Type v → Type w} (throw : {α : Type v} → ε → m α)
--     (tryCatch : {α : Type v} → m α → (ε → m α) → m α) : MonadExceptOf ε m

-- `semiOutParam` not needed in order to start the process of instance search, but unlike an
-- `outParam`, it is not ignored during instance search

-- if an `outParam` is known prior to instance search, Lean simply checks that the result of
-- the search is the same as what is known

-- is a `semiOutParam` is known prior to instance search, Lean can use it to narrow down the
-- search, just like an input parameter

-- versions of type class methods that take the extra info as _explicit_

#print getThe
-- @[reducible] def getThe.{u, v} : (σ : Type u) → {m : Type u → Type v} → [MonadStateOf σ m] → m σ :=
-- fun σ {m} [MonadStateOf σ m] => MonadStateOf.get

#print modifyThe
-- @[reducible] def modifyThe.{u, v} : (σ : Type u) → {m : Type u → Type v} → [MonadStateOf σ m] → (σ → σ) → m PUnit :=
-- fun σ {m} [MonadStateOf σ m] f => MonadStateOf.modifyGet fun s => (PUnit.unit, f s)

-- implementing the `Of` version of the type class yields versions of both

-- generally a good idea to implement the `Of` versions and write programs using the non-`Of`
-- versions, until it becomes necessary to use the `Of` version

-- ### 6.2.5 Transformers and `Id`

example : StateT σ Id α = (σ → (α × σ)) := rfl

-- ### 6.2.6 Exercises

-- #### 6.2.6.1 Monad Contract
-- Check that the rules of the monad transformer contract are satisfied for each monad
-- transformer in this section.

-- ExceptT
instance [Monad m] [LawfulMonad m] : LawfulMonad (ExceptT ε m) where
  bind_pure_comp f x := by
    simp [Bind.bind, Pure.pure, Functor.map, ExceptT.mk]
    apply bind_congr
    intro a
    cases a <;> rfl
  bind_map f x := by
    simp [Bind.bind, Functor.map, ExceptT.mk]
    apply bind_congr
    intro a
    cases a <;> rfl
  pure_bind x f := by
    simp [Bind.bind, Pure.pure, ExceptT.mk]
  bind_assoc x f g := by
    simp [Bind.bind, ExceptT.mk]
    apply bind_congr
    intro a
    cases a <;> simp
  seqLeft_eq x y := by
    simp [Functor.map, Seq.seq, ExceptT.bind, ExceptT.mk, ExceptT.map]
    apply bind_congr
    intro a
    cases a <;> simp [ExceptT.bind, ExceptT.mk, ExceptT.bindCont]; rfl
  seqRight_eq x y := by
    simp [Functor.map, Seq.seq, ExceptT.bind, ExceptT.mk, ExceptT.map]
    apply bind_congr
    intro a
    cases a <;> simp [ExceptT.bindCont];
    refine (bind_pure (m := m) y.run).symm.trans ?_
    apply bind_congr
    intro b
    cases b <;> rfl
  map_const := rfl
  id_map x := by
    simp [Functor.map, ExceptT.map, ExceptT.mk]
    apply Eq.symm
    refine (bind_pure (m := m) x.run).symm.trans ?_
    apply bind_congr
    intro b
    cases b <;> rfl
  pure_seq g x := by
    simp [Functor.map, Seq.seq, Pure.pure, ExceptT.bind, ExceptT.mk, ExceptT.map, ExceptT.bindCont]

-- StateT
instance [Monad m] [LawfulMonad m] : LawfulMonad (StateT σ m) where
  bind_pure_comp f x := by
    simp [Bind.bind, Pure.pure]
    funext s
    simp [StateT.map, Functor.map]
  bind_map f x := by
    simp [Bind.bind, Functor.map]
    funext s
    simp [Seq.seq, StateT.map]
    apply bind_congr
    intro a
    simp [StateT.map]
  pure_bind x f := by
    simp [Bind.bind, Pure.pure]
  bind_assoc x f g := by
    simp [Bind.bind]
  seqLeft_eq x y := by
    simp [Functor.map, Seq.seq, SeqLeft.seqLeft]
    funext s
    simp [StateT.bind, StateT.map, StateT.pure]
  seqRight_eq x y := by
    simp [Functor.map, Seq.seq, SeqRight.seqRight]
    funext s
    simp [StateT.bind, StateT.map]
  map_const := rfl
  id_map x := by
    simp [Functor.map]
    funext s
    simp [StateT.map]
  pure_seq g x := by
    simp [Functor.map, Seq.seq, Pure.pure]
    funext s
    simp [StateT.bind]

-- #### 6.2.6.2 Logging Transformer
-- Define a monad transformer version of `WithLog`. Also define the corresponding type class
-- `MonadWithLog`, and write a program that combines logging and exceptions.

structure WithLog (log : Type u) (α : Type v) where
  log : List log
  val : α

instance : Monad (WithLog log) where
  pure x := { log := [], val := x }
  bind result next :=
    let { log := thisOut, val } := result
    let { log := nextOut, val } := next val
    { log := thisOut ++ nextOut, val }

abbrev WithLogT (log : Type) (m : Type u → Type v) (α : Type u) : Type v :=
  m (WithLog log α)

def WithLogT.mk (x : m (WithLog log α)) : WithLogT log m α := x

instance [Monad m] : Monad (WithLogT log m) where
  pure x := WithLogT.mk ∘ pure <| pure x
  bind result next := WithLogT.mk do
    let { log := thisOut, val } ← result
    let { log := nextOut, val } ← next val
    pure { log := thisOut ++ nextOut, val }

class MonadWithLog (log : outParam Type) (m : Type u → Type v) where
  save : log → m PUnit

instance [Monad m] : MonadWithLog log (WithLogT log m) where
  save entry := WithLogT.mk <| pure { log := [entry], val := ⟨⟩ }

instance [Monad m] : MonadLift m (WithLogT log m) where
  monadLift x := WithLogT.mk do pure { log := [], val := ← x }

instance [MonadLift m n] [MonadWithLog log m] : MonadWithLog log n where
  save entry := MonadLift.monadLift (MonadWithLog.save entry : m _)

-- #### 6.2.6.3 Counting Files
-- Modify `doug`'s monad with `StateT` such that it counts the number of directories and files
-- seen. At the end of execution, it should display a report like:
--   Viewed 38 files in 5 directories.

-- see /Doug.lean

-- ## 6.3 Ordering Monad Transformers

-- different layerings of transformers result in different monads

namespace Reorder

open LetterCounts renaming Err → LCErr

-- same as previous version, except using type classes `MonadState` and `MonadExcept`
def countLetters [Monad m] [MonadState LetterCounts m] [MonadExcept LCErr m]
    (str : String) : m Unit :=
  let rec loop (chars : List Char) := do
    match chars with
    | [] => pure ()
    | c :: cs =>
      if c.isAlpha then
        if vowels.contains c then
          modify fun st => {st with vowels := st.vowels + 1}
        else if consonants.contains c then
          modify fun st => {st with consonants := st.consonants + 1}
        else -- modified or non-English letter
          pure ()
      else throw <| .notALetter c
      loop cs
  loop str.toList

-- state and exception monad transformers can be combined in two different orders
abbrev M1 := StateT LetterCounts (ExceptT LCErr Id)
abbrev M2 := ExceptT LCErr (StateT LetterCounts Id)

-- outputs are subtlely different

#eval (countLetters (m := M1) "hello" ⟨0, 0⟩ : Except _ _)
-- Except.ok ((), { vowels := 2, consonants := 3 })

#eval (countLetters (m := M2) "hello" ⟨0, 0⟩ : Except _ _ × _)
-- (Except.ok (), { vowels := 2, consonants := 3 })

-- only one returns a count when an exception is thrown

#eval countLetters (m := M1) "hello!" ⟨0, 0⟩
-- Except.error (LetterCounts.Err.notALetter '!')

#eval countLetters (m := M2) "hello!" ⟨0, 0⟩
-- (Except.error (LetterCounts.Err.notALetter '!'), { vowels := 2, consonants := 3 })

-- if exceptions are handled, things can get confusing

def countLettersWithFallback [Monad m] [MonadState LetterCounts m] [MonadExcept LCErr m]
    (str : String) : m Unit :=
  try
    countLetters str
  catch _ =>
    countLetters "Fallback"

-- in M1: throwing an exception “rolls back” the state to where the exception was caught
-- in M2: modifications to the state persist across the throwing and catching of exceptions

#eval countLettersWithFallback (m := M1) "hello!" ⟨0, 0⟩
-- Except.ok ((), { vowels := 2, consonants := 6 })

#eval countLettersWithFallback (m := M2) "hello!" ⟨0, 0⟩
-- (Except.ok (), { vowels := 4, consonants := 9 })

-- M1 α returns either an error or updated counts, no final state if exception thrown
example : M1 α = (LetterCounts → Except LCErr (α × LetterCounts)) := rfl

-- M2 α returns updated count paired with either an error or α, exceptions accompanied by state
example : M2 α = (LetterCounts → (Except LCErr α × LetterCounts)) := rfl

end Reorder

-- ### 6.3.1 Commuting Monads

-- monad transformers _commute_ if reordering does not change the meaning of the program
-- `StateT` and `ExceptT` do not commute

-- `StateT` commutes with itself
example : StateT σ (StateT σ' Id) α = (σ → σ' → ((α × σ) × σ')) := rfl
example : StateT σ' (StateT σ Id) α = (σ' → σ → ((α × σ') × σ)) := rfl

-- ### 6.3.2 Exercises

-- 1. Check that `ReaderT` and `StateT` commute by expanding their definitions and reasoning
-- about the resulting types.

example : ReaderT ρ (StateT σ Id) α = (ρ → σ → α × σ) := rfl
example : StateT σ (ReaderT ρ Id) α = (σ → ρ → α × σ) := rfl

-- `ReaderT` and `StateT` commute because inputs and outputs are the same

-- 2. Do `ReaderT` and `ExceptT` commute? Check your answer by expanding their definitions
-- and reasoning about the resulting types.

example : ReaderT ρ (ExceptT ε Id) α = (ρ → Except ε α) := rfl
example : ExceptT ε (ReaderT ρ Id) α = (ρ → Except ε α) := rfl

-- `ReaderT` and `ExceptT` commute because inputs and outputs are the same

-- 3. Construct a monad transformer `ManyT` based on the definition of `Many`, with a suitable
-- `Alternative` instance. Check that it satisfies the `Monad` contract.

inductive Many (α : Type u) where
  | none : Many α
  | more : α → (Unit → Many α) → Many α
deriving Nonempty

def Many.one (x : α) : Many α :=
  .more x fun () => .none

def Many.union : Many α → Many α → Many α
  | .none, xs | xs, .none => xs
  | .more x xs, ys => .more x fun () => (xs ()).union ys

def Many.bind {α β} : Many α → (α → Many β) → Many β
  | .none, _ => .none
  | .more x xs, f => (f x).union <| bind (xs ()) f

def Many.fromList : List α → Many α
  | [] => .none
  | x :: xs => .more x fun () => fromList xs

def Many.takeAll : Many α → List α
  | .none => []
  | .more x xs => x :: (xs ()).takeAll

def List.print [ToString α] : List α → IO Unit
  | [] => pure ()
  | x :: xs => do
    IO.println x
    xs.print

-- helper theorems --

theorem Many.union_none (m : Many α) : m.union .none = m := by
  cases m <;> rfl

theorem Many.more_union (x : α) (xs : Many α)
    : (Many.more x fun () => Many.none).union xs = Many.more x fun () => xs := by
  cases xs <;> simp [Many.union]

theorem Many.union_assoc (a b c : Many α) :
    (a.union b).union c = a.union (b.union c) := by
  induction a with
  | none => rfl
  | more x xs ih =>
    cases b <;> cases c <;> simp [Many.union, ih]

theorem Many.bind_union (a b : Many α) (f : α → Many β) :
    (a.union b).bind f = (a.bind f).union (b.bind f) := by
  induction a with
  | none => rfl
  | more x xs ih =>
    cases b with
    | none => exact (Many.union_none _).symm
    | more y ys => simp [Many.union, Many.bind, ih, Many.union_assoc]

----

instance : Monad Many where
  pure := .one
  bind := .bind

def Many.orElse : Many α → (Unit → Many α) → Many α
  | .none, xs => xs ()
  | .more x xs, ys => .more x fun () => (xs ()).orElse ys

instance : Alternative Many where
  failure := .none
  orElse := .orElse

abbrev ManyT (m : Type u → Type v) (α : Type u) : Type v := m (Many α)

def ManyT.mk (x : m (Many α)) : ManyT m α := x

def Many.bindM [Monad m] (f : α → m (Many β)) : Many α → m (Many β)
  | .none => pure .none
  | .more x xs => do
    let fx ← f x
    let fxs ← (xs ()).bindM f
    pure <| fx.union fxs

def ManyT.bind [Monad m] (x : ManyT m α) (f : α → ManyT m β) : ManyT m β :=
  .mk do (← x).bindM f

instance [Monad m] : Monad (ManyT m) where
  pure := .mk ∘ pure ∘ .one
  bind := .bind

instance [Monad m] : MonadLift m (ManyT m) where
  monadLift x := .mk do pure <| .one (← x)

def ManyT.choose [Monad m] (xs : List α) : ManyT m α :=
  .mk ∘ pure <| .fromList xs

instance : LawfulMonad Many :=
  .mk' _
  (id_map := fun x => by
    simp [Functor.map]
    induction x with
    | none => rfl
    | more _ _ ih =>
      simp [Many.bind, Many.one, Many.more_union, ih])
  (pure_bind := fun x f => by
    show (Many.one x).bind f = f x
    simp [Many.one, Many.bind, Many.union_none])
  (bind_assoc := fun x f g => by
    show (x.bind f).bind g = x.bind fun a => (f a).bind g
    induction x with
    | none => rfl
    | more _ _ ih => simp [Many.bind, Many.bind_union, ih])

-- `ManyT m` does not satify the monad contract even for `LawfulMonad m`, `m` would have to be comutative

-- counterexample invalidate bind associativity
def tag (s : String) (a : Nat) : ManyT (StateT (List String) Id) Nat :=
  .mk do
    modify (·.concat s!"{s}{a}")
    pure <| .one a

/-- info: ["f1", "f2", "g1", "g2"] -/
#guard_msgs in
#eval StateT.run (((ManyT.choose [1, 2]).bind (tag "f")).bind (tag "g")) [] |> (·.2)

/-- info: ["f1", "g1", "f2", "g2"] -/
#guard_msgs in
#eval StateT.run ((ManyT.choose [1, 2]).bind fun a => (tag "f" a).bind (tag "g")) [] |> (·.2)

-- helper
theorem Many.bindM_pure_one [Monad m] [LawfulMonad m] (r : Many α) :
    r.bindM (fun a => (pure (Many.one a) : m (Many α))) = pure r := by
  induction r with
  | none => rfl
  | more a as ih =>
    simp only [Many.bindM, pure_bind, ih]
    simp [Many.one, Many.more_union]

theorem ManyT.pure_bind [Monad m] [LawfulMonad m] (x : α) (f : α → ManyT m β) : pure x >>= f = f x := by
    show (pure (Many.one x) >>= fun r => r.bindM f) = f x
    simp [Many.one, Many.bindM, Many.union_none]

theorem ManyT.bind_pure [Monad m] [LawfulMonad m] (x : ManyT m α) : x >>= pure = x := by
  show x.bind (fun a => ManyT.mk (pure (Many.one a))) = x
  simp [ManyT.bind, ManyT.mk, Many.bindM_pure_one]

-- 4. Does `ManyT` commute with `StateT`? If so, check your answer by expanding definitions and
-- reasoning about the resulting types. If not, write a program in `ManyT (StateT σ Id)` and
-- a program in `StateT σ (ManyT Id)`. Each program should be one that makes more sense for
-- the given ordering of monad transformers.

example : ManyT (StateT σ Id) α = (σ → Many α × σ) := rfl   -- only preserves a single state for all `Many` elements
example : StateT σ (ManyT Id) α = (σ → Many (α × σ)) := rfl -- preserves a state for each `Many` element

-- `ManyT` and `StateT` do not commute

-- `ManyT (StateT σ Id) α` program
def distinctSums (xs : List Nat) : ManyT (StateT (List Nat) Id) Nat := do
  let x ← .choose xs
  let y ← .choose xs
  let sums ← get
  let sum := x + y
  if sums.contains sum then
    .mk <| pure .none
  else
    modify (sum :: ·)
    pure sum

/--
info:
2
4
6
8
10
12
14
16
18
-/
#guard_msgs in
#eval ((distinctSums [1, 3, 5, 7, 9]).run' []).takeAll.print

-- `StateT σ (ManyT Id) α` program
example : ManyT Id = Many := rfl
def evenAddsTo (goal : Nat) : List Nat → StateT (List Nat) Many (List Nat)
  | [] => do
    let list ← get
    guard (goal == 0 && list.length > 0 && list.length % 2 == 0)
    pure list
  | x :: xs =>
    if x > goal then
      evenAddsTo goal xs
    else
      evenAddsTo goal xs <|> do
        modify (·.concat x)
        evenAddsTo (goal - x) xs

/--
info:
[7, 8]
[6, 9]
[5, 10]
[2, 3, 4, 6]
[1, 3, 5, 6]
[1, 3, 4, 7]
[1, 2, 5, 7]
[1, 2, 4, 8]
[1, 2, 3, 9]
-/
#guard_msgs in
#eval ((evenAddsTo 15 [1, 2, 3, 4, 5, 6, 7, 8, 9, 10]).run' []).takeAll.print

-- ## 6.4 More `do` Features

-- ### 6.4.1 Single-Branched `if`

-- common pattern is to carry out a side effect only if some condition is met

def countLetters' (str : String) : StateT LetterCounts (Except LetterCounts.Err) Unit :=
  let rec loop (chars : List Char) := do
    match chars with
    | [] => pure ()
    | c :: cs =>
      if c.isAlpha then
        if vowels.contains c then
          modify fun st => {st with vowels := st.vowels + 1}
        else if consonants.contains c then
          modify fun st => {st with consonants := st.consonants + 1}
      else throw <| .notALetter c
      loop cs
  loop str.toList

example : countLetters = countLetters' := by
  funext s
  show countLetters.loop s.toList = countLetters'.loop s.toList
  induction s.toList with
  | nil => rfl
  | cons _ _ ih =>
    simp only [countLetters.loop, countLetters'.loop, ih]

def count [Monad m] [MonadState Nat m] (p : α → m Bool) (l : List α) : m Unit := do
  if let x :: xs := l then
    if ← p x then
      modify (· + 1)
    count p xs

-- `if not E then STMT ...` can be written `unless E do STMT ...`

def countNot [Monad m] [MonadState Nat m] (p : α → m Bool) (l : List α) : m Unit := do
  if let x :: xs := l then
    unless ← p x do
      modify (· + 1)
    count p xs

-- ### 6.4.2 Early Return

-- List.find?
def find? (p : α → Bool) : List α → Option α
  | [] => failure
  | x :: xs => do
    if p x then return x
    find? p xs

-- under the hood, early return uses the `ExceptT` monad transformer

def runCatch [Monad m] (action : ExceptT α m α) : m α := do
  match ← action with
  | .ok x | .error x => pure x

-- find? is equivalent to this
def find?' (p : α → Bool) : List α → Option α
  | [] => failure
  | x :: xs =>
    runCatch do
      if p x then throw x
      monadLift <| find? p xs

-- ### 6.4.2 Loops

-- #### 6.4.2.1 Looping with `ForM`

-- type class for looping over a container type
#print ForM
-- class ForM.{u, v, w₁, w₂} (m : Type u → Type v) (γ : Type w₁) (α : outParam (Type w₂)) : Type (max (max v w₁) w₂)
-- number of parameters: 3
-- fields:
--   ForM.forM : γ → (α → m PUnit) → m PUnit
-- constructor:
--   ForM.mk.{u, v, w₁, w₂} {m : Type u → Type v} {γ : Type w₁} {α : outParam (Type w₂)}
--     (forM : γ → (α → m PUnit) → m PUnit) : ForM m γ α

#print List.forM
-- protected def List.forM.{u, v, w} : {m : Type u → Type v} →
--   [Monad m] → {α : Type w} → List α → (α → m PUnit) → m PUnit :=
-- fun {m} [Monad m] {α} as f => List.brecOn as (List.forM._f f)

instance [Monad m] : ForM m (List α) α where
  forM := List.forM

def Many.forM [Monad m] : Many α → (α → m PUnit) → m PUnit
  | .none, _ => pure ()
  | .more x xs, action => do
    action x
    forM (xs ()) action

instance [Monad m] : ForM m (Many α) α where
  forM := Many.forM

-- `ForM` supports non-polymorphic types

structure AllLessThan where
  num : Nat

def AllLessThan.forM [Monad m] (coll : AllLessThan) (action : Nat → m Unit) : m Unit :=
  let rec countdown : Nat → m Unit
    | 0 => pure ()
    | n + 1 => do
      action n
      countdown n
  countdown coll.num

instance [Monad m] : ForM m AllLessThan Nat where
  forM := AllLessThan.forM

/-- info: 43210 -/
#guard_msgs in
#eval forM { num := 5 : AllLessThan } IO.print

-- example of `ForM` instance that works only in a particular monad

structure LinesOf where
  stream : IO.FS.Stream

partial def LinesOf.forM (readFrom : LinesOf) (action : String → IO Unit) : IO Unit := do
  let line ← readFrom.stream.getLine
  if line.isEmpty then return ()
  action line
  forM readFrom action

instance : ForM IO LinesOf String where
  forM := LinesOf.forM

-- #### 6.4.3.2 Stopping Iteration

def OptionT.exec [Applicative m] (action : OptionT m α) : m Unit :=
  action *> pure ()

-- failure in the `OptionT` instance of `Alternative` can be used to terminate looping early
def countToThree (n : Nat) : IO Unit :=
  let nums : AllLessThan := ⟨n + 1⟩
  OptionT.exec <| forM nums fun i =>
    if i < 3 then failure else IO.print i

/-- info: 76543 -/
#guard_msgs in
#eval countToThree 7

-- easier to read

instance [Monad m] : ForIn m AllLessThan Nat where
  forIn := ForM.forIn

def countToThree' (n : Nat) : IO Unit :=
  let nums : AllLessThan := ⟨n + 1⟩
  for i in nums do
    if i < 3 then break
    IO.print i

/-- info: 76543 -/
#guard_msgs in
#eval countToThree' 7

-- early return in for loops

def find?'' (p : α → Bool) (xs : List α) : Option α := do
  for x in xs do
    if p x then return x
  failure

-- continue in for loops

def find?''' (p : α → Bool) (xs : List α) : Option α := do
  for x in xs do
    if not <| p x then continue
    return x
  failure

-- ranges for iteration:
-- represented by a collection of types with a naming convention that describes their bounds
-- each type's name begins with `R`, and the next two letters determine the lower and upper
-- bounds, respectively:
-- - `o` represents an open bound, where the bound value is not included
-- - `c` represents a closed bound, where the bound value is included
-- - `i` represents an infinite bound that does not restrict its range

-- left-open, right-closed sequence
example : Std.Roc Nat := 2<...=5

-- left-infinite, right-open sequence
example : Std.Rio Nat := *...5

-- left-infinite, right-infinite sequence
example : Std.Rii Nat := *...*

/-- info: 234 -/
#guard_msgs in
#eval do for i in 2...5 do
  IO.print i

/-- info: 01234 -/
#guard_msgs in
#eval do for i in *...=4 do
  IO.print i

/-- info: abc -/
#guard_msgs in
#eval do for i in 'a'...'d' do
  IO.print i

-- for loops support iterating over multiple collections in parallel

/-- info: (a, 0)(b, 1)(c, 2)(d, 3) -/
#guard_msgs in
#eval do for c in 'a'...'e', i in 0...=(42 : Nat) do
  IO.print (c, i)

/-- info:
xs[0] = 1
xs[1] = 2
xs[2] = 3
-/
#guard_msgs in
#eval let xs := #[1, 2, 3]
  for h : i in 0...xs.size do
    IO.println s!"xs[{i}] = {xs[i]}"

-- the evidence `h : i in 0...xs.size` is required to prove safe access `xs[i]`
