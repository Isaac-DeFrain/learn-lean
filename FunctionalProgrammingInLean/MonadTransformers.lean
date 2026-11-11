/- 6. Monad Transformers -/

-- 6.1 Combining IO and Reader

-- Reader monad is useful when there is some notion of "current configuration"

-- `doug` - `tree`-like command line app

-- 6.1.1 Implementation

-- `doug` passes a config downwards as it recursively traverses the directory structure

-- config:
-- `useASCII` - determines whether to use Unicode box-drawing chars or ASCII chars
-- `currentPrefix` - contains a string to prepend to each directory in output

-- see ./Doug.lean

structure Config where
  useASCII : Bool := false
  currentPrefix : String := ""

-- 6.1.2 Using a Custom Monad

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

-- 6.1.3 Adding a Read to any Monad

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

-- 6.1.4 Exercises

-- 6.1.4.1 Controlling the Display of DotFiles
-- Files whose names begin with a dot character ('.') typically represent files that should
-- usually be hidden, such as source-control metadata and configuration files. Modify `doug`
-- with an option to show or hide filenames that begin with a dot. This option should be
-- controlled with a `-a` command-line option.

-- see ./Doug.lean

-- 6.1.4.2 Starting Directory as Argument

-- see ./Doug.lean
