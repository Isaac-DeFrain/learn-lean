/- 4. Monads -/

import FunctionalProgrammingInLean.OverloadingAndTypeClasses

-- 4.1 One API, Many Applications

-- 4.1.1 Checking for `none`: DRY

def first (xs : List α) : Option α := xs[0]?

def firstThird (xs : List α) : Option (α × α) :=
  match xs[0]? with
  | none => none
  | some first =>
    match xs[2]? with
    | none => none
    | some third => some (first, third)

def Option.andThen (opt : Option α) (next : α → Option β) : Option β :=
  match opt with
  | none => none
  | some x => next x

def firstThird' (xs : List α) : Option (α × α) :=
  .andThen xs[0]? fun first =>
  .andThen xs[2]? fun third =>
  (first, third)

-- 4.1.1.1 Infix Operators

infixl:55 " ~~> " => Option.andThen

def firstThird'' (xs : List α) : Option (α × α) :=
  xs[0]? ~~> fun first =>
  xs[2]? ~~> fun third =>
  (first, third)

-- 4.1.2 Propogating Error Messages

namespace Hidden

inductive Except (ε α : Type) where
  | error : ε → Except ε α
  | ok : α → Except ε α
deriving BEq, Hashable, Repr

end Hidden

#check Except
-- Except.{u, v} (ε : Type u) (α : Type v) : Type (max u v)

-- `andThen` definition for `Except ε α`

-- 4.1.3 Logging

structure WithLog (logged α : Type) where
  log : List logged
  val : α

def WithLog.save (data : α) : WithLog α Unit :=
  { log := [data], val := () }

-- `andThen` definition for `WithLog α β`

-- 4.1.4 Numbering Tree Nodes

-- represents a step of stateful computation
def State (σ : Type u) (α : Type v) : Type (max u v) :=
  σ → σ × α

def State.ok (x : α) : State σ α := fun s => (s, x)

-- when working with a mutable variable, two fundamental operations:
-- - reading the value
-- - replacing the value with a new one

def State.get : State σ σ := fun s => (s, s)

def State.set (s : σ) : State σ Unit := fun _ => (s, ())

def State.andThen (first : State σ α) (next : α → State σ β) : State σ β :=
  fun s =>
    let (s', x) := first s
    next x s'

infixl:55 " ~~> " => State.andThen

def numberTree (t : BinTree α) : BinTree (Nat × α) :=
  let rec helper : BinTree α → State Nat (BinTree (Nat × α))
    | .leaf => .ok .leaf
    | .branch l x r =>
      helper l ~~> fun numberedLeft =>
      .get ~~> fun n =>
      .set (n + 1) ~~> fun () =>
      helper r ~~> fun numberedRight =>
      .ok (.branch numberedLeft (n, x) numberedRight)
  (helper t 0).snd

def bt : BinTree String :=
  .branch (.branch .leaf "a" .leaf) "bc" (.branch .leaf "d" .leaf)

#eval numberTree bt
-- BinTree.branch
--   (BinTree.branch (BinTree.leaf) (0, "a") (BinTree.leaf))
--   (1, "bc")
--   (BinTree.branch (BinTree.leaf) (2, "d") (BinTree.leaf))

-- 4.1.5 Monads: A Functional Design Pattern

-- polymorphic type, such as `Option`, `Except ε`, `WithLog α`, or `State σ`
-- sequencing operator `andThen`
-- operator `ok` which is a kind of identity
-- collection of other operations, such as `none`, `fail`, `save`, and `get`, that name ways of using the type

-- 4.2 The Monad Type Class

class BasicMonad (m : Type u → Type v) where
  pure : α → m α
  bind : m α → (α → m β) → m β

#check Monad
-- Monad.{u, v} (m : Type u → Type v) : Type (max (u + 1) v)

#check Monad.mk
-- Monad.mk.{u, v} {m : Type u → Type v} [toApplicative : Applicative m] [toBind : Bind m] : Monad m

instance : Monad Option where
  pure := some
  bind opt next :=
    match opt with
    | none => none
    | some x => next x

instance : Monad (Except ε) where
  pure := Except.ok
  bind attempt next :=
    match attempt with
    | .error err => .error err
    | .ok x => next x

-- the type of the state cannot change between calls to `get` and `set`
instance : Monad (State σ) where
  pure := .ok
  bind first next :=
    fun s =>
      let (s', x) := first s
      next x s'

-- coerce `α` into `m α` for monad `m`
instance [Monad m] : Coe α (m α) where coe := pure

set_option linter.checkUnivs false in
def firstThirdFifth [Monad m] (lookup : List α → Nat → m α) (xs : List α)
    : m (α × α × α) :=
  lookup xs 0 >>= fun first =>
  lookup xs 2 >>= fun third =>
  lookup xs 4 >>= fun fifth =>
  (first, third, fifth)

-- 4.2.1 General Monad Operations

def mapM [Monad m] (f : α → m β) : List α → m (List β)
  | [] => pure []
  | x :: xs =>
    f x >>= fun hd =>
    mapM f xs >>= fun tl =>
    hd :: tl

def increment (howMuch : Int) : State Int Int :=
  .get >>= fun i =>
  .set (i + howMuch) >>= fun () =>
  i

#eval mapM increment [1, 2, 3, 4, 5] 0
-- (15, [0, 1, 3, 6, 10])

instance : Monad (WithLog logged) where
  pure x := { log := [], val := x }
  bind result next :=
    let { log := thisOut, val } := result
    let { log := nextOut, val } := next val
    { log := thisOut ++ nextOut, val }

def saveIfEven (i : Nat) : WithLog Nat Nat :=
  (if i % 2 == 0 then
    .save i
   else pure ()) >>= fun () =>
  i

#eval mapM saveIfEven [0, 1, 2, 3, 4]
-- { log := [0, 2, 4], val := [0, 1, 2, 3, 4] }

-- 4.2.2 The Identity Monad

-- monads encode programs with effects, such as failure, exceptions, or logging

-- the _identity monad_ has no effects

#check Id
-- Id.{u} (type : Type u) : Type u

instance : Monad Id where
  pure := (·)
  bind x f := f x

#eval mapM (m := Id) (do return · + 1) [1, 2, 3, 4, 5]
-- [2, 3, 4, 5, 6]

#eval mapM (do return · + 1) [1, 2, 3, 4, 5]

-- 4.2.3 The Monad Contract

-- `pure` should be left/right identity of bind
-- `bind` should be associative

-- Id
theorem Id.left_identity (x : α) (f : α → Id β) : pure x >>= f = f x := rfl
theorem Id.right_identity (x : Id α) : x >>= pure = x := rfl
theorem Id.bind_identity (x : Id α) (f : α → Id β) (g : β → Id γ)
    : x >>= f >>= g = x >>= (fun x => (f x) >>= g) := rfl

-- WithLog l
theorem WithLog.left_identity (x : α) (f : α → WithLog l β) : pure x >>= f = f x := rfl
theorem WithLog.right_identity (x : WithLog l α) : x >>= pure = x := by
  simp [Bind.bind, Pure.pure]
theorem WithLog.bind_identity (x : WithLog l α) (f : α → WithLog l β) (g : β → WithLog l γ)
    : x >>= f >>= g = x >>= (fun x => (f x) >>= g) := by
  simp [Bind.bind]

-- State σ
theorem State.left_identity (x : α) (f : α → State σ β) : pure x >>= f = f x := rfl
theorem State.right_identity (x : State σ α) : x >>= pure = x := rfl
theorem State.bind_identity (x : State σ α) (f : α → State σ β) (g : β → State σ γ)
    : x >>= f >>= g = x >>= (fun x => (f x) >>= g) := rfl

-- 4.2.4 Exercises

-- 4.2.4.1 Mapping on a Tree
-- Define a function BinTree.mapM. By analogy to mapM for lists, this function should
-- apply a monadic function to each data entry in a tree, as a preorder traversal. The
-- type signature should be:

def BinTree.mapM [Monad m] (f : α → m β) : BinTree α → m (BinTree β)
  | .leaf => pure .leaf
  | .branch l x r =>
    mapM f l >>= fun left =>
    f x >>= fun val =>
    mapM f r >>= fun right =>
    pure (.branch left val right)

instance : Monad List where
  pure x := [x]
  bind x f := x.flatMap f

#eval bt.mapM (fun s => s.chars.toList)
-- [BinTree.branch
--    (BinTree.branch (BinTree.leaf) 'a' (BinTree.leaf))
--    'b'
--    (BinTree.branch (BinTree.leaf) 'd' (BinTree.leaf)),
--  BinTree.branch
--    (BinTree.branch (BinTree.leaf) 'a' (BinTree.leaf))
--    'c'
--    (BinTree.branch (BinTree.leaf) 'd' (BinTree.leaf))]

-- 4.2.4.2 The Option Monad Contract

theorem Option.left_identity (x : α) (f : α → Option β) : pure x >>= f = f x := rfl
theorem Option.right_identity (x : Option α) : x >>= pure = x := by
  cases x <;> rfl
theorem Option.bind_identity (x : Option α) (f : α → Option β) (g : β → Option γ)
    : x >>= f >>= g = x >>= (fun x => (f x) >>= g) := by
  cases x <;> rfl

-- 4.3 Example: Arithmetic in Monads

-- monads can encode _any_ effect

-- 4.3.1 Arithmetic Expressions

inductive Expr (op : Type) where
  | const : Int → Expr op
  | prim : op → Expr op → Expr op → Expr op

inductive Arith where
  | plus
  | minus
  | times
  | div

-- 2 + 3
def ex1 : Expr Arith :=
  .prim .plus (.const 2) (.const 3)

-- 14 / (45 - 5 * 9)
def ex2 : Expr Arith :=
  .prim .div (.const 14)
    (.prim .minus (.const 45)
      (.prim .times (.const 5) (.const 9)))

-- 4.3.2 Evaluating Expressions

-- division by 0 is undefined, evaluation might fail

def applyPrimOption : Arith → Int → Int → Option Int
  | .plus, v1, v2 => v1 + v2
  | .minus, v1, v2 => v1 - v2
  | .times, v1, v2 => v1 * v2
  | .div, v1, v2 =>
    if v2 != 0 then v1 / v2
    else none

def Expr.evaluate? : Expr Arith → Option Int
  | .const x => x
  | .prim op e1 e2 =>
    e1.evaluate? >>= fun v1 =>
    e2.evaluate? >>= fun v2 =>
    applyPrimOption op v1 v2

#eval ex1.evaluate?
-- some 5

#eval ex2.evaluate?
-- none

def applyPrimExcept : Arith → Int → Int → Except String Int
  | .plus, v1, v2 => v1 + v2
  | .minus, v1, v2 => v1 - v2
  | .times, v1, v2 => v1 * v2
  | .div, v1, v2 =>
    if v2 != 0 then v1 / v2
    else .error s!"Tried to divide {v1} by zero"

def Expr.evaluate : Expr Arith → Except String Int
  | .const x => x
  | .prim op e1 e2 =>
    e1.evaluate >>= fun v1 =>
    e2.evaluate >>= fun v2 =>
    applyPrimExcept op v1 v2

#eval ex1.evaluate
-- Except.ok 5

#eval ex2.evaluate
-- Except.error "Tried to divide 14 by zero"

def Expr.evaluateM' [Monad m]
    (applyPrim : Arith → Int → Int → m Int)
    : Expr Arith → m Int
  | .const x => x
  | .prim op e1 e2 =>
    e1.evaluateM' applyPrim >>= fun v1 =>
    e2.evaluateM' applyPrim >>= fun v2 =>
    applyPrim op v1 v2

#eval ex2.evaluateM' applyPrimOption
-- none

#eval ex2.evaluateM' applyPrimExcept
-- Except.error "Tried to divide 14 by zero"

-- 4.3.3 Further Effects

inductive Prim (special : Type) where
  | plus
  | minus
  | times
  | other : special → Prim special

inductive CanFail where
  | div

def divOption : CanFail → Int → Int → Option Int
  | .div, x, y => if y == 0 then none else x / y

def divExcept : CanFail → Int → Int → Except String Int
  | .div, x, y =>
    if y == 0 then
      .error s!"Tried to divide {x} by zero"
    else x / y

def applyPrim [Monad m]
    (applySpecial : special → Int → Int → m Int)
    : Prim special → Int → Int → m Int
  | .plus, x, y => x + y
  | .minus, x, y => x - y
  | .times, x, y => x * y
  | .other op, x, y => applySpecial op x y

def Expr.evaluateM [Monad m]
    (applySpecial : special → Int → Int → m Int)
    : Expr (Prim special) → m Int
  | .const x => x
  | .prim op e1 e2 =>
    e1.evaluateM applySpecial >>= fun v1 =>
    e2.evaluateM applySpecial >>= fun v2 =>
    applyPrim applySpecial op v1 v2

-- 4.3.3.1 No Effects

-- can use `Empty` to signal that a function does not return

def applyEmpty [Monad m] (op : Empty) (_ _ : Int) : m Int :=
  nomatch op

open Expr Prim in
#eval (prim plus (const 5) (const (-14))).evaluateM applyEmpty
-- -9

-- 4.3.3.2 Nondeterministic Search

-- add `choose` function to the language of expressions

-- turn result of evaluator into a multiset of values, rather than a single value
-- - constant `n` evaluates to a singleton set `{n}`
-- - arithmetic operations other than division are calle on each pair from the Cartesian
--   product of the operators, e.g. `X + Y` evaluates to `{x + y | x ∈ X, y ∈ Y}`
-- - division `X / Y` evaluates to `{x / y | x ∈ X, y ∈ Y, y ≠ 0}`
-- - a choice `choose(x, y)` evaluates to `{x, y}`

-- monad representing this non-deterministic effect
inductive Many (α : Type) where
  | none : Many α
  | more : α → (Unit → Many α) → Many α

-- like `List α` except unlike `cons`, `more` stores a function that should compute remaining values on demand
-- so a consumer of `Many` can stop the search when they want

-- single result
def Many.one (x : α) : Many α := more x (fun () => none)

def Many.union : Many α → Many α → Many α
  | none, ys => ys
  | more x xs, ys => more x (fun () => (xs ()).union ys)

def Many.fromList : List α → Many α
  | [] => .none
  | x :: xs => .more x (fun () => fromList xs)

-- extract values for search

def Many.take : Nat → Many α → List α
  | 0, _ | _, none => []
  | n + 1, more x xs => x :: (xs ()).take n

def Many.takeAll : Many α → List α
  | none => []
  | more x xs => x :: (xs ()).takeAll

def Many.bind : Many α → (α → Many β) → Many β
  | none, _ => none
  | more x xs, f =>
    (f x).union <| (xs ()).bind f

instance : Monad Many where
  pure := .one
  bind := .bind

theorem Many.union_none : (m : Many α) → m.union none = m
  | none => rfl
  | more x xs => by
    simp [Many.union]
    funext
    apply union_none

theorem Many.union_assoc (m n o : Many α) :
    (m.union n).union o = m.union (n.union o) := by
  induction m with
  | none => rfl
  | more _ xs ih =>
    simp [Many.union]
    funext
    apply ih

theorem Many.bind_union (m n : Many α) (f : α → Many β) :
    (m.union n).bind f = (m.bind f).union (n.bind f) := by
  induction m with
  | none => simp [Many.union, Many.bind]
  | more _ xs ih =>
    simp [Many.union, Many.bind, ih, Many.union_assoc]

-- Many monad contract

theorem Many.left_identity (x : α) (f : α → Many β) : pure x >>= f = f x := by
  simp [Bind.bind, Pure.pure, Many.one, Many.bind, Many.union_none]

theorem Many.right_identity (x : Many α) : x >>= pure = x := by
  simp [Bind.bind, Pure.pure]
  induction x with
  | none => rfl
  | more x xs ih =>
    simp [Many.one, Many.bind, Many.union]
    funext
    apply ih

theorem Many.bind_identity (x : Many α) (f : α → Many β) (g : β → Many γ)
    : x >>= f >>= g = x >>= (fun x => (f x) >>= g) := by
  simp [Bind.bind]
  induction x with
  | none => rfl
  | more x xs ih =>
    simp [Many.bind, Many.bind_union, ih]

-- example search

def addsTo (goal : Nat) : List Nat → Many (List Nat)
  | [] =>
    if goal == 0 then
      pure []
    else .none
  | x :: xs =>
    if x > goal then
      addsTo goal xs
    else
      (addsTo goal xs).union
        (addsTo (goal - x) xs >>= fun answer =>
          x :: answer)

def List.print [ToString α] : List α → IO Unit
  | [] => pure ()
  | x :: xs => do
    IO.println x
    xs.print

#eval (addsTo 15 [1, 2, 3, 4, 5, 6, 7, 8, 9, 10]).takeAll.print
-- [7, 8]
-- [6, 9]
-- [5, 10]
-- [4, 5, 6]
-- [3, 5, 7]
-- [3, 4, 8]
-- [2, 6, 7]
-- [2, 5, 8]
-- [2, 4, 9]
-- [2, 3, 10]
-- [2, 3, 4, 6]
-- [1, 6, 8]
-- [1, 5, 9]
-- [1, 4, 10]
-- [1, 3, 5, 6]
-- [1, 3, 4, 7]
-- [1, 2, 5, 7]
-- [1, 2, 4, 8]
-- [1, 2, 3, 9]
-- [1, 2, 3, 4, 5]

inductive NeedsSearch where
  | div
  | choose

def applySearch : NeedsSearch → Int → Int → Many Int
  | .choose, x, y => Many.fromList [x, y]
  | .div, x, y =>
    if y == 0 then .none
    else .one (x / y)

section
open Expr Prim NeedsSearch

#eval
  (evaluateM applySearch
    (prim plus (const 1)
      (prim (other choose) (const 2)
        (const 5)))).takeAll
-- [3, 6]

#eval
  (evaluateM applySearch
    (prim plus (const 1)
      (prim (other div) (const 2)
        (const 0)))).takeAll
-- []

#eval
  (evaluateM applySearch
    (prim (other div) (const 90)
      (prim plus (prim (other choose) (const (-5)) (const 5))
        (const 5)))).takeAll
-- [9]

end

-- 4.3.3.3 Custom Environments

-- make evaluator user-extensible by allowing strings to be used as operators and providing
-- a mapping from strings to a function implementing them (environment)

-- `evaluateM` does not need an extra argument to hold the environment because passing an arg
-- like this is a monad

-- using functions as a monad is called a _reader monad_

-- rules for evaluating in the reader monad:
-- - constant `n` evaluates to a constant function `fun _ => n`
-- - arithmetic operators evaluate to functions that pass their arguments,
--   e.g. `f + g` evaluates to `fun e => f e + g e`
-- - custom operators evaluate to the result of applying the custom operator to the arguments,
--   so `f op g` evaluates to `fun e => h (f e) (g e)` if `e` contains `(op, h)`, `0` otherwise

def Reader (ρ : Type) (α : Type) : Type := ρ → α

def read : Reader ρ ρ := fun env => env

def Reader.pure (x : α) : Reader ρ α := fun _ => x

def Reader.bind (res : Reader ρ α) (f : α → Reader ρ β) : Reader ρ β :=
  fun env => (f <| res env) env

-- Reader monad
instance : Monad (Reader ρ) where
  pure := .pure
  bind := .bind

-- Reader monad contract
theorem Reader.left_identity (x : α) (f : α → Reader ρ β) : pure x >>= f = f x := by
  simp [Bind.bind]; trivial

theorem Reader.right_identity (x : Reader ρ α) : x >>= pure = x := by
  simp [Bind.bind]; trivial

theorem Reader.bind_identity (x : Reader ρ α) (f : α → Reader ρ β) (g : β → Reader ρ γ)
    : x >>= f >>= g = x >>= (fun x => (f x) >>= g) := by
  simp [Bind.bind]; trivial

abbrev Env : Type := List (String × (Int → Int → Int))

def exampleEnv : Env := [("max", max), ("mod", (· % ·))]

def applyPrimReader (op : String) (x y : Int) : Reader Env Int :=
  fun env =>
    match env.lookup op with
    | none => 0
    | some h => h x y

open Expr Prim in
#eval evaluateM applyPrimReader
    (prim (other "max") (prim plus (const 5) (const 4))
      (prim times (const 3)
        (const 2)))
    exampleEnv
-- 9

-- 4.3.4 Exercises

-- 4.3.4.1 Checking Monad Contracts
-- Check the monad contract for `State σ` and `Except ε`

#check State.left_identity
#check State.right_identity
#check State.bind_identity

theorem Except.left_identity (x : α) (f : α → Except ε β) : pure x >>= f = f x := rfl

theorem Except.right_identity (x : Except ε α) : x >>= pure = x := by
  simp [Bind.bind]; split <;> rfl

theorem Except.bind_identity (x : Except ε α) (f : α → Except ε β) (g : β → Except ε γ)
    : x >>= f >>= g = x >>= (fun x => (f x) >>= g) := by
  simp [Bind.bind]
  cases x <;> rfl

-- 4.3.4.2 Readers with Failure
-- Adapt the reader monad example so that it can also indicate failure when the custom operator
-- is not defined, rather than just returning zero. In other words, given the definition:

def ReaderMonad [Monad m] (ρ α : Type) : Type := Reader ρ (m α)

-- 1. Write suitable `pure` and `bind` functions
def ReaderMonad.pure [Monad m] (x : α) : ReaderMonad (m := m) ρ α :=
  fun _ => Pure.pure x

def ReaderMonad.bind [Monad m]
    (read : ReaderMonad (m := m) ρ α)
    (f : α → ReaderMonad (m := m) ρ β)
    : ReaderMonad (m := m) ρ β :=
  fun env => read env >>= (f · env)

-- 2. Check that these functions satisfy the Monad contract
instance [Monad m] : Monad (ReaderMonad (m := m) ρ) where
  pure := .pure
  bind := .bind

theorem ReaderMonad.left_identity [Monad m]
    {left_id : ∀ (x : α) (f : α → m β), Pure.pure x >>= f = f x}
    (x : α) (f : α → ReaderMonad (m := m) ρ β)
    : pure x >>= f = f x := by
  funext env
  exact left_id x (f · env)

theorem ReaderMonad.right_identity [Monad m]
    {right_id : ∀ (x : m α), x >>= Pure.pure = x}
    (x : ReaderMonad (m := m) ρ α) : x >>= pure = x := by
  funext
  simp [Bind.bind, ReaderMonad.bind, ReaderMonad.pure, right_id]

theorem ReaderMonad.bind_identity [Monad m]
    {bind_id : ∀ (x : m α) (f : α → m β) (g : β → m γ), x >>= f >>= g = x >>= (fun x => (f x) >>= g)}
    (x : ReaderMonad (m := m) ρ α)
    (f : α → ReaderMonad (m := m) ρ β)
    (g : β → ReaderMonad (m := m) ρ γ)
    : x >>= f >>= g = x >>= (fun x => (f x) >>= g) := by
  funext
  simp [Bind.bind, ReaderMonad.bind, bind_id]

-- 3. Write Monad instances for ReaderOption and ReaderExcept
abbrev ReaderOption : Type → Type → Type := ReaderMonad (m := Option)
abbrev ReaderExcept (ε : Type) : Type → Type → Type := ReaderMonad (m := Except ε)

instance : Monad (ReaderOption ρ) where
instance : Monad (ReaderExcept ε ρ) where

instance : MonadExcept String Option where
  throw _ := none
  tryCatch b _ := b

instance : MonadExcept String (Except String) where
  throw op := .error s!"Operator not found: {op}"
  tryCatch b _ := b

-- 4. Define suitable `applyPrimReaderMonad` operator and test with `evaluateM` on some example expressions
def applyPrimReaderMonad [Monad m] [MonadExcept String m]
    (op : String) (x y : Int) : ReaderMonad (m := m) Env Int :=
  fun env =>
    match env.lookup op with
    | none => throw op
    | some h => h x y

open Expr Prim in
#eval evaluateM (applyPrimReaderMonad (m := Option))
    (prim (other "max") (prim plus (const 5) (const 4))
      (prim times (const 3)
        (const 2)))
    exampleEnv
-- some 9

open Expr Prim in
#eval evaluateM (applyPrimReaderMonad (m := Option))
    (prim (other "no") (prim plus (const 5) (const 4))
      (prim times (const 3)
        (const 2)))
    exampleEnv
-- none

open Expr Prim in
#eval evaluateM (applyPrimReaderMonad (m := Except String))
    (prim (other "max") (prim plus (const 5) (const 4))
      (prim times (const 3)
        (const 2)))
    exampleEnv
-- Except.ok 9

open Expr Prim in
#eval evaluateM (applyPrimReaderMonad (m := Except String))
    (prim (other "no") (prim plus (const 5) (const 4))
      (prim times (const 3)
        (const 2)))
    exampleEnv
-- Except.error "Operator not found: no"

-- 4.3.4.3 A Tracing Evaluator
-- The WithLog type can be used with the evaluator to add optional tracing of some operations.
-- In particular, the type `ToTrace` can serve as a signal to trace a given operator:

inductive Trace (α : Type) where
  | noTrace : α → Trace α
  | trace : α → Trace α

-- For the tracing evaluator, expressions should have type `Expr (Prim (Trace (Prim Empty)))`.
-- This says that the operators in the expression consist of addition, subtraction, and
-- multiplication, augmented with traced versions of each. The innermost argument is `Empty`
-- to signal that there are no further special operators inside of trace, only the three basic ones.

-- Do the following:
-- 1. Implement a `Monad (WithLog logged)` instance

#check (inferInstance : Monad (WithLog _))

-- 2. Write an `applyTraced` function to apply traced operators to their arguments, logging
-- both the operator and the arguments, with type
-- `Trace (Prim Empty) → Int → Int → WithLog (Prim Empty × Int × Int) Int`

def applyTraced : Trace (Prim Empty) → Int → Int → WithLog (Prim Empty × Int × Int) Int
  | .noTrace t, x, y =>
    { log := [],
      val := (applyPrim (m := Id) applyEmpty) t x y
    }
  | .trace t, x, y =>
    { log := (t, x, y),
      val := (applyPrim (m := Id) applyEmpty) t x y
    }

deriving instance Repr for WithLog
deriving instance Repr for Empty
deriving instance Repr for Prim

open Expr Prim Trace in
#eval
  evaluateM applyTraced
    (prim (other (trace times))
      (prim (other (trace plus)) (const 1)
        (const 2))
      (prim (other (trace minus)) (const 3)
        (const 4)))
-- { log := [(Prim.plus, 1, 2), (Prim.minus, 3, 4), (Prim.times, 3, -1)], val := -3 }

open Expr Prim Trace in
#eval
  evaluateM applyTraced
    (prim (other (noTrace times))
      (prim (other (trace plus)) (const 1)
        (const 2))
      (prim (other (trace minus)) (const 3)
        (const 4)))
-- { log := [(Prim.plus, 1, 2), (Prim.minus, 3, 4)], val := -3 }
