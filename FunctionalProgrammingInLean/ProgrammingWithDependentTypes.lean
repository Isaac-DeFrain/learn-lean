-- # 7 Programming with Dependent Types

-- _dependent types_ are types that contain non-type expressions

def natOrStringThree (b : Bool) : if b then Nat else String :=
  match b with
  | true => (3 : Nat)
  | false => "three"

-- ## 7.1 Indexed Families

inductive Vect (α : Type u) : Nat → Type u where
  | nil : Vect α 0
  | cons : α → Vect α n → Vect α (n + 1)

-- `α` is a parameter - fixed
-- `n` is an index - varies

def List.toVect : (l : List α) → Vect α l.length
  | [] => .nil
  | x :: xs => .cons x <| toVect xs

def Vect.toList : Vect α n → List α
  | .nil => []
  | .cons x xs => x :: toList xs

def Vect.print [ToString α] : Vect α n → String → String
  | .nil, _ => ""
  | .cons x .nil, _ => ToString.toString x
  | .cons x xs, sep =>
    ToString.toString x |>.append sep |>.append <| print xs sep

example : Vect String 2 := .cons "hello" <| .cons "world" .nil

/-- info: "hello world" -/
#guard_msgs in
#eval ["hello", "world"].toVect.print " "

def Vect.replicate (n : Nat) (x : α) : Vect α n :=
  match n with
  | 0 => .nil
  | n + 1 => .cons x <| replicate n x

-- require `zip` to take vectors of the same length

def Vect.zip : Vect α n → Vect β n → Vect (α × β) n
  | .nil, _ => .nil
  | .cons x xs, .cons y ys => .cons (x, y) <| zip xs ys

-- do not need to pattern match on `.cons _ _, .nil`

-- Getting a feel for programming with dependent types requires experience, and the exercises
-- in this section are very important. For each exercise, try to see which mistakes the type
-- checker can catch, and which ones it can't, by experimenting with the code as you go. This
-- is also a good way to develop a feel for the error messages.

-- - Double-check that `Vect.zip` gives the right answer when combining the three highest peaks
--   in Oregon with the three highest peaks in Denmark. Because `Vect` doesn't have the
--   syntactic sugar that `List` has, it can be helpful to begin by defining
--   `oregonianPeaks : Vect String 3` and `danishPeaks : Vect String 3`.

/-- info: [("a", 0), ("b", 1), ("c", 2)] -/
#guard_msgs in
#eval Vect.zip ["a", "b", "c"].toVect [0, 1, (2 : Nat)].toVect |>.toList

-- - Define a function `Vect.map` with type `(α → β) → Vect α n → Vect β n`.

def Vect.map : (α → β) → Vect α n → Vect β n
  | _, .nil => .nil
  | f, .cons x xs => .cons (f x) <| map f xs

-- - Define a function `Vect.zipWith` that combines the entries in a `Vect` one at a time with
--   a function. It should have the type `(α → β → γ) → Vect α n → Vect β n → Vect γ n`.

def Vect.zipWith : (α → β → γ) → Vect α n → Vect β n → Vect γ n
  | _, .nil, _ => .nil
  | f, .cons x xs, .cons y ys => .cons (f x y) <| zipWith f xs ys

-- - Define a function `Vect.unzip` that splits a `Vect` of pairs into a pair of `Vect`s. It
--   should have the type `Vect (α × β) n → Vect α n × Vect β n`.

def Vect.unzip : Vect (α × β) n → Vect α n × Vect β n
  | .nil => (.nil, .nil)
  | .cons (x, y) xys =>
    let (xs, ys) := unzip xys
    (.cons x xs, .cons y ys)

-- - Define a function `Vect.push` that adds an entry to the end of a `Vect`. Its type should
--   be `Vect α n → α → Vect α (n + 1)` and `#eval Vect.push (.cons "snowy" .nil) "peaks"`
--   should yield `Vect.cons "snowy" (Vect.cons "peaks" (Vect.nil))`.

def Vect.push : Vect α n → α → Vect α (n + 1)
  | .nil, y => .cons y .nil
  | .cons x xs, y => .cons x <| push xs y

/-- info: Vect.cons "snowy" (Vect.cons "peaks" (Vect.nil)) -/
#guard_msgs in
#eval Vect.push (.cons "snowy" .nil) "peaks"

-- - Define a function `Vect.reverse` that reverses the order of a `Vect`.

def Vect.reverse : Vect α n → Vect α n
  | .nil => .nil
  | .cons x xs => xs.reverse.push x

/-- info: Vect.cons "peaks" (Vect.cons "snowy" (Vect.nil)) -/
#guard_msgs in
#eval Vect.cons "snowy" (Vect.cons "peaks" (Vect.nil)) |>.reverse

-- - Define a function `Vect.drop` with the following type:
--   `(n : Nat) → Vect α (k + n) → Vect α k`. Verify that it works by checking that
--   `#eval danishPeaks.drop 2 yields Vect.cons "Ejer Bavnehøj" (Vect.nil)`.

def Vect.drop : (n : Nat) → Vect α (k + n) → Vect α k
  | 0, xs => xs
  | n + 1, .cons _ xs => xs.drop n

/-- info: Vect.nil -/
#guard_msgs in
#eval Vect.push (.cons "a" .nil) "b" |>.drop 2

-- - Define a function `Vect.take` with type `(n : Nat) → Vect α (k + n) → Vect α n` that
--   returns the first n entries in the Vect. Check that it works on an example.

def Vect.take : (n : Nat) → Vect α (k + n) → Vect α n
  | 0, _ => .nil
  | n + 1, .cons x xs => .cons x <| take n xs

/-- info: Vect.cons "a" (Vect.nil) -/
#guard_msgs in
#eval Vect.push (.cons "a" .nil) "b" |>.take 1
