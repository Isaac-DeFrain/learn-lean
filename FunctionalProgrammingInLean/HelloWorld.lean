/- 2. Hello World -/

-- 2.1 Running a Program

-- use `--run` option to the Lean exe

def main' : IO Unit := IO.println "Hello, world!"

/-
```shell
$ lean --run FunctionalProgrammingInLean/HelloWorld.lean
Hello, world!
```
-/

-- 2.1.1 Anatomy of a Greeting

-- separation of evaluation of expressions and IO actions (side effects)

-- 2.1.2 Functional Programming vs Effects

-- 2.1.3 Real-World Functional Programming

-- 2.1.4 Combining `IO` Actions

-- `do` notation is a sub-language for modeling imperative programs

def main : IO Unit := do
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout

  stdout.putStrLn "What is your name?"
  let input ← stdin.getLine
  let name := input.dropEndWhile Char.isWhitespace

  stdout.putStrLn s!"Hello, {name}!"

-- 2.2 Step By Step

-- 2.2.1 Standard IO

-- 2.2.2 Asking a Question

-- 2.2.3 Greeting the User

-- 2.2.4 IO Actions as Values

-- can use functions as control structures

def twice (action: IO Unit) : IO Unit := do
  action; action

/--
info:
hello
hello
-/
#guard_msgs (info) in
#eval twice (IO.println "hello")

def nTimes (action : IO Unit) : Nat → IO Unit
  | 0 => pure ()
  | n + 1 => do
    action
    nTimes action n

/--
info:
hello
hello
hello
-/
#guard_msgs (info) in
#eval nTimes (IO.println "hello") 3

-- since IO actions are first-class values, they can be stored in data structures for later execution

def countdown : Nat → List (IO Unit)
  | 0 => [IO.println "Blast off!"]
  | n + 1 => IO.println s!"{n + 1}" :: countdown n

def runActions : List (IO Unit) → IO Unit
  | [] => pure ()
  | action :: as => do
    action; runActions as

/--
info:
3
2
1
Blast off!
-/
#guard_msgs (info) in
#eval runActions (countdown 3)

-- 2.2.5 Exercise

#eval do
  let englishGreeting := IO.println "Hello!"
  IO.println "Bonjour!"
  englishGreeting

-- 2.3 Starting a Project

-- `lake` (Lean Make)

-- 2.3.1 First Steps

/-
```shell
$ lake new <project>
```
-/

-- creates a directory `<project>` that contains the following files:
-- `Main.lean` - file in which the Lean compiler will look for the `main` action
-- `<Project>.lean` and `<Project>/Basic.lean` - scaffolding of a support library
-- `lakefile.toml` - configuration that `lake` needs to build the app
-- `lean-toolchain` - identifier for the specific version of Lean used

-- initializes `<project>` as a git repo with `.gitignore`

-- can `lake init` in an existing directory

-- `lake build` builds the binary and places it in `.lake/build/bin`
-- can run `.lake/build/bin/<project>` directly or use `lake exe <project>`

-- 2.3.2 Lakefiles

-- [Lake docs](https://lean-lang.org/doc/reference/latest/find/?domain=Verso.Genre.Manual.section&name=lake-config-toml)

-- 2.3.3 Libraries and Imports

/-
File: Greeting/Smile.lean
1 | def Expression.happy : String := "a big smile"
-/

/-
File: Main.lean
1 | import Greeting
2 | import Greeting.Smile
3 |
4 | open Expression
5 |
6 | def main : IO Unit :=
7 |   IO.println s!"Hello, {hello}, with {happy}!"
-/

-- modules are units of code ditribution (`import` makes content available)
-- namespaces are units of code organization (`open` makes names available)

-- 2.4 Worked Example: cat

-- `feline` simplified version of `cat`

-- 2.4.1 Getting Started

-- see [Feline.lean](./Feline.lean)

-- 2.4.2 Concatenating Streams

-- 2.4.2.1 Streams

-- main work done by `dump`
-- reads (and dumps to stdout) until `read` returns an empty array

-- partial function declaration needed when cannot prove termination

-- `IO.FS.Stream` represents POSIX stream
structure IOFSStream where
  flush   : IO Unit
  read    : USize → IO ByteArray
  write   : ByteArray → IO Unit
  getLine : IO String
  putStr  : String → IO Unit
  isTty   : BaseIO Bool

-- 2.4.2.2 Handling Input

-- 2.4.2.3 Main

-- three options for `main` action:
-- 1. `main : IO Unit` - no command-line args and always exit code 0
-- 2. `main : IO UInt32` - no command-line args, but has exit codes
-- 3. `main : List String → IO UInt32` - command-line args and exit codes

-- 2.5 Additional Conveniences

-- 2.5.1 Nested Actions

-- inside do block, can wite
--   (← IO.getStdout).putStrLn "hello"
-- instead of
--   let stdout ← IO.getStdout
--   stdout.puStrLn "hello"

-- 2.5.2 Flexible Layouts for `do`

-- can use whitespace, {}, and ;

-- 2.5.3 Running `IO` Actions with `#eval`

-- `#eval` can be used to execute IO actions

-- 2.6 Summary
