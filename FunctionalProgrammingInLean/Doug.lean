-- doug cli

import FunctionalProgrammingInLean.OverloadingAndTypeClasses

structure Config where
  useASCII : Bool := false
  showDotFiles : Bool := false
  currentPrefix : String := ""

def usage : String :=
  "Usage: doug [-a] [--ascii] [DIR]
Options:
\t-a\tShow all files, including dotfiles
\t--ascii\tUse ASCII characters to display the directory structure
\tDIR\tDirectory to start recursive crawl from"

def configFromArgs (args : List String) : Option Config :=
  match args.toArray.qsort with
  | #[] => some {}
  | #["--ascii"] => some { useASCII := true }
  | #["-a"] => some { showDotFiles := true }
  | #["--ascii", "-a"] => some { useASCII := true, showDotFiles := true }
  | _ => none

-- use reader instance to pass config

abbrev ConfigIO (α : Type) : Type := ReaderT Config IO α

instance : Monad ConfigIO where
  pure x := fun _ => pure x
  bind action next := fun cfg => do next (← action cfg) cfg

def ConfigIO.run (action : ConfigIO α) (cfg : Config) : IO α :=
  action cfg

instance [Monad m] : MonadReader ρ (ReaderT ρ m) where
  read := pure

instance : MonadWithReader ρ (ReaderT ρ m) where
  withReader change action := action ∘ change

-- IO actions do not need a config
instance : MonadLift m (ReaderT ρ m) where
  monadLift action := fun _ => action

inductive Entry where
  | file : String → Entry
  | dir : String → Entry

-- want to skip files named `.` or `..`

def toEntry (path : System.FilePath) : ConfigIO (Option Entry) := do
  match path.components.getLast? with
  | none => pure <| some <| .dir ""
  | some "." | some ".." => pure none
  | some name =>
    if name.startsWith '.' && !(← read).showDotFiles then
      pure none
    else
      pure <| some <| if (← path.isDir) then .dir name else .file name

def dirLT (e1 : IO.FS.DirEntry) (e2 : IO.FS.DirEntry) : Bool :=
  e1.fileName < e2.fileName

def Config.preFile (cfg : Config) :=
  if cfg.useASCII then "|--" else "├──"

def Config.preDir (cfg : Config) :=
  if cfg.useASCII then "|  " else "│  "

def Config.fileName (cfg : Config) (file : String) : String :=
  s!"{cfg.currentPrefix}{cfg.preFile} {file}"

def Config.dirName (cfg : Config) (dir : String) : String :=
  s!"{cfg.currentPrefix}{cfg.preFile} {dir}/"

def Config.inDirectory (cfg : Config) : Config :=
  {cfg with currentPrefix := cfg.preDir ++ " " ++ cfg.currentPrefix}

def showFileName (file : String) : ConfigIO Unit := do
  IO.println ((← read).fileName file)

def showDirName (dir : String) : ConfigIO Unit := do
  IO.println ((← read).dirName dir)

def doList [Applicative f] : List α → (α → f Unit) → f Unit
  | [], _ => pure ()
  | x :: xs, action => action x *> doList xs action

-- Lean has no way of knowing the directory tree is finite so `dirTree` must be partial def

/--
Draws the directory tree
-/
partial def dirTree (path : System.FilePath) : ConfigIO Unit := do
  match ← toEntry path with
  | none => pure ()
  | some (.file name) => showFileName name
  | some (.dir name) =>
    showDirName name
    let contents ← path.readDir
    withReader (·.inDirectory) <|
      doList (contents.qsort dirLT).toList fun d =>
        dirTree d.path

def startingDir (args : List String) : IO System.FilePath := do
  let nonOptionArgs := args.filter (fun arg => arg != "--ascii" && arg != "-a")
  match nonOptionArgs with
  | "." :: _ => IO.currentDir
  | dir :: _ => pure (dir.dropEndWhile (· == '/')).copy
  | _ => IO.currentDir

def main (args : List String) : IO UInt32 := do
  if args.contains "--help" then
    IO.println usage
    pure 0
  else
    let options := args.filter (fun arg => arg == "--ascii" || arg == "-a")
    let startingDir := startingDir args

    match configFromArgs options with
    | some config =>
      (dirTree (← startingDir)).run config
      pure 0
    | none =>
      IO.eprintln s!"Didn't understand argument(s) {args.separate " "}\n"
      IO.eprintln usage
      pure 1
