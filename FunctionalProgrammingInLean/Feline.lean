/-- `feline` exe - simplified `cat` -/

def bufsize : USize := 20 * 1024  -- 20kB

/--
Dumps input stream to stdout
-/
partial def dump (stream : IO.FS.Stream) : IO Unit := do
  let buf ← stream.read bufsize
  if buf.isEmpty then
    pure ()
  else
    (← IO.getStdout).write buf
    dump stream

/--
Checks file existence and reads stream
-/
def fileStream (filename : System.FilePath) : IO (Option IO.FS.Stream) := do
  let fileExists ← filename.pathExists
  if not fileExists then
    (← IO.getStderr).putStrLn s!"File not found: {filename}"
    pure none
  else
    let handle ← IO.FS.Handle.mk filename IO.FS.Mode.read
    pure <| some <| IO.FS.Stream.ofHandle handle

/--
Main work loop
-/
def process (exitCode : UInt32) (args : List String) : IO UInt32 := do
  match args with
  | [] => pure exitCode
  | "-" :: args =>
    dump (← IO.getStdin)
    process exitCode args
  | filename :: args =>
    match ← fileStream ⟨filename⟩ with
    | none => process 1 args
    | some stream =>
      dump stream
      process exitCode args

def printHelp : IO UInt32 := do
    let helpMsg := "Feline - simplified cat
  Print the contents of stdin and files to stdout.

  Usage: feline <filename>*
    - : stdin

  Returns non-zero error code if file is not found."
    IO.println helpMsg
    pure 0

def main (args : List String) : IO UInt32 := do
  match args with
  | [] => process 0 ["-"]
  | ["--help"] => printHelp
  | _ => process 0 args
