import NearLinear4ct

/-!
CLI entry point. Mirrors `../src/main.cpp`.

The flag surface matches the C++ `main`: each mode is selected by a
`--combine_rules` / `--enum_wheels` / … switch (modes are independent, not
mutually exclusive), and the required options for each mode are validated up front
(C++ `existArgs`: warn `Specify X.` and `exit(1)`).

Each mode dispatches to its driver (P6). A failed proof obligation inside a
`check_*` driver throws, which propagates out of `main` and exits non-zero (L1),
matching the C++ `assert` abort.
-/


open NearLinear4ct

/-- Parsed command line: present boolean flags + option/value pairs. -/
structure Args where
  flags : List String := []
  vals : List (String × String) := []

/-- Short → long option names (C++ `value<...>` short aliases). -/
def shortToLong : List (Char × String) :=
  [('C', "confdir"), ('R', "ruledir"), ('S', "combined_ruledir"),
   ('W', "cartwheeldir"), ('w', "wheel"), ('d', "degree"),
   ('o', "outdir"), ('H', "help"), ('v', "verbosity")]

/-- Options that take a value (everything else is a boolean switch). -/
def valuedOptions : List String :=
  ["confdir", "ruledir", "combined_ruledir", "cartwheeldir",
   "wheel", "degree", "outdir", "verbosity"]

def isValued (name : String) : Bool := valuedOptions.contains name

partial def parse (args : List String) (acc : Args) : Args :=
  match args with
  | [] => acc
  | tok :: rest =>
    if tok.startsWith "--" then
      let body := (tok.drop 2).toString
      if body.contains '=' then
        let name := (body.takeWhile (· != '=')).toString
        let val := ((body.dropWhile (· != '=')).drop 1).toString
        parse rest { acc with vals := (name, val) :: acc.vals }
      else if isValued body then
        match rest with
        | v :: rest' => parse rest' { acc with vals := (body, v) :: acc.vals }
        | [] => acc
      else parse rest { acc with flags := body :: acc.flags }
    else if tok.startsWith "-" && tok.length == 2 then
      let c := tok.toList.getLast!
      match List.lookup c shortToLong with
      | some name =>
        if isValued name then
          match rest with
          | v :: rest' => parse rest' { acc with vals := (name, v) :: acc.vals }
          | [] => acc
        else parse rest { acc with flags := name :: acc.flags }
      | none => parse rest acc
    else parse rest acc

def Args.has (a : Args) (flag : String) : Bool := a.flags.contains flag
def Args.get? (a : Args) (key : String) : Option String := a.vals.lookup key

/-- Mirror of C++ `existArgs`: warn `Specify X.` for each missing arg, return
whether all are present. -/
def existArgs (a : Args) (names : List String) : IO Bool := do
  let mut ok := true
  for n in names do
    if (a.get? n).isNone then
      IO.eprintln s!"Specify {n}."
      ok := false
  return ok

def helpText : String :=
  "Options:\n" ++
  "  --combine_rules           Combine rules\n" ++
  "  --enum_wheels             Enumerate wheels\n" ++
  "  --enum_cartwheels         Enumerate cartwheels\n" ++
  "  --check_deg8              Combine cartwheels with degree 8 center\n" ++
  "  --check_7triangle         Combine cartwheels to form a 7-triangle\n" ++
  "  --check_deg7              Combine cartwheels with degree 7 center\n" ++
  "  -C [ --confdir ] arg      A directory containing configuration files\n" ++
  "  -R [ --ruledir ] arg      A directory containing rule files\n" ++
  "  -S [ --combined_ruledir ] arg  A directory containing combined rule files\n" ++
  "  -W [ --cartwheeldir ] arg A directory containing cartwheel files\n" ++
  "  -w [ --wheel ] arg        A wheel file\n" ++
  "  -d [ --degree ] arg       Degree of the center vertex of wheels\n" ++
  "  -o [ --outdir ] arg       Output directory\n" ++
  "  -H [ --help ]             Display options\n" ++
  "  -v [ --verbosity ] arg    1 for debug, 2 for trace"

/-- Fetch a required option, assuming `existArgs` already validated its presence. -/
def need (args : Args) (key : String) : String := (args.get? key).getD ""

def main (argv : List String) : IO UInt32 := do
  let args := parse argv {}
  if args.has "help" then
    IO.println helpText
    return 0

  if args.has "combine_rules" then
    unless (← existArgs args ["ruledir", "confdir", "outdir"]) do return 1
    runCombineRules (need args "confdir") (need args "ruledir") (need args "outdir")
  if args.has "enum_wheels" then
    unless (← existArgs args ["degree", "confdir", "ruledir", "combined_ruledir", "outdir"]) do
      return 1
    let degree := ((need args "degree").toInt?.getD 0).toNat
    runEnumWheels degree (need args "confdir") (need args "ruledir")
      (need args "combined_ruledir") (need args "outdir")
  if args.has "enum_cartwheels" then
    unless (← existArgs args ["wheel", "confdir", "ruledir", "combined_ruledir", "outdir"]) do
      return 1
    runEnumCartwheels (need args "wheel") (need args "confdir") (need args "ruledir")
      (need args "combined_ruledir") (need args "outdir")
  if args.has "check_deg8" then
    unless (← existArgs args ["cartwheeldir", "confdir"]) do return 1
    runCheckDeg8 (need args "cartwheeldir") (need args "confdir")
  if args.has "check_7triangle" then
    unless (← existArgs args ["cartwheeldir", "confdir"]) do return 1
    runCheck7triangle (need args "cartwheeldir") (need args "confdir")
  if args.has "check_deg7" then
    unless (← existArgs args ["cartwheeldir", "confdir"]) do return 1
    runCheckDeg7 (need args "cartwheeldir") (need args "confdir")
  return 0
