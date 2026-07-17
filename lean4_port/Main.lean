import NearLinear4ct

/-!
CLI entry point, in three layers: `parseOptions` (tokens → option/flag pairs,
rejecting unknown options and missing values), `buildJobs` (validate every
selected mode's arguments into a typed `Job` -- a constructed job is runnable
by construction), and `Job.run` (dispatch to the drivers). Modes are
independent, not mutually exclusive; all selected modes are validated before
any executes.

A failed proof obligation inside a `check_*` driver throws, which propagates
out of `main` and exits non-zero.
-/

open NearLinear4ct

/-- Parsed command line: present boolean flags + option/value pairs. -/
structure Options where
  flags : List String := []
  vals : List (String × String) := []

def Options.has (opts : Options) (flag : String) : Bool := opts.flags.contains flag
def Options.get? (opts : Options) (key : String) : Option String := opts.vals.lookup key

/-- Short → long option names. -/
def shortToLong : List (Char × String) :=
  [('C', "confdir"), ('R', "ruledir"), ('S', "combined_ruledir"),
   ('W', "cartwheeldir"), ('w', "wheel"), ('d', "degree"),
   ('o', "outdir"), ('H', "help")]

/-- Options that take a value. -/
def valuedOptions : List String :=
  ["confdir", "ruledir", "combined_ruledir", "cartwheeldir",
   "wheel", "degree", "outdir", "shard"]

/-- Boolean switches: the mode selectors and `help`. -/
def flagOptions : List String :=
  ["combine_rules", "enum_wheels", "enum_cartwheels",
   "check_deg8", "check_7triangle", "check_deg7", "help"]

/-- An option either takes a value or is a boolean switch. -/
inductive OptKind | valued | flag

/-- Bridge `Option` into `Except`: the value, or the given error. -/
def Option.orErr : Option α → String → Except String α
  | some a, _ => .ok a
  | none, msg => .error msg

def parseOptions (args : List String) : Except String Options := do
  let (opts, pending) ← args.foldlM step ({}, none)
  match pending with
  | some name => .error s!"missing value for --{name}"
  | none => .ok opts
where
  /-- One token's canonical long name plus its inline `=value`, if any. -/
  canon (tok : String) : Except String (String × Option String) :=
    if tok.startsWith "--" then
      let body := (tok.drop 2).toString
      match body.splitOn "=" with
      | [name] => .ok (name, none)
      | name :: val => .ok (name, some (String.intercalate "=" val))
      | [] => .error s!"unexpected argument {tok} (see --help)"
    else if tok.startsWith "-" && tok.length == 2 then
      return ((← (shortToLong.lookup (tok.toList.getLast!)).orErr
        s!"unknown option {tok} (see --help)"), none)
    else .error s!"unexpected argument {tok} (see --help)"
  /-- Which kind of option `name` is, or the unknown-option error. -/
  kind (name : String) : Except String OptKind :=
    (if valuedOptions.contains name then some .valued
     else if flagOptions.contains name then some .flag
     else none).orErr s!"unknown option --{name} (see --help)"
  /-- Fold step: the token is either the value for the pending valued option,
  or a new option. -/
  step : Options × Option String → String → Except String (Options × Option String)
    | (acc, some name), tok => .ok ({ acc with vals := (name, tok) :: acc.vals }, none)
    | (acc, none), tok => do
      let (name, inline?) ← canon tok
      match (← kind name), inline? with
      | .valued, some v => .ok ({ acc with vals := (name, v) :: acc.vals }, none)
      | .valued, none => .ok (acc, some name)
      | .flag, none => .ok ({ acc with flags := name :: acc.flags }, none)
      | .flag, some _ => .error s!"--{name} does not take a value"

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
  "  --shard arg               i/n: check_* only handles cartwheels k = i mod n\n" ++
  "  -H [ --help ]             Display options"

/-- The three checks share an argument shape. -/
inductive CheckKind | deg8 | triangle7 | deg7

/-- A fully validated unit of work: constructing a `Job` is the evidence that
its mode's arguments were present and well-formed. -/
inductive Job
  | help
  | combineRules (confdir ruledir outdir : System.FilePath)
  | enumWheels (degree : Nat) (confdir ruledir combinedRuledir outdir : System.FilePath)
  | enumCartwheels (wheel confdir ruledir combinedRuledir outdir : System.FilePath)
  | check (kind : CheckKind) (cartwheeldir confdir : System.FilePath)
      (shard : Option (Nat × Nat))

/-- A required option's value, or which one is missing for which mode. -/
def req (opts : Options) (mode name : String) : Except String String :=
  (opts.get? name).orErr s!"--{mode}: specify --{name}"

/-- A required `Nat` option (rejects malformed values rather than defaulting). -/
def reqNat (opts : Options) (mode name : String) : Except String Nat := do
  let s ← req opts mode name
  s.toNat?.orErr s!"--{mode}: --{name} expects a natural number, got '{s}'"

/-- `--shard i/n` (worker `i` of `n`, round-robin over the check's cartwheel
list); `none` when absent. -/
def shardArg (opts : Options) : Except String (Option (Nat × Nat)) := do
  let some s := opts.get? "shard" | return none
  let parsed : Option (Nat × Nat) := do
    let [i, n] := s.splitOn "/" | none
    return (← i.toNat?, ← n.toNat?)
  let (i, n) ← parsed.orErr s!"--shard {s}: expected i/n"
  unless i < n do throw s!"--shard {s}: need 0 <= i < n"
  return some (i, n)

/-- The shared builder of the three check jobs. -/
def checkJob (kind : CheckKind) (mode : String) (opts : Options) : Except String Job :=
  return .check kind (← req opts mode "cartwheeldir") (← req opts mode "confdir") (← shardArg opts)

/-- Mode flag → validated job builder (handed its own flag name), in the fixed
execution order. -/
def modes : List (String × (String → Options → Except String Job)) :=
  [("combine_rules", fun mode opts => do
      let r := req opts mode
      return .combineRules (← r "confdir") (← r "ruledir") (← r "outdir")),
   ("enum_wheels", fun mode opts => do
      let r := req opts mode
      return .enumWheels (← reqNat opts mode "degree") (← r "confdir") (← r "ruledir")
        (← r "combined_ruledir") (← r "outdir")),
   ("enum_cartwheels", fun mode opts => do
      let r := req opts mode
      return .enumCartwheels (← r "wheel") (← r "confdir") (← r "ruledir")
        (← r "combined_ruledir") (← r "outdir")),
   ("check_deg8", checkJob .deg8),
   ("check_7triangle", checkJob .triangle7),
   ("check_deg7", checkJob .deg7)]

/-- Validate each selected mode into a `Job`; everything is validated before
anything runs. -/
def buildJobs (opts : Options) : Except String (List Job) :=
  if opts.has "help" then .ok [.help]
  else match modes.filter (fun (name, _) => opts.has name) with
  | [] => .error "no mode selected (see --help)"
  | selected => selected.mapM fun (name, build) => build name opts

def Job.run : Job → IO Unit
  | .help => IO.println helpText
  | .combineRules confdir ruledir outdir => runCombineRules confdir ruledir outdir
  | .enumWheels degree confdir ruledir combinedRuledir outdir =>
      runEnumWheels degree confdir ruledir combinedRuledir outdir
  | .enumCartwheels wheel confdir ruledir combinedRuledir outdir =>
      runEnumCartwheels wheel confdir ruledir combinedRuledir outdir
  | .check .deg8 cartwheeldir confdir shard => runCheckDeg8 cartwheeldir confdir shard
  | .check .triangle7 cartwheeldir confdir shard => runCheck7triangle cartwheeldir confdir shard
  | .check .deg7 cartwheeldir confdir shard => runCheckDeg7 cartwheeldir confdir shard

def main (argv : List String) : IO UInt32 := do
  match parseOptions argv >>= buildJobs with
  | .error msg => IO.eprintln msg; return 1
  | .ok jobs => jobs.forM Job.run; return 0
