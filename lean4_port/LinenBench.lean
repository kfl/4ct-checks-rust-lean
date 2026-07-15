import Linen

/-!
Microbenchmark for the Linen prototype. It compares the previous
one-`Task`-per-element implementation with the bounded worker implementation on
both scheduler-only and uneven-compute workloads.

Run with `lake exe linenBench`; use `LEAN_NUM_THREADS` and `LINEN_CHUNK_SIZE` to
probe scaling and claim granularity.
-/

def oldTaskMap (xs : Array α) (f : α → β) : Array β :=
  (xs.map (fun x => Task.spawn (fun _ => f x))).map (·.get)

@[noinline]
def mix : Nat → Nat → Nat
  | 0, acc => acc
  | fuel + 1, acc => mix fuel ((acc * 1664525 + 1013904223) % 4294967291)

/-- Mostly medium elements with regularly spaced expensive outliers, so static
partitioning leaves a tail while dynamic claims can rebalance. -/
@[noinline]
def unevenWork (i : Nat) : Nat :=
  mix (if i % 97 == 0 then 4000 else 200) (i + 1)

def timed (label : String) (run : Unit → Array Nat) : IO (Array Nat) := do
  let start ← IO.monoNanosNow
  let result := run ()
  let checksum := result.foldl (· ^^^ ·) 0
  let elapsed ← IO.monoNanosNow
  IO.println s!"{label}: {(elapsed - start) / 1000000} ms (checksum {checksum})"
  return result

def benchCase (label : String) (xs : Array Nat) (f : Nat → Nat) : IO Unit := do
  let old ← timed s!"{label}, task/element" fun _ => oldTaskMap xs f
  let linen ← timed s!"{label}, Linen" fun _ => Linen.map xs f
  unless old == linen do
    throw (IO.userError s!"{label}: implementations returned different results")

def main : IO UInt32 := do
  let config ← Linen.Config.fromEnv
  IO.println s!"Linen config: {repr config}"
  benchCase "scheduler" (Array.range 200000) (· + 1)
  benchCase "uneven" (Array.range 50000) unevenWork
  return 0
