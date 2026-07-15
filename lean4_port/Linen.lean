import Init.System.IO

/-!
A small, dependency-free data-parallel executor for the port's `par*`
combinators.

Lean's task pool is a good fit for coarse tasks, but enqueueing one task for
every cartwheel candidate creates tens of millions of scheduler operations.
`Linen.mapM` instead starts a bounded team of workers. Workers repeatedly
claim a small chunk from an atomic cursor, so cheap and expensive
elements balance dynamically without becoming individual Lean `Task`s.

The worker count follows `LINEN_WORKERS`, then `LEAN_NUM_THREADS`, then the
machine's hardware concurrency. `LINEN_CHUNK_SIZE` controls the claim size and
defaults to one.
-/

namespace Linen

/-- Runtime settings for one parallel region. -/
structure Config where
  workers : Nat
  chunkSize : Nat
deriving Repr, DecidableEq

@[extern "lean_internal_get_hardware_concurrency"]
private opaque hardwareConcurrencyImpl (_ : Unit) : UInt32

/-- The same hardware-concurrency query used by Lean's executable shell.  The
fallback keeps interpreted evaluation serial; compiled executables use the
runtime query. -/
@[implemented_by hardwareConcurrencyImpl]
private def hardwareConcurrency (_ : Unit) : UInt32 := 1

private def positiveEnvNat (name : String) : BaseIO (Option Nat) := do
  let some value ← IO.getEnv name | return none
  let some n := value.toNat? | return none
  return if n == 0 then none else some n

/-- Read Linen's executor settings. Invalid and zero-valued overrides are
ignored, leaving at least one worker and one element per claim. -/
def Config.fromEnv : BaseIO Config := do
  let override ← positiveEnvNat "LINEN_WORKERS"
  let runtime ← positiveEnvNat "LEAN_NUM_THREADS"
  let workers := override.orElse fun _ => runtime
  let workers := workers.getD (hardwareConcurrency ()).toNat |>.max 1
  let chunkSize := (← positiveEnvNat "LINEN_CHUNK_SIZE").getD 1
  return { workers, chunkSize }

/-- Claim the next half-open chunk.  This is the executor's scheduling point:
workers that finish cheap chunks return here and take work from the common
remainder instead of becoming idle. -/
private def claim (cursor : IO.Ref Nat) (size chunkSize : Nat) :
    BaseIO (Option (Nat × Nat)) := do
  cursor.modifyGet fun next =>
    if next < size then
      let stop := (next + chunkSize).min size
      (some (next, stop), stop)
    else
      (none, next)

private partial def worker (cursor : IO.Ref Nat) (xs : Array α)
    (f : α → BaseIO β) (chunkSize : Nat) (initial : Array (Nat × β)) :
    BaseIO (Array (Nat × β)) := do
  let some (start, stop) ← claim cursor xs.size chunkSize | return initial
  let mut results := initial
  for i in [start:stop] do
    -- `claim` caps `stop` at `xs.size`; the optional read keeps this runtime
    -- implementation independent of an `Inhabited α` instance.
    if let some x := xs[i]? then
      results := results.push (i, ← f x)
  worker cursor xs f chunkSize results

/-- Bounded, dynamically balanced map engine.  At most one Lean task per
configured worker is created, regardless of `xs.size`; results are restored to
input order after all workers finish. -/
def mapM (xs : Array α) (f : α → BaseIO β) : BaseIO (Array β) := do
  let config ← Config.fromEnv
  if config.workers == 1 || xs.size ≤ config.chunkSize then
    xs.mapM f
  else
    let cursor ← IO.mkRef 0
    let chunks := (xs.size + config.chunkSize - 1) / config.chunkSize
    let workerCount := config.workers.min chunks
    let mut tasks : Array (Task (Array (Nat × β))) := Array.mkEmpty workerCount
    for _ in [0:workerCount] do
      tasks := tasks.push (← BaseIO.asTask (worker cursor xs f config.chunkSize #[]))
    let mut results := Array.replicate xs.size none
    for task in tasks do
      for (i, value) in (← IO.wait task) do
        results := results.set! i (some value)
    return results.filterMap id

/-- Runtime implementation of `map`. The public definition remains the
sequential specification, so theorem proving never has to model tasks, atomic
references, or scheduling. -/
private unsafe def mapImpl.{u, v} {α : Type u} {β : Type v}
    (xs : Array α) (f : α → β) : Array β :=
  -- `BaseIO`/`IO.Ref` store `Type 0`; the casts only erase universe
  -- bookkeeping. The runtime pointers pass through `f` and the result array
  -- unchanged, and the public sequential definition supplies the semantics.
  unsafeCast <| unsafeBaseIO <|
    mapM (unsafeCast xs : Array Unit) fun x =>
      pure ((unsafeCast f : Unit → Unit) x)

/-- Parallel `Array.map`, order-preserving and definitionally equal to the
sequential operation for reasoning. -/
@[implemented_by mapImpl]
def map.{u, v} {α : Type u} {β : Type v}
    (xs : Array α) (f : α → β) : Array β := xs.map f

/-- Parallel `Array.filterMap`, preserving input order. -/
def filterMap (xs : Array α) (f : α → Option β) : Array β :=
  (map xs f).filterMap id

/-- Parallel flat-map, preserving input and per-element output order. -/
def flatMap (xs : Array α) (f : α → Array β) : Array β :=
  (map xs f).flatten

/-- Parallel `IO` map. Every action runs before the first failure in input
order is re-raised. -/
def mapIO (xs : Array α) (f : α → IO β) : IO (Array β) := do
  let results ← mapM xs fun x => (f x).toBaseIO
  results.mapM IO.ofExcept

/-- Parallel `IO` traversal with ordered failure reporting. -/
def forEach (xs : Array α) (f : α → IO Unit) : IO Unit :=
  discard <| mapIO xs f

end Linen
