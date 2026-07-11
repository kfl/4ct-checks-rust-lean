import NearLinear4ct.OptIdx

/-!
Vertex- and dart-index maps.

`Mappings { vmap, dmap }` carries vertex- and dart-index maps and supports
composition. Free functions `composeMap` / `splitMap` go here too.

Index / sentinel representation (the crate-wide decision): an index map
entry is an `OptIdx`, where `none` is the C++ `-1` ("unmapped"). `homomorphism`
returns *partial* maps, so the type must admit "no image". `OptIdx` is the
**verified-sound** compact form of `Option Nat` (see `OptIdx.lean`): it reads in
`none`/`some` terms (turning the C++ `== -1` into `OptIdx.isNone`) but is stored
unboxed (`Array OptIdx` is a dense scalar array, where `Array (Option Nat)` would
box every `some` -- Lean has no niche optimisation). The `OptIdx ≃ Option Nat`
bijection is machine-checked, so this is as trustworthy as `Option` and faster.
-/

namespace NearLinear4ct

/-- A vertex- or dart-index map. `OptIdx.none` == the C++ `-1` (unmapped). -/
abbrev IndexMap := Array OptIdx

/-- Vertex map + dart map produced by (free) homomorphisms. -/
structure Mappings where
  vmap : IndexMap
  dmap : IndexMap
deriving Repr, Inhabited, DecidableEq

/-- Compose two index maps: `result[i] = map2[map1[i]]`.

`none` propagates: if `map1[i]` is unmapped, so is the result. Total inputs map
every entry; on a partial input the unmapped entry stays `none`. -/
def composeMap (map1 map2 : IndexMap) : IndexMap :=
  map1.map (fun j => if j.isNone then OptIdx.none else map2[j.idx!]!)

/-- Split an index map at `l` into `(map[:l], map[l:])`.

The `0 <= l && l <= size` bound is a defensive precondition, not a proof
obligation; `Array.extract` clamps safely, so we keep it implicit. -/
def splitMap (map : IndexMap) (l : Nat) : IndexMap × IndexMap :=
  (map.extract 0 l, map.extract l map.size)

namespace Mappings

/-- Identity maps on `n` vertices and `dartSize` darts. -/
def initialMappings (n dartSize : Nat) : Mappings :=
  { vmap := (Array.range n).map OptIdx.some
  , dmap := (Array.range dartSize).map OptIdx.some }

/-- `self` followed by `other`: `result[i] = other[self[i]]`. -/
def compose (self other : Mappings) : Mappings :=
  { vmap := composeMap self.vmap other.vmap
  , dmap := composeMap self.dmap other.dmap }

end Mappings
end NearLinear4ct
