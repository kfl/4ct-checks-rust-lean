import NearLinear4ct

/-!
Test executable for the Lean port — the analogue of `cargo test` / the C++
googletests. A tiny `expect` harness counts failures and exits non-zero if any
fire (so `lake exe test` is a usable CI gate). Each `expect` cites the C++ test
it mirrors where one exists.
-/


open NearLinear4ct

abbrev Counter := IO.Ref Nat

def expect (c : Counter) (name : String) (cond : Bool) : IO Unit := do
  if cond then
    IO.println s!"ok   - {name}"
  else
    IO.eprintln s!"FAIL - {name}"
    c.modify (· + 1)

/-- Degree ordering (lexicographic by lower then upper) plus the range
predicates (intersection / disjoint / includes). -/
def degreeTests (c : Counter) : IO Unit := do
  let d1 := Degree.mk 5 6
  let d2 := Degree.mk 5 6
  let d3 := Degree.mk 5 7
  let d4 := Degree.mk 6 7
  expect c "degree d1 == d2" (d1 == d2)
  expect c "degree d1 < d3" (d1 < d3)
  expect c "degree d1 < d4" (d1 < d4)
  expect c "degree d3 > d1" (d3 > d1)
  expect c "degree d4 > d1" (d4 > d1)
  -- fixed / exact
  expect c "degree exact is fixed" (Degree.exact 7).fixed
  expect c "degree range not fixed" (!(Degree.mk 5 6).fixed)
  expect c "degree exact = mk x x" (Degree.exact 7 == Degree.mk 7 7)
  -- intersection / disjoint / includes
  let a := Degree.mk 5 8
  let b := Degree.mk 7 9
  let e := Degree.mk 10 11
  expect c "degree has_intersection a b" (Degree.hasIntersection a b)
  expect c "degree not disjoint a b" (!Degree.disjoint a b)
  expect c "degree intersection a b = [7,8]" (Degree.intersection a b == Degree.mk 7 8)
  expect c "degree disjoint a e" (Degree.disjoint a e)
  let empty := Degree.intersection a e
  expect c "degree empty intersection lower>upper" (decide (empty.lower > empty.upper))
  expect c "degree includes [5,9] [6,8]" (Degree.includes (Degree.mk 5 9) (Degree.mk 6 8))
  expect c "degree not includes [6,8] [5,9]" (!Degree.includes (Degree.mk 6 8) (Degree.mk 5 9))

def im (xs : List Nat) : IndexMap := (xs.map OptIdx.some).toArray

def mappingTests (c : Counter) : IO Unit := do
  -- initial_mappings is the identity
  let id3 := Mappings.initialMappings 3 4
  expect c "initial vmap = id" (id3.vmap == im [0, 1, 2])
  expect c "initial dmap = id" (id3.dmap == im [0, 1, 2, 3])
  -- compose: result[i] = map2[map1[i]]
  expect c "compose_map semantics"
    (composeMap (im [2, 0, 1]) (im [10, 11, 12]) == im [12, 10, 11])
  -- compose with identity is a no-op
  let idm := Mappings.initialMappings 3 3
  let am := Mappings.mk (im [1, 2, 0]) (im [2, 1, 0])
  expect c "compose a id = a" (am.compose idm == am)
  expect c "compose id a = a" (idm.compose am == am)
  -- none propagates
  expect c "compose propagates none"
    (composeMap #[OptIdx.some 0, OptIdx.none, OptIdx.some 1] (im [7, 8])
      == #[OptIdx.some 7, OptIdx.none, OptIdx.some 8])
  -- split
  let (l, r) := splitMap (im [0, 1, 2, 3, 4]) 2
  expect c "split left" (l == im [0, 1])
  expect c "split right" (r == im [2, 3, 4])

def utilTests (c : Counter) : IO Unit := do
  -- Unionfind: unite attaches root(x) under root(y)
  let uf := Unionfind.new 5
  expect c "uf fresh num_roots = 5" (uf.numRoots == 5)
  let uf := uf.unite 0 1
  let uf := uf.unite 3 4
  expect c "uf same 0 1" (uf.same 0 1)
  expect c "uf not same 0 2" (!uf.same 0 2)
  expect c "uf same 3 4" (uf.same 3 4)
  expect c "uf num_roots = 3" (uf.numRoots == 3)
  expect c "uf all_roots = [1,2,4]" (uf.allRoots == #[1, 2, 4])
  expect c "uf each_root = [1,1,2,4,4]" (uf.eachRoot == #[1, 1, 2, 4, 4])
  expect c "uf index_roots"
    (uf.indexRoots == #[OptIdx.none, OptIdx.some 0, OptIdx.some 1, OptIdx.none, OptIdx.some 2])
  -- relabel composes to a total map (the disjoint_union pattern)
  let uf2 := (Unionfind.new 4).unite 0 2
  let each : IndexMap := uf2.eachRoot.map OptIdx.some
  let relabel := composeMap each uf2.indexRoots
  expect c "uf relabel total" (relabel.all (·.isSome))
  expect c "uf relabel size" (relabel.size == 4)
  -- Bool analogue of `Unionfind.RootsWF` (`UtilProofs.lean`): every
  -- representative lands in range, on a root.
  let rootsWF (u : Unionfind) : Bool :=
    (List.range u.n).all fun i =>
      decide (u.root i < u.n) && u.parents[u.root i]!.isNone
  expect c "uf RootsWF check" (rootsWF uf)
  expect c "uf RootsWF check (relabel fixture)" (rootsWF uf2)
  -- lexMin (specified against `List.rotateLeft` by
  -- `lexMin_iff_forall_rotateLeft` in `UtilProofs.lean`)
  expect c "lexMin [1,2,3]" (lexMin [1, 2, 3])
  expect c "lexMin not [2,3,1]" (!lexMin [2, 3, 1])
  expect c "lexMin not [3,1,2]" (!lexMin [3, 1, 2])
  expect c "lexMin [1,1,2]" (lexMin [1, 1, 2])
  expect c "lexMin empty" (lexMin ([] : List Nat))
  expect c "lexMin single" (lexMin [5])

/-- Build a `Dart` from the C++ test's `int` quad, mapping `-1` -> `none`. -/
def dt (head rev : Nat) (succ pred : Int) : Dart :=
  let o : Int → OptIdx := fun x => if x == -1 then OptIdx.none else OptIdx.some x.toNat
  ⟨head, rev, o succ, o pred⟩

/-- fromVRotations builds the dart structure from clockwise vertex rotations;
freeHomomorphismPair glues two triangulations, returning the quotient and each
input's index maps onto it. -/
def ptTests (c : Counter) : IO Unit := do
  let rotation : Array (Array Int) := #[#[1, 2, -1], #[2, 0, -1], #[0, 1, -1]]
  -- FromVRotation
  let pt := PseudoTriangulation.fromVRotations 3 rotation
  let expected := PseudoTriangulation.mk 3 #[
    dt 0 3 1 (-1), dt 0 4 (-1) 0, dt 1 5 3 (-1),
    dt 1 0 (-1) 2, dt 2 1 5 (-1), dt 2 2 (-1) 4]
  expect c "pt FromVRotation" (pt == expected)
  expect c "pt FromVRotation wfCheck" pt.wfCheck
  -- Identify: glue (0,1) and (2,1)
  let pt0 := PseudoTriangulation.fromVRotations 3 rotation
  let pt1 := PseudoTriangulation.fromVRotations 3 rotation
  let (ptI, m0, m1) := PseudoTriangulation.freeHomomorphismPair pt0 pt1 0 5
  let expectedI := PseudoTriangulation.mk 4 #[
    dt 3 2 (-1) 9, dt 2 3 6 (-1), dt 0 0 3 (-1), dt 0 1 (-1) 2,
    dt 1 7 5 (-1), dt 1 8 (-1) 4, dt 2 9 7 1, dt 2 4 (-1) 6,
    dt 3 5 9 (-1), dt 3 6 0 8]
  expect c "pt Identify vmap0" (m0.vmap == im [3, 2, 0])
  expect c "pt Identify vmap1" (m1.vmap == im [1, 2, 3])
  expect c "pt Identify dmap0" (m0.dmap == im [9, 0, 1, 6, 2, 3])
  expect c "pt Identify dmap1" (m1.dmap == im [4, 5, 6, 7, 8, 9])
  expect c "pt Identify structure" (ptI == expectedI)
  expect c "pt Identify wfCheck" ptI.wfCheck
  -- Identify2: 5-wheel+1 with 7-wheel+1, glue (1,5) and (1,7)
  let pt0b := PseudoTriangulation.fromVRotations 7 #[
    #[1, 2, 3, 4, 5], #[2, 0, 5, -1], #[3, 0, 1, -1], #[4, 0, 2, -1],
    #[6, 5, 0, 3, -1], #[1, 0, 4, 6, -1], #[5, 4, -1]]
  let pt1b := PseudoTriangulation.fromVRotations 9 #[
    #[1, 2, 3, 4, 5, 6, 7], #[8, 2, 0, 7, -1], #[3, 0, 1, 8, -1], #[4, 0, 2, -1],
    #[5, 0, 3, -1], #[6, 0, 4, -1], #[7, 0, 5, -1], #[1, 0, 6, -1], #[2, 1, -1]]
  let (ptI2, _, _) := PseudoTriangulation.freeHomomorphismPair pt0b pt1b 7 10
  let expectedI2 := PseudoTriangulation.mk 3 #[
    dt 1 1 4 (-1), dt 2 0 (-1) 7, dt 0 5 2 2, dt 1 7 (-1) 6,
    dt 1 6 5 0, dt 1 2 6 4, dt 1 4 3 5, dt 2 3 1 (-1)]
  expect c "pt Identify2 structure" (ptI2 == expectedI2)

/-- Terse aliases for the `Degree` constructors used across the fixtures. -/
abbrev dg := Degree.mk
abbrev dgx := Degree.exact

/-- freeHomomorphismPair (gluing), resolveDegreeIssues (splitting an unfixed
centre-degree range into its concrete completions), and homomorphism (the
degree-compatible embedding search). The containment/charge cases need derived
types and live in `cartwheelTests`. -/
def pcTests (c : Counter) : IO Unit := do
  -- Identify1: identify (2,1) and (2,0)
  let rot3 : Array (Array Int) := #[#[1, 2, -1], #[2, 0, -1], #[0, 1, -1]]
  let degs3 := #[dg 5 6, dg 6 7, dgx 7]
  let pc0 := PseudoConfiguration.fromVRotations 3 rot3 degs3
  let pc1 := PseudoConfiguration.fromVRotations 3 rot3 degs3
  let pcs := PseudoConfiguration.freeHomomorphismPair pc0 pc1 5 4
  expect c "pc Identify1 size" (pcs.size == 1)
  let (pcR, m0, m1) := pcs[0]!
  let exp1 := PseudoConfiguration.new 4 #[
    dt 0 2 1 (-1), dt 0 3 (-1) 0, dt 1 0 (-1) 5, dt 3 1 8 (-1), dt 1 7 5 (-1),
    dt 1 8 2 4, dt 2 9 7 (-1), dt 2 4 (-1) 6, dt 3 5 9 3, dt 3 6 (-1) 8]
    #[dg 5 6, dgx 6, dg 6 7, dgx 7]
  expect c "pc Identify1 structure" (pcR == exp1)
  expect c "pc Identify1 wfCheck" pcR.wfCheck
  expect c "pc Identify1 vmap0" (m0.vmap == im [0, 1, 3])
  expect c "pc Identify1 dmap0" (m0.dmap == im [0, 1, 5, 2, 3, 8])
  expect c "pc Identify1 vmap1" (m1.vmap == im [1, 2, 3])
  expect c "pc Identify1 dmap1" (m1.dmap == im [4, 5, 6, 7, 8, 9])

  -- resolveDegreeIssues1: degree-8 center splits into 3
  let r1 : Array (Array Int) := #[
    #[1, 2, 3, 4, 5, 6, -1], #[2, 0, -1], #[3, 0, 1, -1], #[4, 0, 2, -1],
    #[5, 0, 3, -1], #[6, 0, 4, -1], #[0, 5, -1]]
  let d1 := #[dg 5 8, dgx 6, dgx 6, dgx 6, dgx 6, dgx 6, dgx 6]
  let rdi1 := (PseudoConfiguration.fromVRotations 7 r1 d1).resolveDegreeIssues
  expect c "pc rdi1 size" (rdi1.size == 3)
  let e0 := PseudoConfiguration.new 6 #[
    dt 0 7 1 4, dt 0 10 2 0, dt 0 13 3 1, dt 0 16 4 2, dt 0 18 0 3, dt 5 8 18 (-1),
    dt 1 11 7 (-1), dt 1 0 8 6, dt 1 5 (-1) 7, dt 2 14 10 (-1), dt 2 1 11 9,
    dt 2 6 (-1) 10, dt 3 17 13 (-1), dt 3 2 14 12, dt 3 9 (-1) 13, dt 4 19 16 (-1),
    dt 4 3 17 15, dt 4 12 (-1) 16, dt 5 4 19 5, dt 5 15 (-1) 18]
    #[dgx 5, dgx 6, dgx 6, dgx 6, dgx 6, dgx 6]
  let e1 := PseudoConfiguration.new 7 #[
    dt 0 7 1 (-1), dt 0 9 2 0, dt 0 12 3 1, dt 0 15 4 2, dt 0 18 5 3, dt 0 20 (-1) 4,
    dt 1 10 7 (-1), dt 1 0 (-1) 6, dt 2 13 9 (-1), dt 2 1 10 8, dt 2 6 (-1) 9,
    dt 3 16 12 (-1), dt 3 2 13 11, dt 3 8 (-1) 12, dt 4 19 15 (-1), dt 4 3 16 14,
    dt 4 11 (-1) 15, dt 5 21 18 (-1), dt 5 4 19 17, dt 5 14 (-1) 18, dt 6 5 21 (-1),
    dt 6 17 (-1) 20]
    #[dg 7 8, dgx 6, dgx 6, dgx 6, dgx 6, dgx 6, dgx 6]
  let e2 := PseudoConfiguration.new 7 #[
    dt 0 7 1 5, dt 0 9 2 0, dt 0 12 3 1, dt 0 15 4 2, dt 0 18 5 3, dt 0 20 0 4,
    dt 1 10 7 (-1), dt 1 0 22 6, dt 2 13 9 (-1), dt 2 1 10 8, dt 2 6 (-1) 9,
    dt 3 16 12 (-1), dt 3 2 13 11, dt 3 8 (-1) 12, dt 4 19 15 (-1), dt 4 3 16 14,
    dt 4 11 (-1) 15, dt 5 21 18 (-1), dt 5 4 19 17, dt 5 14 (-1) 18, dt 6 5 21 23,
    dt 6 17 (-1) 20, dt 1 23 (-1) 7, dt 6 22 20 (-1)]
    #[dgx 6, dgx 6, dgx 6, dgx 6, dgx 6, dgx 6, dgx 6]
  expect c "pc rdi1 [0]" (rdi1[0]!.1 == e0)
  expect c "pc rdi1 [1]" (rdi1[1]!.1 == e1)
  expect c "pc rdi1 [2]" (rdi1[2]!.1 == e2)
  expect c "pc rdi1 vmap0" (rdi1[0]!.2.vmap == im [0, 5, 1, 2, 3, 4, 5])
  expect c "pc rdi1 dmap0"
    (rdi1[0]!.2.dmap == im [4, 0, 1, 2, 3, 4, 5, 18, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19])
  expect c "pc rdi1 vmap1" (rdi1[1]!.2.vmap == im [0, 1, 2, 3, 4, 5, 6])
  expect c "pc rdi1 dmap1" (rdi1[1]!.2.dmap == im (List.range 22))
  expect c "pc rdi1 vmap2" (rdi1[2]!.2.vmap == im [0, 1, 2, 3, 4, 5, 6])
  expect c "pc rdi1 dmap2" (rdi1[2]!.2.dmap == im (List.range 22))

  -- resolveDegreeIssues2
  let r2 : Array (Array Int) := #[
    #[1, 2, 3, 4, 5, 6], #[2, 0, 6, -1], #[3, 0, 1, -1], #[4, 0, 2, -1],
    #[5, 0, 3, -1], #[6, 0, 4, -1], #[1, 0, 5, -1]]
  let d2 := #[dg 5 8, dgx 5, dgx 5, dgx 5, dgx 5, dgx 5, dgx 5]
  let rdi2 := (PseudoConfiguration.fromVRotations 7 r2 d2).resolveDegreeIssues
  expect c "pc rdi2 size" (rdi2.size == 1)
  let e2b := PseudoConfiguration.new 7 #[
    dt 0 7 1 5, dt 0 10 2 0, dt 0 13 3 1, dt 0 16 4 2, dt 0 19 5 3, dt 0 22 0 4,
    dt 1 11 7 (-1), dt 1 0 8 6, dt 1 21 (-1) 7, dt 2 14 10 (-1), dt 2 1 11 9,
    dt 2 6 (-1) 10, dt 3 17 13 (-1), dt 3 2 14 12, dt 3 9 (-1) 13, dt 4 20 16 (-1),
    dt 4 3 17 15, dt 4 12 (-1) 16, dt 5 23 19 (-1), dt 5 4 20 18, dt 5 15 (-1) 19,
    dt 6 8 22 (-1), dt 6 5 23 21, dt 6 18 (-1) 22]
    #[dgx 6, dgx 5, dgx 5, dgx 5, dgx 5, dgx 5, dgx 5]
  expect c "pc rdi2 [0]" (rdi2[0]!.1 == e2b)
  expect c "pc rdi2 vmap" (rdi2[0]!.2.vmap == im [0, 1, 2, 3, 4, 5, 6])
  expect c "pc rdi2 dmap" (rdi2[0]!.2.dmap == im (List.range 24))

  -- resolveDegreeIssues3: icosahedral graph
  let r3 : Array (Array Int) := #[
    #[1, 3, 8, 7, 2, -1], #[2, 5, 4, 3, 0, -1], #[0, 7, 6, 5, 1, -1],
    #[0, 1, 4, 9, 8], #[1, 5, 10, 9, 3], #[1, 2, 6, 10, 4],
    #[2, 7, 11, 10, 5], #[2, 0, 8, 11, 6], #[0, 3, 9, 11, 7],
    #[3, 4, 10, 11, 8], #[4, 5, 6, 11, 9], #[6, 7, 8, 9, 10]]
  let d3 := Array.replicate 12 (dgx 5)
  let rdi3 := (PseudoConfiguration.fromVRotations 12 r3 d3).resolveDegreeIssues
  expect c "pc rdi3 size" (rdi3.size == 1)
  let e3 := PseudoConfiguration.new 12 #[
    dt 0 8 1 4, dt 0 13 2 0, dt 0 38 3 1, dt 0 34 4 2, dt 0 9 0 3, dt 1 23 6 58,
    dt 1 18 7 5, dt 1 14 8 6, dt 1 0 58 7, dt 2 4 10 59, dt 2 33 11 9, dt 2 28 12 10,
    dt 2 24 59 11, dt 3 1 14 17, dt 3 7 15 13, dt 3 22 16 14, dt 3 43 17 15,
    dt 3 39 13 16, dt 4 6 19 22, dt 4 27 20 18, dt 4 48 21 19, dt 4 44 22 20,
    dt 4 15 18 21, dt 5 5 24 27, dt 5 12 25 23, dt 5 32 26 24, dt 5 49 27 25,
    dt 5 19 23 26, dt 6 11 29 32, dt 6 37 30 28, dt 6 53 31 29, dt 6 50 32 30,
    dt 6 25 28 31, dt 7 10 34 37, dt 7 3 35 33, dt 7 42 36 34, dt 7 54 37 35,
    dt 7 29 33 36, dt 8 2 39 42, dt 8 17 40 38, dt 8 47 41 39, dt 8 55 42 40,
    dt 8 35 38 41, dt 9 16 44 47, dt 9 21 45 43, dt 9 52 46 44, dt 9 56 47 45,
    dt 9 40 43 46, dt 10 20 49 52, dt 10 26 50 48, dt 10 31 51 49, dt 10 57 52 50,
    dt 10 45 48 51, dt 11 30 54 57, dt 11 36 55 53, dt 11 41 56 54, dt 11 46 57 55,
    dt 11 51 53 56, dt 1 59 5 8, dt 2 58 9 12]
    (Array.replicate 12 (dgx 5))
  expect c "pc rdi3 icosahedral" (rdi3[0]!.1 == e3)
  expect c "pc rdi3 wfCheck" (rdi3[0]!.1.wfCheck)

  -- Identify2: 6-vertex + 10-vertex, identify (4,5) and (3,2)
  let pc0b := PseudoConfiguration.fromVRotations 6 #[
    #[1, 2, 3, 4, 5], #[2, 0, 5, -1], #[3, 0, 1, -1], #[4, 0, 2, -1],
    #[5, 0, 3, -1], #[1, 0, 4, -1]]
    #[dgx 5, dgx 5, dgx 5, dgx 5, dgx 6, dgx 5]
  let pc1b := PseudoConfiguration.fromVRotations 10 #[
    #[1, 2, 9, -1], #[2, 0, -1], #[3, 9, 0, 1, -1], #[4, 7, 8, 9, 2, -1], #[5, 6, 7, 3, -1],
    #[6, 4, -1], #[7, 4, 5, -1], #[8, 3, 4, 6, -1], #[9, 3, 7, -1], #[0, 2, 3, 8, -1]]
    #[dgx 6, dgx 5, dgx 5, dgx 6, dgx 5, dgx 5, dgx 6, dgx 6, dgx 6, dgx 6]
  let pcs2 := PseudoConfiguration.freeHomomorphismPair pc0b pc1b 14 13
  expect c "pc Identify2 size" (pcs2.size == 1)
  let (pcR2, n0, n1) := pcs2[0]!
  let exp2 := PseudoConfiguration.new 11 #[
    dt 0 6 1 4, dt 0 8 2 0, dt 0 11 3 1, dt 0 13 4 2, dt 0 15 0 3, dt 4 9 6 (-1),
    dt 4 0 19 5, dt 1 12 8 31, dt 1 1 9 7, dt 1 5 (-1) 8, dt 2 14 11 30, dt 2 2 12 10,
    dt 2 7 29 11, dt 6 3 14 28, dt 6 10 25 13, dt 5 4 21 24, dt 3 20 17 (-1),
    dt 3 23 18 16, dt 3 42 (-1) 17, dt 4 24 20 6, dt 4 16 (-1) 19, dt 5 28 22 15,
    dt 5 43 23 21, dt 5 17 24 22, dt 5 19 15 23, dt 6 36 26 14, dt 6 40 27 25,
    dt 6 44 28 26, dt 6 21 13 27, dt 2 33 30 12, dt 2 37 10 29, dt 1 34 7 (-1),
    dt 7 38 33 (-1), dt 7 29 34 32, dt 7 31 (-1) 33, dt 8 41 36 (-1), dt 8 25 37 35,
    dt 8 30 38 36, dt 8 32 (-1) 37, dt 9 45 40 (-1), dt 9 26 41 39, dt 9 35 (-1) 40,
    dt 10 18 43 (-1), dt 10 22 44 42, dt 10 27 45 43, dt 10 39 (-1) 44]
    #[dgx 5, dgx 5, dgx 5, dgx 6, dgx 5, dgx 5, dgx 6, dgx 6, dgx 6, dgx 6, dgx 6]
  expect c "pc Identify2 structure" (pcR2 == exp2)
  expect c "pc Identify2 vmap0" (n0.vmap == im [0, 4, 1, 2, 6, 5])
  expect c "pc Identify2 vmap1" (n1.vmap == im [3, 4, 5, 6, 2, 1, 7, 8, 9, 10])
  expect c "pc Identify2 dmap0"
    (n0.dmap == im [0, 1, 2, 3, 4, 5, 6, 19, 7, 8, 9, 10, 11, 12, 28, 13, 14, 24, 15, 21])
  expect c "pc Identify2 dmap1"
    (n1.dmap == im [16, 17, 18, 19, 20, 21, 22, 23, 24, 14, 25, 26, 27, 28, 12, 29, 30, 10, 31, 7,
                    32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45])

  -- findHomomorphism
  let fh0 := PseudoConfiguration.fromVRotations 5
    #[#[1, 2, 3, 4, -1], #[2, 0, -1], #[3, 0, 1, -1], #[4, 0, 2, -1], #[0, 3, -1]]
    #[dgx 6, dgx 5, dgx 6, dgx 6, dgx 5]
  let fh1 := PseudoConfiguration.fromVRotations 7
    #[#[1, 2, 3, 4, 5, 6], #[2, 0, 6, -1], #[3, 0, 1, -1], #[4, 0, 2, -1],
      #[5, 0, 3, -1], #[6, 0, 4, -1], #[1, 0, 5, -1]]
    #[dgx 6, dg 5 INFTY, dgx 6, dgx 6, dgx 5, dgx 6, dgx 6]
  expect c "pc findHom (0,1)->(0,1)"
    (PseudoConfiguration.homomorphism fh0 0 fh1 0 Degree.hasIntersection).isSome
  expect c "pc findHom (0,1)->(6,1) none"
    (PseudoConfiguration.homomorphism fh0 0 fh1 8 Degree.hasIntersection).isNone

/-- Write `content` to a freshly-created temp file (secure, race-free, unique
name in the system temp dir, via `IO.FS.createTempFile`) and return its path. The
caller removes it; prefer `IO.FS.withTempFile` where RAII cleanup fits (`mkRule`). -/
def tempFile (content : String) : IO System.FilePath := do
  let (_, path) ← IO.FS.createTempFile
  IO.FS.writeFile path content
  return path

-- On-disk fixtures in the FORMAT.md text encoding.
def conf1 : String := "\n17 10\n11 5 1 12 17 9 10\n12 5 1 2 13 17 11\n13 6 2 14 16 7 17 12\n14 5 2 3 15 16 13\n15 5 3 4 5 16 14\n16 6 5 6 7 13 14 15\n17 6 7 8 9 11 12 13\n"
def conf2 : String := "\n11 7\n8 5 1 2 9 11 7\n9 6 2 3 4 10 11 8\n10 5 4 5 6 11 9\n11 5 6 7 8 9 10\n"
def rule1 : String := "\n2 1 2 2\n1 5 5 2 -1\n2 5 0 1 -1\n"
def rule2 : String := "\n6 1 2 1\n1 7 7 5 4 3 2 6 -1\n2 7 0 1 3 -1 6\n3 5 5 2 1 4 -1\n4 5 6 3 1 5 -1\n5 5 5 4 1 -1\n6 5 5 1 2 -1\n"
def rule3 : String := "\n6 1 2 1\n1 7 7 4 6 2 3 -1\n2 7 0 3 1 6 -1\n3 5 5 1 2 -1\n4 6 6 5 6 1 -1\n5 5 5 6 4 -1\n6 5 5 2 1 4 5 -1\n"
def rule4 : String := "\n8 1 2 1\n1 7 7 3 4 2 6 -1\n2 7 7 7 6 1 4 5 -1\n3 5 5 4 1 -1\n4 7 7 5 2 1 3 -1\n5 6 0 2 4 -1\n6 5 5 1 2 7 8 -1\n7 6 6 8 6 2 -1\n8 7 0 6 7 -1\n"
def cw1str : String := "8 1\n1 7 7 2 3 4 5 6 7 8\n2 5 5 3 1 8 -1\n3 5 5 4 1 2 -1\n4 6 6 5 1 3 -1\n5 5 5 6 1 4 -1\n6 5 5 7 1 5 -1\n7 5 5 8 1 6 -1\n8 9 9 2 1 7 -1\n"

/-- Load a `Rule` from a fixture string via a temporary file (auto-removed). -/
def mkRule (content : String) : IO Rule :=
  IO.FS.withTempFile fun _ path => do
    IO.FS.writeFile path content
    (FromFile.fromFile path : IO Rule)

def exA (xs : List Nat) : Array Degree := (xs.map dgx).toArray

/-- Set several vertices to exact degrees (test helper). -/
def setDeg (cw : CartWheel) (mods : List (Nat × Nat)) : CartWheel := Id.run do
  let mut c := cw
  for (v, d) in mods do
    c := { c with degrees := c.degrees.set! v (dgx d) }
  return c

/-- Cartwheel FromFile / enumWheels / charge / pruning / refinement /
enumBadCartwheels, plus the containment and charge-amount cases that need the
CartWheel type. -/
def cartwheelTests (c : Counter) : IO Unit := do
  -- FromFile (cw1 full structure; cw2 structural — too large to transcribe)
  let cw1 := CartWheel.ofString cw1str
  let cw1exp := CartWheel.new 0 #[0, 1, 2, 3, 4, 5, 6] 8 #[
    dt 0 8 1 6, dt 0 11 2 0, dt 0 14 3 1, dt 0 17 4 2, dt 0 20 5 3, dt 0 23 6 4,
    dt 0 26 0 5, dt 1 12 8 (-1), dt 1 0 9 7, dt 1 25 (-1) 8, dt 2 15 11 (-1),
    dt 2 1 12 10, dt 2 7 (-1) 11, dt 3 18 14 (-1), dt 3 2 15 13, dt 3 10 (-1) 14,
    dt 4 21 17 (-1), dt 4 3 18 16, dt 4 13 (-1) 17, dt 5 24 20 (-1), dt 5 4 21 19,
    dt 5 16 (-1) 20, dt 6 27 23 (-1), dt 6 5 24 22, dt 6 19 (-1) 23, dt 7 9 26 (-1),
    dt 7 6 27 25, dt 7 22 (-1) 26] (exA [7, 5, 5, 6, 5, 5, 5, 9])
  expect c "cw1 FromFile" (cw1 == cw1exp)

  -- EnumWheels counts (Burnside) — the P5 gate
  expect c "enumWheels 5 = 629" ((CartWheel.enumWheels 5).size == 629)
  expect c "enumWheels 6 = 2635" ((CartWheel.enumWheels 6).size == 2635)
  expect c "enumWheels 7 = 11165" ((CartWheel.enumWheels 7).size == 11165)

  -- charge (sum over center darts)
  let rules3 := #[(← mkRule rule1), (← mkRule rule2), (← mkRule rule3)]
  let chWheels := #[
    (CartWheel.generateCartwheel 7 #[5, 7, 5, 5, 9, 5, 6], (1, 8)),
    (CartWheel.generateCartwheel 7 #[5, 5, 7, 5, 7, 5, 7], (0, 8))]
  for (wheel, expOut, expIn) in chWheels do
    let mut outCharge : Int := 0
    let mut inCharge : Int := 0
    for dartId in wheel.centerDarts do
      inCharge := inCharge + wheel.toPseudoConfiguration.amountOfChargeSend dartId rules3
      let rev := (wheel.darts[dartId]!).rev
      outCharge := outCharge + wheel.toPseudoConfiguration.amountOfChargeSend rev rules3
    expect c s!"charge out={expOut}" (outCharge == expOut)
    expect c s!"charge in={expIn}" (inCharge == expIn)

  -- AmountChargeSend (specific dart ids)
  let acsCw := setDeg (CartWheel.generateCartwheel 7 #[5, 5, 5, 5, 7, 5, 7]) [(8, 6), (18, 5)]
  let acsP := acsCw.toPseudoConfiguration
  expect c "amountChargeSend 28" (acsP.amountOfChargeSend 28 rules3 == 1)
  expect c "amountChargeSend 41" (acsP.amountOfChargeSend 41 rules3 == 0)
  expect c "amountChargeSend 23" (acsP.amountOfChargeSend 23 rules3 == 0)
  expect c "amountChargeSend 6" (acsP.amountOfChargeSend 6 rules3 == 1)
  expect c "amountChargeSend 0" (acsP.amountOfChargeSend 0 rules3 == 2)

  -- AmountPossibleChargeSend
  let combined3 := combineRules rules3 #[]
  let apcsCw := setDeg (CartWheel.generateCartwheel 8 #[5, 7, 5, 7, 5, 9, 9, 9]) [(13, 6), (14, 7)]
  let apcsP := apcsCw.toPseudoConfiguration
  expect c "amountPossibleChargeSend 1" (apcsP.amountOfPossibleChargeSend 1 combined3 == 1)
  expect c "amountPossibleChargeSend 2" (apcsP.amountOfPossibleChargeSend 2 combined3 == 2)
  expect c "amountPossibleChargeSend 3" (apcsP.amountOfPossibleChargeSend 3 combined3 == 2)

  -- PruneByCharge
  let pcWheel0 := CartWheel.generateCartwheel 7 #[7, 5, 7, 5, 7, 5, 5]
  let spokes1 := #[combined3[0]!, combined3[1]!]
  expect c "prune nonassoc false" (!pcWheel0.pruneByNonAssociatedRule spokes1 rules3)
  expect c "prune ubc > 0" (decide (pcWheel0.upperBoundOfCharge spokes1 rules3 combined3 > 0))
  let pcWheel := setDeg pcWheel0 [(10, 5), (11, 6), (12, 5)]
  let spokes2 := #[combined3[4]!, combined3[1]!]
  expect c "prune2 nonassoc false" (!pcWheel.pruneByNonAssociatedRule spokes2 rules3)
  expect c "prune2 ubc > 0" (decide (pcWheel.upperBoundOfCharge spokes2 rules3 combined3 > 0))

  -- refinement1 / refinement2
  let rule4v ← mkRule rule4
  let refCw := setDeg (CartWheel.generateCartwheel 7 #[7, 7, 5, 5, 9, 6, 5]) [(14, 6)]
  expect c "refinement1 shouldRefine" (refCw.shouldRefine 1 rule4v)
  let refinements := refCw.refinement 1 rule4v
  expect c "refinement1 count 4" (refinements.size == 4)
  let withMods (mods : List (Nat × Degree)) : CartWheel := Id.run do
    let mut x := refCw
    for (v, deg) in mods do
      x := { x with degrees := x.degrees.set! v deg }
    return x
  let refExp := #[
    withMods [(11, dgx 5)], withMods [(15, dgx 5)], withMods [(15, dgx 6)],
    withMods [(11, dg 6 9), (15, dg 7 9)]]
  expect c "refinement1 structures" (refinements == refExp)
  let refCw2 := CartWheel.generateCartwheel 7 #[7, 7, 5, 5, 9, 6, 5]
  expect c "refinement2 not shouldRefine" (!refCw2.shouldRefine 1 rule4v)

  -- enumBadCartwheels1
  let rules4 := #[(← mkRule rule1), (← mkRule rule2),
                 (← mkRule rule3), (← mkRule rule4)]
  let combined4 := combineRules rules4 #[]
  let ebCw := CartWheel.generateCartwheel 7 #[5, 7, 5, 7, 5, 8, 9]
  let enumerated ← ebCw.enumBadCartwheels rules4 combined4 #[]
  let ebExp := setDeg ebCw [(11, 5), (12, 6), (13, 5), (15, 5), (16, 6), (17, 5)]
  expect c "enumBadCartwheels1 count 1" (enumerated.size == 1)
  expect c "enumBadCartwheels1 structure" (enumerated[0]! == ebExp)

  -- enumBadCartwheels2
  let eb2Cw := CartWheel.generateCartwheel 7 #[5, 5, 5, 7, 7, 5, 7]
  let enum1 ← eb2Cw.enumBadCartwheels rules4 combined4 #[]
  let eb2Exp1 := setDeg eb2Cw [(8, 6), (9, 5), (20, 5)]
  expect c "enumBadCartwheels2a count 1" (enum1.size == 1)
  expect c "enumBadCartwheels2a structure" (enum1[0]! == eb2Exp1)
  let eb2Cw' := setDeg eb2Cw [(17, 6)]
  let enum2 ← eb2Cw'.enumBadCartwheels rules4 combined4 #[]
  let base2 := setDeg eb2Exp1 [(17, 6)]
  let eb2Exp2 := #[setDeg base2 [(14, 5)], setDeg base2 [(18, 5)], setDeg base2 [(18, 6)]]
  expect c "enumBadCartwheels2b structures" (enum2 == eb2Exp2)

  -- Contain1 / Contain2 (need conf files)
  let cf1 ← tempFile conf1
  let confs1 ← Configuration.fromFile cf1
  IO.FS.removeFile cf1
  let ctnCw := setDeg (CartWheel.generateCartwheel 7 #[6, 6, 6, 6, 6, 6, 6]) [(9, 5), (10, 5), (12, 5), (13, 5)]
  expect c "Contain1" (ctnCw.toPseudoConfiguration.blockedByReducibleConfiguration ctnCw.center confs1)
  let cf2 ← tempFile conf2
  let confs2 ← Configuration.fromFile cf2
  IO.FS.removeFile cf2
  let ctn2Cw := setDeg (CartWheel.generateCartwheel 7 #[5, 6, 6, 6, 6, 6, 5]) [(8, 6)]
  expect c "Contain2 not blocked"
    (!ctn2Cw.toPseudoConfiguration.blockedByReducibleConfiguration ctn2Cw.center confs2)
  let ctn2Cw' := setDeg ctn2Cw [(9, 5)]
  expect c "Contain2 blocked"
    (ctn2Cw'.toPseudoConfiguration.blockedByReducibleConfiguration ctn2Cw'.center confs2)

/-- fromFile parses a .conf into configurations (cut-vertices expanded, each
paired with its mirror). -/
def configTests (c : Counter) : IO Unit := do
  let f1 ← tempFile conf1
  let f2 ← tempFile conf2
  let confs1 ← Configuration.fromFile f1
  let confs2 ← Configuration.fromFile f2
  IO.FS.removeFile f1; IO.FS.removeFile f2
  let deg8 := #[dg 4 INFTY, dgx 5, dgx 5, dgx 6, dgx 5, dgx 5, dgx 6, dgx 6]
  let e0 := Configuration.new 9 8 #[
    dt 0 22 1 (-1), dt 0 10 2 0, dt 0 18 (-1) 1, dt 1 7 4 (-1), dt 1 23 (-1) 3,
    dt 2 12 6 (-1), dt 2 24 7 5, dt 2 3 (-1) 6, dt 3 15 9 (-1), dt 3 19 10 8,
    dt 3 1 11 9, dt 3 25 12 10, dt 3 5 (-1) 11, dt 4 17 14 (-1), dt 4 20 15 13,
    dt 4 8 (-1) 14, dt 5 21 17 (-1), dt 5 13 (-1) 16, dt 6 2 19 (-1), dt 6 9 20 18,
    dt 6 14 21 19, dt 6 16 (-1) 20, dt 7 0 (-1) 25, dt 7 4 24 (-1), dt 7 6 25 23,
    dt 7 11 22 24] deg8
  let e1 := Configuration.new 11 8 #[
    dt 0 14 1 (-1), dt 0 9 2 0, dt 0 5 (-1) 1, dt 1 8 4 (-1), dt 1 23 (-1) 3,
    dt 2 2 6 (-1), dt 2 13 7 5, dt 2 24 8 6, dt 2 3 (-1) 7, dt 3 1 10 13,
    dt 3 17 11 9, dt 3 20 (-1) 10, dt 3 25 13 (-1), dt 3 6 9 12, dt 4 0 (-1) 17,
    dt 4 19 16 (-1), dt 4 21 17 15, dt 4 10 14 16, dt 5 22 19 (-1), dt 5 15 (-1) 18,
    dt 6 11 21 (-1), dt 6 16 22 20, dt 6 18 (-1) 21, dt 7 4 24 (-1), dt 7 7 25 23,
    dt 7 12 (-1) 24] deg8
  let e2 := Configuration.new 9 8 #[
    dt 0 22 (-1) 1, dt 0 10 0 2, dt 0 18 1 (-1), dt 1 7 (-1) 4, dt 1 23 3 (-1),
    dt 2 12 (-1) 6, dt 2 24 5 7, dt 2 3 6 (-1), dt 3 15 (-1) 9, dt 3 19 8 10,
    dt 3 1 9 11, dt 3 25 10 12, dt 3 5 11 (-1), dt 4 17 (-1) 14, dt 4 20 13 15,
    dt 4 8 14 (-1), dt 5 21 (-1) 17, dt 5 13 16 (-1), dt 6 2 (-1) 19, dt 6 9 18 20,
    dt 6 14 19 21, dt 6 16 20 (-1), dt 7 0 25 (-1), dt 7 4 (-1) 24, dt 7 6 23 25,
    dt 7 11 24 22] deg8
  let e3 := Configuration.new 11 8 #[
    dt 0 14 (-1) 1, dt 0 9 0 2, dt 0 5 1 (-1), dt 1 8 (-1) 4, dt 1 23 3 (-1),
    dt 2 2 (-1) 6, dt 2 13 5 7, dt 2 24 6 8, dt 2 3 7 (-1), dt 3 1 13 10,
    dt 3 17 9 11, dt 3 20 10 (-1), dt 3 25 (-1) 13, dt 3 6 12 9, dt 4 0 17 (-1),
    dt 4 19 (-1) 16, dt 4 21 15 17, dt 4 10 16 14, dt 5 22 (-1) 19, dt 5 15 18 (-1),
    dt 6 11 (-1) 21, dt 6 16 20 22, dt 6 18 21 (-1), dt 7 4 (-1) 24, dt 7 7 23 25,
    dt 7 12 24 (-1)] deg8
  expect c "conf1 size" (confs1.size == 4)
  expect c "conf1[0]" (confs1[0]! == e0)
  expect c "conf1[1]" (confs1[1]! == e1)
  expect c "conf1[2]" (confs1[2]! == e2)
  expect c "conf1[3]" (confs1[3]! == e3)
  let deg4 := #[dgx 5, dgx 6, dgx 5, dgx 5]
  let c2e0 := Configuration.new 2 4 #[
    dt 0 4 1 (-1), dt 0 7 (-1) 0, dt 1 6 3 (-1), dt 1 8 4 2, dt 1 0 (-1) 3,
    dt 2 9 6 (-1), dt 2 2 (-1) 5, dt 3 1 8 (-1), dt 3 3 9 7, dt 3 5 (-1) 8] deg4
  let c2e1 := Configuration.new 2 4 #[
    dt 0 4 (-1) 1, dt 0 7 0 (-1), dt 1 6 (-1) 3, dt 1 8 2 4, dt 1 0 3 (-1),
    dt 2 9 (-1) 6, dt 2 2 5 (-1), dt 3 1 (-1) 8, dt 3 3 7 9, dt 3 5 8 (-1)] deg4
  expect c "conf2 size" (confs2.size == 2)
  expect c "conf2[0]" (confs2[0]! == c2e0)
  expect c "conf2[1]" (confs2[1]! == c2e1)

/-- Rule parsing, byte-exact + idempotent write, and combineRules. -/
def ruleTests (c : Counter) : IO Unit := do
  let f1 ← tempFile rule1
  let f2 ← tempFile rule2
  let f3 ← tempFile rule3
  let r1 ← (FromFile.fromFile f1 : IO Rule)
  let r2 ← (FromFile.fromFile f2 : IO Rule)
  let r3 ← (FromFile.fromFile f3 : IO Rule)
  IO.FS.removeFile f1; IO.FS.removeFile f2; IO.FS.removeFile f3
  let r1exp := Rule.new 1 2 2 #[dt 0 1 (-1) (-1), dt 1 0 (-1) (-1)] #[dgx 5, dg 5 INFTY]
  let r2exp := Rule.new 5 1 6 #[
    dt 0 15 1 (-1), dt 0 12 2 0, dt 0 9 3 1, dt 0 5 4 2, dt 0 16 (-1) 3,
    dt 1 3 6 7, dt 1 8 (-1) 5, dt 1 17 5 (-1), dt 2 6 9 (-1), dt 2 2 10 8,
    dt 2 11 (-1) 9, dt 3 10 12 (-1), dt 3 1 13 11, dt 3 14 (-1) 12, dt 4 13 15 (-1),
    dt 4 0 (-1) 14, dt 5 4 17 (-1), dt 5 7 (-1) 16]
    #[dgx 7, dg 7 INFTY, dgx 5, dg 5 6, dgx 5, dgx 5]
  expect c "rule1 read" (r1 == r1exp)
  expect c "rule2 read" (r2 == r2exp)
  -- R7: write is byte-exact (trailing space after each vertex line)
  expect c "rule1 write byte-exact" (r1.write == "\n2 1 2 2\n1 5 5 2 -1 \n2 5 0 1 -1 \n")
  -- R7: write is idempotent
  for (tag, content) in [("rt1", rule1), ("rt2", rule2), ("rt3", rule3)] do
    let fa ← tempFile content
    let w1 := (← (FromFile.fromFile fa : IO Rule)).write
    IO.FS.removeFile fa
    let fb ← tempFile w1
    let w2 := (← (FromFile.fromFile fb : IO Rule)).write
    IO.FS.removeFile fb
    expect c s!"rule write idempotent {tag}" (w1 == w2)
  -- CombineRules
  let combined := combineRules #[r1, r2, r3] #[]
  expect c "combineRules size" (combined.size == 5)
  let c0 := CombinedRule.new #[false, false, false] 0 0 2
    #[dt 0 1 (-1) (-1), dt 1 0 (-1) (-1)] #[dg 1 INFTY, dg 1 INFTY]
  let c1 := CombinedRule.new #[true, false, false] 1 2 2
    #[dt 0 1 (-1) (-1), dt 1 0 (-1) (-1)] #[dgx 5, dg 5 INFTY]
  let c2 := CombinedRule.new #[false, true, false] 5 1 6 #[
    dt 0 15 1 (-1), dt 0 12 2 0, dt 0 9 3 1, dt 0 5 4 2, dt 0 16 (-1) 3,
    dt 1 3 6 7, dt 1 8 (-1) 5, dt 1 17 5 (-1), dt 2 6 9 (-1), dt 2 2 10 8,
    dt 2 11 (-1) 9, dt 3 10 12 (-1), dt 3 1 13 11, dt 3 14 (-1) 12, dt 4 13 15 (-1),
    dt 4 0 (-1) 14, dt 5 4 17 (-1), dt 5 7 (-1) 16]
    #[dgx 7, dg 7 INFTY, dgx 5, dg 5 6, dgx 5, dgx 5]
  let c3 := CombinedRule.new #[false, false, true] 5 1 6 #[
    dt 0 11 1 (-1), dt 0 15 2 0, dt 0 5 3 1, dt 0 7 (-1) 2, dt 1 8 5 (-1),
    dt 1 2 6 4, dt 1 14 (-1) 5, dt 2 3 8 (-1), dt 2 4 (-1) 7, dt 3 13 10 (-1),
    dt 3 16 11 9, dt 3 0 (-1) 10, dt 4 17 13 (-1), dt 4 9 (-1) 12, dt 5 6 15 (-1),
    dt 5 1 16 14, dt 5 10 17 15, dt 5 12 (-1) 16]
    #[dgx 7, dg 7 INFTY, dgx 5, dgx 6, dgx 5, dgx 5]
  let c4 := CombinedRule.new #[false, true, true] 9 2 7 #[
    dt 1 3 4 (-1), dt 4 2 (-1) 15, dt 0 1 3 (-1), dt 0 0 (-1) 2, dt 1 15 5 0,
    dt 1 19 6 4, dt 1 9 7 5, dt 1 11 (-1) 6, dt 2 12 9 (-1), dt 2 6 10 8,
    dt 2 18 (-1) 9, dt 3 7 12 (-1), dt 3 8 (-1) 11, dt 4 17 14 (-1), dt 4 20 15 13,
    dt 4 4 1 14, dt 5 21 17 (-1), dt 5 13 (-1) 16, dt 6 10 19 (-1), dt 6 5 20 18,
    dt 6 14 21 19, dt 6 16 (-1) 20]
    #[dgx 5, dgx 7, dg 7 INFTY, dgx 5, dgx 6, dgx 5, dgx 5]
  expect c "combined[0]" (combined[0]! == c0)
  expect c "combined[1]" (combined[1]! == c1)
  expect c "combined[2]" (combined[2]! == c2)
  expect c "combined[3]" (combined[3]! == c3)
  expect c "combined[4]" (combined[4]! == c4)

/-- Sanity checks for `CombineCartwheel` (get7triangle / getX / deleteDegree);
its full validation is the differential run. -/
def combineCartwheelTests (c : Counter) : IO Unit := do
  let t := get7triangle
  expect c "get7triangle n=3" (t.n == 3)
  expect c "get7triangle dartId=0" (t.dartId == 0)
  expect c "get7triangle all deg 7" (t.degrees.all (· == dgx 7))
  let x := getX
  expect c "getX n=17" (x.n == 17)
  expect c "getX deg0=8" (x.degrees[0]! == dgx 8)
  expect c "getX anyDart 0" (x.anyDart 0).isSome
  -- delete_degree: a fixed degree-9 vertex is removed; otherwise kept
  let cw := CartWheel.generateCartwheel 7 #[5, 5, 5, 5, 5, 5, 5]
  expect c "deleteDegree keeps" ((deleteDegreeFromKTo9 #[cw] 9).size == 1)
  let cw9 := setDeg cw [(8, 9)]
  expect c "deleteDegree removes fixed-9" ((deleteDegreeFromKTo9 #[cw9] 9).isEmpty)

/-- A trivial `FromFile` payload to exercise `getObjects` (R3 sorted load). -/
structure Line where
  s : String
deriving DecidableEq, Repr

instance : FromFile Line where
  fromFile p := do return { s := (← IO.FS.readFile p).trimAscii.toString }

def getObjectsTest (c : Counter) : IO Unit :=
  IO.FS.withTempDir fun dir => do
    -- created out of order, with a non-matching extension mixed in
    IO.FS.writeFile (dir / "b.rule") "B"
    IO.FS.writeFile (dir / "a.rule") "A"
    IO.FS.writeFile (dir / "c.other") "C"
    let objs ← getObjects Line dir ".rule"
    expect c "getObjects sorted + filtered"
      (objs.map (·.s) == #["A", "B"])

-- The Degree algebra laws are proved universally as theorems in
-- `NearLinear4ct/Degree.lean` (stronger than the finite grid they replaced).

def main : IO UInt32 := do
  let c ← IO.mkRef 0
  degreeTests c
  mappingTests c
  utilTests c
  ptTests c
  pcTests c
  configTests c
  ruleTests c
  cartwheelTests c
  combineCartwheelTests c
  getObjectsTest c
  let failures ← c.get
  if failures == 0 then
    IO.println "all tests passed"
    return 0
  else
    IO.eprintln s!"{failures} test(s) failed"
    return 1
