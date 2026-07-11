-- Phase 1: leaf types
import NearLinear4ct.OptIdx
import NearLinear4ct.SmallNatPair
import NearLinear4ct.Util
import NearLinear4ct.UtilProofs
import NearLinear4ct.Mapping
import NearLinear4ct.MappingProofs
import NearLinear4ct.Degree

-- Phase 2: combinatorial map
import NearLinear4ct.PseudoTriangulation

-- Phase 3: configuration with degrees
import NearLinear4ct.PseudoConfiguration

-- Phase 4: file-backed types
import NearLinear4ct.Configuration
-- graph well-formedness (after Configuration: proves `mirror` preserves WF)
import NearLinear4ct.PseudoTriangulationProofs
-- homomorphism BFS: structural well-formedness of `homCoreGo`'s output
import NearLinear4ct.HomomorphismProofs
import NearLinear4ct.Rule

-- Phase 5: the enumeration engine
import NearLinear4ct.Cartwheel
-- degree-gate sufficiency for the refinement subtraction
import NearLinear4ct.CartwheelProofs

-- Phase 6: verification drivers
import NearLinear4ct.CombineCartwheel

/-!
Lean 4 port of the near-linear 4CT computer checks.

A behaviour-preserving port of the C++ library in `../src`, mirroring the Rust
port in `../rust_port`. Built bottom-up; modules are imported here in dependency
order and filled in phase by phase. See `PORTING_PLAN.md` for the phases, the
carried-over decisions (R1–R7), and the Lean-specific risk register (L1–L8).
-/

