-- core value types & helpers
import NearLinear4ct.OptIdx
import NearLinear4ct.SmallNatPair
import NearLinear4ct.Util
import NearLinear4ct.UtilProofs
import NearLinear4ct.Mapping
import NearLinear4ct.MappingProofs
import NearLinear4ct.Degree

-- combinatorial map
import NearLinear4ct.PseudoTriangulation

-- configuration with degrees
import NearLinear4ct.PseudoConfiguration

-- file-backed types
import NearLinear4ct.Configuration
-- graph well-formedness (after Configuration: proves `mirror` preserves WF)
import NearLinear4ct.PseudoTriangulationProofs
-- homomorphism BFS: structural well-formedness of `homCoreGo`'s output
import NearLinear4ct.HomomorphismProofs
import NearLinear4ct.Rule

-- the enumeration engine
import NearLinear4ct.Cartwheel
-- degree-gate sufficiency for the refinement subtraction
import NearLinear4ct.CartwheelProofs

-- verification drivers
import NearLinear4ct.CombineCartwheel

/-!
Lean 4 port of the near-linear 4CT computer checks.

A behaviour-preserving port of the C++ library in `computer-checks/src`. Built bottom-up;
modules are imported here in dependency order.
-/

