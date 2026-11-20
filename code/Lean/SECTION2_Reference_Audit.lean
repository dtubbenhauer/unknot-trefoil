import Trefoil.Section2Certificate
import Trefoil.Section2InitialExterior
import Trefoil.Section2Pachner
import Trefoil.Section2ReferenceTangle

/-! The checked endpoint types and explicit geometry and reference inputs for Section 2. -/

open Trefoil.Section2Topology Trefoil.Section2Certificate Trefoil.Section2DiagramData

example : ∀ {K : KnotGeometry}, KnotReferences K → ∀ m : ℕ,
    K.unknotting (partner K m) ≤ 3 :=
  @partner_upper_bound

example : ∀ {K : KnotGeometry} {A : AugmentedGeometry K} {I : DiagramGeometry A},
    KnotReferences K → FillingReferences A → DiagramReferences I →
    ExteriorBridges I → I.knot trefoilModel = K.trefoil → ∀ m : ℕ,
      K.unknotting (K.connectedSum K.trefoil (partner K m)) ≤ 3 :=
  @family_upper_bound

example : ∀ {K : KnotGeometry} {A : AugmentedGeometry K} {I : DiagramGeometry A},
    KnotReferences K → DiagramReferences I → SeedExteriorBridges I →
    I.knot trefoilModel = K.trefoil →
    Changes K.switch 3 (K.connectedSum K.trefoil (K.mirror (I.knot seedTable))) K.unknot :=
  @seed_movie

example : ∀ {K : KnotGeometry} {A : AugmentedGeometry K} {I : DiagramGeometry A},
    KnotReferences K → DiagramReferences I → SeedExteriorBridges I →
      partner K 2 = K.mirror (I.knot seedTable) :=
  @seed_partner_is_table

#print KnotGeometry
#print KnotReferences
#print AugmentedGeometry
#print FillingReferences
#print DiagramGeometry
#print DiagramReferences
#print ExteriorBridges
#print SeedExteriorBridges
#print Trefoil.Section2InitialExterior.SignedPD
#print partner

#print axioms Trefoil.Section2Topology.partner_upper_bound
#print axioms Trefoil.Section2Topology.filled_movie
#print axioms Trefoil.Section2Topology.connected_sum_upper_bound
#print axioms Trefoil.Section2Certificate.family_upper_bound
#print axioms Trefoil.Section2Certificate.seed_movie
#print axioms Trefoil.Section2Certificate.seed_reference_agrees
#print axioms Trefoil.Section2Certificate.seed_partner_is_table
#print axioms Trefoil.Section2Certificate.exterior_identification
#print axioms Trefoil.Section2Certificate.diagram_to_raw
#print axioms Trefoil.Section2Certificate.reference_chart
#print axioms Trefoil.Section2Arithmetic.partner_three_local_switches
#print axioms Trefoil.Section2Arithmetic.changedPartnerBoxes_infinity
#print axioms Trefoil.Section2DiagramMoves.CertifiedMoves.sound
#print axioms Trefoil.Section2DiagramMoves.CertifiedMoves.markedSound
#print axioms Trefoil.Section2DiagramMoves.CertifiedMoves.knotSound
#print axioms Trefoil.Section2DiagramMoves.CertifiedMoves.markedPlanarSound
#print axioms Trefoil.Section2InitialExterior.checkSnapshot_of_tables
#print axioms Trefoil.Section2Pachner.checkMarkedMove_sound
#print axioms Trefoil.Section2Pachner.checkMove_sound
#print axioms Trefoil.Section2ReferenceTangle.evenReference_constructor
#print axioms Trefoil.Section2ReferenceTangle.oddReference_constructor
#print axioms Trefoil.Section2ReferenceTangle.seedReference_constructor
#print axioms Trefoil.Section2ReferenceTangle.seedReference_constructor_domain
#print axioms Trefoil.Section2TriangulationData.data_checked
#print axioms Trefoil.Section2TriangulationData.data_slopes
