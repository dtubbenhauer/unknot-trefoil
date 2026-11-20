import experimental.Section3AExplicitHomology
import Trefoil.Section3ATopology

/-!
Check the exact reference-relative endpoint types and audit the three earlier
homology-level stages. The printed structures expose the geometric inputs.
-/

open Trefoil.Section3ATopology in
example : ∀ {T : Geometry}, References T → ∀ {m : ℕ},
    (m = 4 ∨ 6 ≤ m) → 3 ≤ T.unknotting (partner T m) :=
  @section3A_lower_bound

open Trefoil.Section3ATopology in
example : ∀ {T : Geometry}, References T → ∀ {m : ℕ},
    (m = 4 ∨ 6 ≤ m) → 3 ≤ T.unknotting (orientedPartner T m) :=
  @section3A_oriented_lower_bound

#print Trefoil.Section3ATopology.Geometry
#print Trefoil.Section3ATopology.Handlebody
#print Trefoil.Section3ATopology.Gluing
#print Trefoil.Section3ATopology.References
#print Trefoil.Section3ASignature.SignatureReferences
#print Trefoil.Section3ATopology.partner
#print Trefoil.Section3ATopology.orientedPartner

#print axioms Trefoil.Section3ATopology.section3A_lower_bound
#print axioms Trefoil.Section3ATopology.section3A_oriented_lower_bound
#print axioms Trefoil.Section3ATopology.two_negative_changes
#print axioms Trefoil.Section3ATopology.owens_filling
#print axioms Trefoil.Section3ATopology.explicit_plumbing
#print axioms Trefoil.Section3ATopology.lens_F2_vanish
#print axioms Trefoil.Section3ATopology.mv_F2_bijective
#print axioms Trefoil.Section3ATopology.integral_joint_exact
#print axioms Trefoil.Section3ATopology.integral_joint_index
#print axioms Trefoil.Section3ATopology.glue_positive
#print axioms Trefoil.Section3ATopology.no_two_change_gluing
#print axioms Trefoil.Section3APlumbing.plumbing_positiveDefinite
#print axioms Trefoil.Section3APlumbing.plumbing_det
#print axioms Trefoil.Section3APlumbing.joint_det
#print axioms Trefoil.Section3APlumbing.selectedIndex_injective
#print axioms Trefoil.Section3ACoefficients.reduced_columns_independent
#print axioms Trefoil.Section3ASignature.partner_signature_four
#print axioms Trefoil.LatticeExtraction.no_embedding
#print axioms Trefoil.RelativeTopology.lens_boundary_scalar
#print axioms Trefoil.RelativeTopology.lens_cellular_kernel_zero
#print axioms Trefoil.RelativeTopology.lens_cellular_boundary_surjective
#print axioms Trefoil.RelativeTopology.lensTwoCycles_eq_zero
#print axioms Trefoil.RelativeTopology.lensTwoCycles_subsingleton
#print axioms Trefoil.RelativeTopology.canonicalSelectedHandles_injective
#print axioms Trefoil.RelativeTopology.GluingData.inclusion_injective
#print axioms Trefoil.RelativeTopology.GluingData.selected_independent
#print axioms Trefoil.RelativeTopology.GluingData.toEmbedding
#print axioms Trefoil.RelativeTopology.no_gluing_data
#print axioms Trefoil.RelativeTopology.CanonicalGluingData.toGluingData
#print axioms Trefoil.RelativeTopology.no_canonical_gluing_data
#print axioms Trefoil.RelativeTopology.ManifoldHomologyData.boundarySubsingleton
#print axioms Trefoil.RelativeTopology.ManifoldHomologyData.toCanonical
#print axioms Trefoil.RelativeTopology.no_manifold_homology_data
#print Trefoil.RelativeTopology.ManifoldHomologyData
#print Trefoil.RelativeTopology.no_manifold_homology_data
