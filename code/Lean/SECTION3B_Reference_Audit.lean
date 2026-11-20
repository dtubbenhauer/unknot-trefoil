import Trefoil.Section3LowerBound

/-!
Exact endpoint types and expanded references for Section 3B and the
combined Section 3 lower bound.
-/

open Trefoil.Section3ATopology in
open Trefoil.Section3BTopology in
example : ∀ {T : Geometry}, References T → FloerReferences T →
    3 ≤ T.unknotting (partner T 2) :=
  @section3B_lower_bound

open Trefoil.Section3ATopology in
open Trefoil.Section3BTopology in
example : ∀ {T : Geometry}, References T → FloerReferences T →
    3 ≤ T.unknotting (orientedPartner T 2) :=
  @section3B_oriented_lower_bound

open Trefoil.Section3BMinimum in
example : ∀ {h a s : ℤ}, ReducedAt 245 h a s →
    OwensMinimum 245 h a s (lensCorrection 245 104) →
    Trefoil.Finite.HasCorrectionComparison h a s :=
  @minimum_to_comparison

#print Trefoil.Section3BTopology.FloerReferences
#print Trefoil.Section3BMinimum.OwensMinimum
#print Trefoil.Section3BMinimum.ReducedAt
#print Trefoil.Section3BMinimum.spinBase
#print Trefoil.Section3BMinimum.lensCorrection
#print axioms Trefoil.Section3BMinimum.spinBase_245
#print axioms Trefoil.Section3BMinimum.lensCorrection_245
#print axioms Trefoil.Section3BMinimum.finiteLabel_double
#print axioms Trefoil.Section3BMinimum.surgeryMatrixZ_det
#print axioms Trefoil.Section3BMinimum.quadraticBound_translate
#print axioms Trefoil.Section3BMinimum.quadraticBound_translate_even
#print axioms Trefoil.Section3BMinimum.characteristic_iff_twice
#print axioms Trefoil.Section3BMinimum.doubled_characteristic_value
#print axioms Trefoil.Section3BMinimum.doubleClassesEquiv
#print axioms Trefoil.Section3BMinimum.OwensMinimum.changeCorrection
#print axioms Trefoil.Section3BMinimum.minimum_to_comparison
#print axioms Trefoil.Section3BMinimum.no_owens_minimum_245
#print axioms Trefoil.Section3BTopology.raw_spin_245
#print axioms Trefoil.Section3BTopology.oriented_correction_245
#print axioms Trefoil.Section3BTopology.section3B_oriented_lower_bound
#print axioms Trefoil.Section3BTopology.section3B_lower_bound

open Trefoil.Section3ATopology in
open Trefoil.Section3BTopology in
open Trefoil.Section3LowerBound in
example : ∀ {T : Geometry}, References T → FloerReferences T →
    ∀ {m : ℕ}, (m = 2 ∨ m = 4 ∨ 6 ≤ m) →
      3 ≤ T.unknotting (partner T m) :=
  @section3_lower_bound

#print axioms Trefoil.Section3LowerBound.section3_lower_bound
