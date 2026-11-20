import Trefoil.Section3BTopology

/-!
# Unified Section 3 lower bound

Section 3A covers `m = 4` and `m ≥ 6`. Section 3B deals with `m = 2`.
This is the precise range of the paper's theorem. No values of `m` are
silently checked by finite computation or inferred by monotonicity.
-/

namespace Trefoil.Section3LowerBound

open Trefoil.Section3ATopology
open Trefoil.Section3BTopology

variable {T : Geometry}

/-- Unified reference-relative conclusion of Section 3. The new part
for `m=2` is obtained from the alternating Floer inputs; all other cases
invoke the previously kernel-checked Section 3A lattice obstruction. -/
theorem section3_lower_bound (R : References T) (F : FloerReferences T) {m : ℕ}
    (hm : m = 2 ∨ m = 4 ∨ 6 ≤ m) : 3 ≤ T.unknotting (partner T m) := by
  rcases hm with rfl | h
  · exact section3B_lower_bound R F
  · exact section3A_lower_bound R h

end Trefoil.Section3LowerBound
