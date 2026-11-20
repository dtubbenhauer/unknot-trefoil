import Trefoil.Arithmetic
import Trefoil.FiniteObstruction
import Trefoil.LatticeExtraction

/-!
# Explicit conditional assembly

This file records short deductions after the relevant geometric transfers.
The transfer hypotheses below are NOT described as literature inputs. They
include unfinished identifications belonging to this paper. In particular,
these theorems do not claim a complete formalization of unknotting number.
-/

namespace Trefoil.Consequences

/-- Section 3B after the external theory and knot/cover interpretation have
produced the precise surgery-form comparison. The implication is deliberately
visible; it is not an axiom and is not discharged in this checkpoint. -/
theorem lower_bound_245 (u : ℕ) (hu : 2 ≤ u)
    (realize : u = 2 → ∃ h a s : ℤ,
      Finite.ReducedForm h a s ∧ Finite.HasCorrectionComparison h a s) :
    3 ≤ u := by
  by_contra hn
  have heq : u = 2 := by omega
  obtain ⟨h, a, s, hf, hc⟩ := realize heq
  exact Finite.no_reduced_correction_comparison hf hc

/-- Section 3A after the topological construction of the integral embedding.
The signed-coordinate normalization and parity step are proved internally. -/
theorem lower_bound_lattice (m u : ℕ) (hm : m = 4 ∨ 6 ≤ m)
    (hu : 2 ≤ u)
    (realize : u = 2 → Nonempty (LatticeEmbedding.Embedding m)) :
    3 ≤ u := by
  by_contra hn
  have heq : u = 2 := by omega
  obtain ⟨embedding⟩ := realize heq
  exact LatticeExtraction.no_embedding hm embedding

/-- Once the two substantive bounds are proved, the partner has number three. -/
theorem exact_three_of_bounds (u : ℕ) (hl : 3 ≤ u) (hu : u ≤ 3) : u = 3 := by
  omega

/-- The strict inequality in the main theorem, with all premises displayed. -/
theorem strict_saving (uT uP uSum : ℕ)
    (ht : uT = 1) (hp : uP = 3) (hs : uSum ≤ 3) :
    uSum < uT + uP := by omega

/-- The arithmetic at the end of the positive trefoil-plumbing argument. -/
theorem plumbing_saving (g uP uSum : ℕ)
    (hg : 1 ≤ g) (hp : uP = 3) (hs : uSum ≤ (g - 1) + 3) :
    uSum ≤ g + 2 ∧ uSum < g + uP := by omega

/-- Distinct determinant values distinguish family members once the
determinant formula for the actual knot family has been established. -/
theorem family_injective {K : Type*} (partner : ℕ → K) (determinant : K → ℕ)
    (hdet : ∀ m, determinant (partner m) = 104 * m + 37) :
    Function.Injective partner := by
  intro m n h
  have hd := congrArg determinant h
  rw [hdet m, hdet n] at hd
  exact Arithmetic.determinant_injective hd

end Trefoil.Consequences
