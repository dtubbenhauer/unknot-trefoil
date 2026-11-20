import Trefoil.Arithmetic
import Mathlib.Algebra.Ring.Parity

/-!
# The signature calculation preceding Section 3A

The arithmetic and choice of signed continued fraction are specific to this
family. The reference inputs are the general Seifert-form realization by
plumbed twisted annuli and the signature rule for tridiagonal elimination.
-/

namespace Trefoil.Section3ASignature

open Trefoil.Arithmetic

/-- The negative continued fraction used for even `m`. -/
def evenWeights (m : ℕ) : List ℤ := [m, -2, 2, 2, 2, 2, 4, -2]

/-- The negative continued fraction used for odd `m`. -/
def oddWeights (m : ℕ) : List ℤ := [(m : ℤ) + 1, 2, 2, -4, 4, 2]

/-- Either sign of the homogeneous pair represents the same rational slope. -/
def MatchesFraction (weights : List ℤ) (p q : ℕ) : Prop :=
  minusPair weights = ((p : ℤ), (q : ℤ)) ∨
    minusPair weights = (-(p : ℤ), -(q : ℤ))

/-- General facts used to identify the signature of the two-bridge knot
whose oriented double branched cover is positive `p/q` surgery. The chain
signature uses the rational symmetric matrix with diagonal the listed
weights and off-diagonal entries `-1` at consecutive vertices. -/
structure SignatureReferences {Knot : Type*}
    (twoBridge : ℕ → ℕ → Knot) (signature : Knot → ℤ) where
  chainSignature : List ℤ → ℤ
  /-- An even linear plumbing realizes a symmetrized Seifert matrix of the
  corresponding oriented two-bridge knot. -/
  evenPlumbingSignature : ∀ (p q : ℕ) (weights : List ℤ),
    0 < q → q < p → Nat.Coprime p q → Odd p →
    (∀ w ∈ weights, Even w) → MatchesFraction weights p q →
    signature (twoBridge p q) = chainSignature weights
  /-- Sylvester's law of inertia applied to right-to-left elimination of
  the symmetric tridiagonal matrix when every pivot is nonzero. -/
  chainSignature_eq_signedPivotCount : ∀ (weights : List ℤ),
    (∀ pivot ∈ rightPivots (weights.map fun w => (w : ℚ)), pivot ≠ 0) →
    chainSignature weights = signedPivotCount (rightPivots
      (weights.map fun w => (w : ℚ)))

theorem evenWeights_fraction (m : ℕ) : MatchesFraction (evenWeights m) (104 * m + 37) 104 := by
  left
  simpa [evenWeights] using even_seifert_pair (m : ℤ)

theorem oddWeights_fraction (m : ℕ) : MatchesFraction (oddWeights m) (104 * m + 37) 104 := by
  right
  simpa [oddWeights] using odd_seifert_pair (m : ℤ)

theorem evenWeights_even (m : ℕ) (hm : Even m) : ∀ w ∈ evenWeights m, Even w := by
  have hEven : Even (m : ℤ) := by exact_mod_cast hm
  norm_num [evenWeights, hEven, show Even (4 : ℤ) by decide]

theorem oddWeights_even (m : ℕ) (hm : Odd m) : ∀ w ∈ oddWeights m, Even w := by
  have hEven : Even ((m : ℤ) + 1) := by exact_mod_cast hm.add_one
  norm_num [oddWeights, hEven, show Even (4 : ℤ) by decide]

/-- The manuscript's continued fractions and pivot counts imply signature
four for the chirality used in Owens's theorem. -/
theorem partner_signature_four {Knot : Type*} {twoBridge : ℕ → ℕ → Knot}
    {signature : Knot → ℤ} (ref : SignatureReferences twoBridge signature)
    (m : ℕ) (hm : 1 ≤ m) : signature (twoBridge (104 * m + 37) 104) = 4 := by
  have hq : 0 < (104 : ℕ) := by decide
  have hqp : 104 < 104 * m + 37 := by omega
  have hnonneg : 0 ≤ (m : ℚ) := by positivity
  rcases Nat.even_or_odd m with he | ho
  · rw [ref.evenPlumbingSignature _ _ _ hq hqp (determinant_coprime m)
      (determinant_odd m) (evenWeights_even m he) (evenWeights_fraction m)]
    rw [ref.chainSignature_eq_signedPivotCount _ (by
      simpa [evenWeights] using even_pivots_nonzero (m : ℚ) hnonneg)]
    simpa [evenWeights] using even_pivot_signature (m : ℚ) hnonneg
  · rw [ref.evenPlumbingSignature _ _ _ hq hqp (determinant_coprime m)
      (determinant_odd m) (oddWeights_even m ho) (oddWeights_fraction m)]
    rw [ref.chainSignature_eq_signedPivotCount _ (by
      simpa [oddWeights] using odd_pivots_nonzero (m : ℚ) hnonneg)]
    simpa [oddWeights] using odd_pivot_signature (m : ℚ) hnonneg

end Trefoil.Section3ASignature
