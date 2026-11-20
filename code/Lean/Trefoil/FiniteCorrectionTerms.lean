import Trefoil.FiniteForms
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Tactic.Ring

/-!
# Kernel-checked correction-term witnesses

The stored integer table is not a trusted numerical input: `scaled_correction_spec`
checks every entry against the rational Ozsváth–Szabó recursion in Lean's kernel.
The witnesses below strengthen the manuscript's finite calculation: they work
without constructing the cokernel isomorphism or restricting to unit multipliers.
-/

namespace Trefoil.Finite

/-- The recursion for d(-L(p,q),i). On the coprime Euclidean chains used here,
`q = 0` occurs only at `(p,q) = (1,0)`. -/
def correctionTerm (p q i : ℕ) : ℚ :=
  if hq : q = 0 then 0 else
    ((p : ℚ) * q - (2 * (i : ℚ) + 1 - p - q) ^ 2) / (4 * p * q) -
      correctionTerm q (p % q) (i % q)
termination_by q
decreasing_by exact Nat.mod_lt _ (Nat.pos_of_ne_zero hq)

/-- Spin-centered labels for Y = -L(245,141) = L(245,104). -/
def dY (j : Fin 245) : ℚ := correctionTerm 245 141 ((70 + j.val) % 245)

/-- Clearing the seven fixed denominators in the Euclidean recursion. -/
def commonNumerator (j : Fin 245) : ℤ :=
  let i₀ : ℕ := (70 + j.val) % 245
  let i₁ : ℕ := i₀ % 141
  let i₂ : ℕ := i₁ % 104
  let i₃ : ℕ := i₂ % 37
  let i₄ : ℕ := i₃ % 30
  let i₅ : ℕ := i₄ % 7
  let i₆ : ℕ := i₅ % 2
  3848 * (34545 - (2 * (i₀ : ℤ) - 385) ^ 2) -
  9065 * (14664 - (2 * (i₁ : ℤ) - 244) ^ 2) +
  34545 * (3848 - (2 * (i₂ : ℤ) - 140) ^ 2) -
  119756 * (1110 - (2 * (i₃ : ℤ) - 66) ^ 2) +
  632996 * (210 - (2 * (i₄ : ℤ) - 36) ^ 2) -
  9494940 * (14 - (2 * (i₅ : ℤ) - 8) ^ 2) +
  66464580 * (2 - (2 * (i₆ : ℤ) - 2) ^ 2)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
/-- The closed expression is derived from the recursion, not assumed. -/
theorem dY_common_denominator (j : Fin 245) :
    dY j = (commonNumerator j : ℚ) / 531716640 := by
  unfold dY
  rw [correctionTerm]
  simp only [Nat.reduceMod, Nat.reduceEqDiff, ↓reduceDIte]
  rw [correctionTerm]
  simp only [Nat.reduceMod, Nat.reduceEqDiff, ↓reduceDIte]
  rw [correctionTerm]
  simp only [Nat.reduceMod, Nat.reduceEqDiff, ↓reduceDIte]
  rw [correctionTerm]
  simp only [Nat.reduceMod, Nat.reduceEqDiff, ↓reduceDIte]
  rw [correctionTerm]
  simp only [Nat.reduceMod, Nat.reduceEqDiff, ↓reduceDIte]
  rw [correctionTerm]
  simp only [Nat.reduceMod, Nat.reduceEqDiff, ↓reduceDIte]
  rw [correctionTerm]
  simp only [Nat.reduceMod, Nat.reduceEqDiff, ↓reduceDIte]
  rw [correctionTerm]
  simp only [↓reduceDIte]
  unfold commonNumerator
  simp only [Int.cast_add, Int.cast_sub, Int.cast_mul, Int.cast_pow,
    Int.cast_natCast, Int.cast_ofNat]
  ring

private def scaledData : Array ℤ := #[
  -245, -351, -179, -219, 19, 45, -141, -49, -169, -11, -65, 159, 171, -29,
  49, -85, 59, -9, 201, 199, -15, 49, -99, 31, -51, 145, 129, -99,
  -49, -211, -95, -191, -9, -39, -281, -245, -421, -319, -429, -261, -305, -71,
  -49, -239, -151, -275, -121, -179, 41, 49, -155, -81, -219, -79, -151, 55,
  49, -169, -109, -261, -135, -221, -29, -49, -281, -235, -401, -289, -389, -211,
  -245, -1, 31, -149, -51, -165, -1, -49, 181, 199, 5, 89, -39, 111,
  49, 265, 269, 61, 131, -11, 125, 49, 251, 241, 19, 75, -81, 41,
  -49, 139, 115, -121, -79, -249, -141, -245, -71, -109, 131, 159, -25, 69,
  -49, 111, 59, 285, 299, 101, 181, 49, 195, 129, 341, 341, 129, 195,
  49, 181, 101, 299, 285, 59, 111, -49, 69, -25, 159, 131, -109, -71,
  -245, -141, -249, -79, -121, 115, 139, -49, 41, -81, 75, 19, 241, 251,
  49, 125, -11, 131, 61, 269, 265, 49, 111, -39, 89, 5, 199, 181,
  -49, -1, -165, -51, -149, 31, -1, -245, -211, -389, -289, -401, -235, -281,
  -49, -29, -221, -135, -261, -109, -169, 49, 55, -151, -79, -219, -81, -155,
  49, 41, -179, -121, -275, -151, -239, -49, -71, -305, -261, -429, -319, -421,
  -245, -281, -39, -9, -191, -95, -211, -49, -99, 129, 145, -51, 31, -99,
  49, -15, 199, 201, -9, 59, -85, 49, -29, 171, 159, -65, -11, -169,
  -49, -141, 45, 19, -219, -179, -351]

/-- The integer 245*d(Y,j); its equality with the recursion is proved below. -/
def scaledCorrection (j : Fin 245) : ℤ := scaledData[j.val]!

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem common_numerator_table :
    ∀ j : Fin 245, commonNumerator j = 2170272 * scaledCorrection j := by
  decide +kernel

theorem scaled_correction_spec (j : Fin 245) :
    dY j = (scaledCorrection j : ℚ) / 245 := by
  rw [dY_common_denominator, common_numerator_table]
  push_cast
  ring

/-- Twice a spin-centered label, reduced modulo the determinant. -/
def doubleLabel (j : Fin 245) : Fin 245 :=
  ⟨(2 * j.val) % 245, Nat.mod_lt _ (by decide)⟩

/-- An exact integer form of nonnegative even correction-term difference. -/
def Admissible (boundNumerator : ℤ) (j : Fin 245) : Prop :=
  0 ≤ boundNumerator - scaledCorrection j ∧
    (boundNumerator - scaledCorrection j) % 490 = 0

instance (b : ℤ) (j : Fin 245) : Decidable (Admissible b j) := by
  unfold Admissible
  infer_instance

/-- A correction-term equality as required by Owens implies the tested predicate. -/
theorem admissible_of_comparison (b : ℤ) (j : Fin 245) (n : ℕ)
    (hc : (b : ℚ) / 245 - dY j = 2 * n) : Admissible b j := by
  rw [scaled_correction_spec j] at hc
  have heqQ : ((b - scaledCorrection j : ℤ) : ℚ) = ((490 * (n : ℤ) : ℤ) : ℚ) := by
    push_cast
    linarith
  have heq : b - scaledCorrection j = 490 * (n : ℤ) := by exact_mod_cast heqQ
  unfold Admissible
  rw [heq]
  constructor
  · exact mul_nonneg (by decide) (Int.natCast_nonneg n)
  · omega

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- All single-vector obstructions, including the form excluded by cyclicity in the paper. -/
theorem single_vector_obstructions : ∀ j : Fin 245,
    ¬ Admissible (-199) j ∧ ¬ Admissible 1 j ∧
    ¬ Admissible (-225) j ∧ ¬ Admissible (-175) j := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- No label can work simultaneously for x and 2x in the remaining form. -/
theorem doubling_obstruction : ∀ j : Fin 245,
    ¬ (Admissible (-239) j ∧ Admissible (-221) (doubleLabel j)) := by
  decide +kernel

end Trefoil.Finite
