import Trefoil.FiniteCorrectionTerms
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Matrix.Notation

/-!
# The complete finite correction-term obstruction

This theorem is pure integer/rational mathematics. It has no topological input.
The topology enters only when Owens's theorem and the lens-space interpretation
are used to produce `HasCorrectionComparison` in the caller.

The proof uses a slightly stronger set of witnesses than the manuscript:
* `(4,0,18)` is obstructed by `x=(-1,0,0,0)`, with bound `-5/7`;
* `(2,1,42)` is obstructed by the simultaneous tests at `x` and `x+x`,
  for every label, without a cyclic-cokernel or unit-multiplier calculation.
-/

namespace Trefoil.Finite

open scoped BigOperators

abbrev ZVector := Fin 4 → ℤ
abbrev QVector := Fin 4 → ℚ

/-- The even positive surgery-form shape in Section 3B. -/
def surgeryMatrix (h a s : ℤ) : Matrix (Fin 4) (Fin 4) ℚ :=
  ![![(h : ℚ), 1, (a : ℚ), 0], ![1, 2, 0, 0],
    ![(a : ℚ), 0, (s : ℚ), 1], ![0, 0, 1, 2]]

/-- Evaluating xᵀQ⁻¹x−1 using a solution z to Qz=x. -/
def quadraticBound (x : ZVector) (z : QVector) : ℚ :=
  (∑ i : Fin 4, (x i : ℚ) * z i) - 1

/-- A necessary weakening of Owens's correction-term comparison.
The genuine spin-centered cokernel isomorphism preserves addition, hence doubling.
The inequality is required for every integral x, not just one chosen witness. -/
def HasCorrectionComparison (h a s : ℤ) : Prop :=
  ∃ label : ZVector → Fin 245,
    (∀ x, label (x + x) = doubleLabel (label x)) ∧
    ∀ (x : ZVector) (z : QVector),
      (surgeryMatrix h a s).mulVec z = (fun i => (x i : ℚ)) →
      ∃ n : ℕ, quadraticBound x z - dY (label x) = 2 * n

private def firstVector : ZVector := ![-1, 0, 0, 0]
private def mixedVector : ZVector := ![-1, 0, -1, 0]
private def thirdVector : ZVector := ![0, 0, -1, 0]
private def twiceThirdVector : ZVector := ![0, 0, -2, 0]

private def solution8 : QVector := ![-46/245, 23/245, 4/49, -2/49]
private def solution62 : QVector := ![-246/245, 123/245, 244/245, -122/245]
private def solution14 : QVector := ![-2/49, 1/49, -2/49, 1/49]
private def solution4 : QVector := ![-2/7, 1/7, 0, 0]
private def solution2 : QVector := ![4/245, -2/245, -6/245, 3/245]
private def solution2twice : QVector := ![8/245, -4/245, -12/245, 6/245]

set_option maxRecDepth 1000000 in
private theorem witness8 :
    (surgeryMatrix 8 5 12).mulVec solution8 = (fun i => (firstVector i : ℚ)) ∧
      quadraticBound firstVector solution8 = (-199 : ℚ) / 245 := by decide +kernel

set_option maxRecDepth 1000000 in
private theorem witness62 :
    (surgeryMatrix 62 61 62).mulVec solution62 = (fun i => (firstVector i : ℚ)) ∧
      quadraticBound firstVector solution62 = (1 : ℚ) / 245 := by decide +kernel

set_option maxRecDepth 1000000 in
private theorem witness14 :
    (surgeryMatrix 14 11 14).mulVec solution14 = (fun i => (mixedVector i : ℚ)) ∧
      quadraticBound mixedVector solution14 = (-225 : ℚ) / 245 := by decide +kernel

set_option maxRecDepth 1000000 in
private theorem witness4 :
    (surgeryMatrix 4 0 18).mulVec solution4 = (fun i => (firstVector i : ℚ)) ∧
      quadraticBound firstVector solution4 = (-175 : ℚ) / 245 := by decide +kernel

set_option maxRecDepth 1000000 in
private theorem witness2 :
    (surgeryMatrix 2 1 42).mulVec solution2 = (fun i => (thirdVector i : ℚ)) ∧
      quadraticBound thirdVector solution2 = (-239 : ℚ) / 245 := by decide +kernel

set_option maxRecDepth 1000000 in
private theorem witness2twice :
    (surgeryMatrix 2 1 42).mulVec solution2twice = (fun i => (twiceThirdVector i : ℚ)) ∧
      quadraticBound twiceThirdVector solution2twice = (-221 : ℚ) / 245 := by decide +kernel

private theorem no_comparison_of_witness {h a s b : ℤ}
    (x : ZVector) (z : QVector)
    (hw : (surgeryMatrix h a s).mulVec z = (fun i => (x i : ℚ)) ∧
      quadraticBound x z = (b : ℚ) / 245)
    (ho : ∀ j, ¬ Admissible b j) : ¬ HasCorrectionComparison h a s := by
  rintro ⟨label, hd, hc⟩
  obtain ⟨n, hn⟩ := hc x z hw.1
  rw [hw.2] at hn
  exact ho (label x) (admissible_of_comparison b (label x) n hn)

theorem no_comparison_8_5_12 : ¬ HasCorrectionComparison 8 5 12 :=
  no_comparison_of_witness firstVector solution8 witness8
    (fun j => (single_vector_obstructions j).1)

theorem no_comparison_62_61_62 : ¬ HasCorrectionComparison 62 61 62 :=
  no_comparison_of_witness firstVector solution62 witness62
    (fun j => (single_vector_obstructions j).2.1)

theorem no_comparison_14_11_14 : ¬ HasCorrectionComparison 14 11 14 :=
  no_comparison_of_witness mixedVector solution14 witness14
    (fun j => (single_vector_obstructions j).2.2.1)

theorem no_comparison_4_0_18 : ¬ HasCorrectionComparison 4 0 18 :=
  no_comparison_of_witness firstVector solution4 witness4
    (fun j => (single_vector_obstructions j).2.2.2)

theorem no_comparison_2_1_42 : ¬ HasCorrectionComparison 2 1 42 := by
  rintro ⟨label, hd, hc⟩
  obtain ⟨n, hn⟩ := hc thirdVector solution2 witness2.1
  obtain ⟨n2, hn2⟩ := hc twiceThirdVector solution2twice witness2twice.1
  have hdouble : twiceThirdVector = thirdVector + thirdVector := by decide +kernel
  have hlabel : label twiceThirdVector = doubleLabel (label thirdVector) := by
    rw [hdouble]
    exact hd thirdVector
  rw [witness2.2] at hn
  rw [witness2twice.2, hlabel] at hn2
  exact doubling_obstruction (label thirdVector)
    ⟨admissible_of_comparison (-239) _ n hn,
     admissible_of_comparison (-221) _ n2 hn2⟩

/-- The complete unconditional arithmetic obstruction for determinant 245. -/
theorem no_reduced_correction_comparison {h a s : ℤ}
    (hf : ReducedForm h a s) : ¬ HasCorrectionComparison h a s := by
  rcases candidates_complete hf with
    ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  · exact no_comparison_2_1_42
  · exact no_comparison_4_0_18
  · exact no_comparison_8_5_12
  · exact no_comparison_14_11_14
  · exact no_comparison_62_61_62

end Trefoil.Finite
