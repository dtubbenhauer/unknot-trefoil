import Trefoil.FiniteObstruction
import Trefoil.Arithmetic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.Tactic.Linarith

/-!
# Section 3B: from Owens's minima to individual test vectors

Theorem 1 of Owens compares the minimum characteristic-vector value `m_Q`
with a correction term on the boundary. The existing `FiniteObstruction`
needs the corresponding inequality and congruence for *each* integral
characteristic vector, not only a minimizer.

This module proves that transfer. The minimum-property and the Floer
comparison are kept separate. The latter is a general reference input,
not an assumption about any particular one of the five matrices.
-/

namespace Trefoil.Section3BMinimum

open Trefoil.Finite
open scoped BigOperators

/-- Owens's reduced rank-four form for a determinant `delta`.
The modulus is not specialized to the determinant of our knot. -/
def ReducedAt (delta : ℕ) (h a s : ℤ) : Prop :=
  0 ≤ a ∧ a < h ∧ h ≤ s ∧ h % 2 = 0 ∧ s % 2 = 0 ∧
    (2 * h - 1) * (2 * s - 1) - 4 * a ^ 2 = (delta : ℤ)

/-- Every positive-surgery lens space is oriented here as
`L(p,q) = -L(p,p-q)` in the recursion convention.
For odd `p`, the unique spin structure is the solution of
`2*i = p+(p-q)-1 (mod p)`. -/
def spinBase (p q : ℕ) : ℕ :=
  ((p + (p - q) - 1) * ((p + 1) / 2)) % p

/-- Spin-centered Ozsváth--Szabó correction term in positive-surgery
orientation. This is a numerical model; its identification with the
actual Floer invariant is a separate input in `Section3BTopology`. -/
def lensCorrection (p q : ℕ) (j : ZMod p) : ℚ :=
  correctionTerm p (p - q) ((spinBase p q + j.val) % p)

/-- The spin base for the oriented cover `L(245,104)` is `70` in
`-L(245,141)` convention. -/
theorem spinBase_245 : spinBase 245 104 = 70 := by decide

/-- The generally defined recursion agrees exactly with the 245-entry
array whose values were independently checked by the original Lean code. -/
theorem lensCorrection_245 (j : ZMod 245) :
    lensCorrection 245 104 j = dY ⟨j.val, ZMod.val_lt j⟩ := by
  change correctionTerm 245 141 ((spinBase 245 104 + j.val) % 245) =
    correctionTerm 245 141 ((70 + j.val) % 245)
  rw [spinBase_245]

/-- The canonical representative of a class in `ZMod 245` as a finite label. -/
def finiteLabel (j : ZMod 245) : Fin 245 := ⟨j.val, ZMod.val_lt j⟩

/-- Any additive labeling automatically takes `x+x` to twice the label.
This is the only group-theoretic feature required by `FiniteObstruction`. -/
theorem finiteLabel_double (j : ZMod 245) :
    finiteLabel (j + j) = doubleLabel (finiteLabel j) := by
  apply Fin.ext
  change (j + j).val = (2 * j.val) % 245
  rw [ZMod.val_add]
  omega

/-- The integral surgery matrix whose rational extension is used to evaluate
the characteristic quadratic bound. -/
def surgeryMatrixZ (h a s : ℤ) : Matrix (Fin 4) (Fin 4) ℤ :=
  ![![h, 1, a, 0], ![1, 2, 0, 0], ![a, 0, s, 1], ![0, 0, 1, 2]]

theorem surgeryMatrixZ_det (h a s : ℤ) :
    (surgeryMatrixZ h a s).det = (2 * h - 1) * (2 * s - 1) - 4 * a ^ 2 := by
  rw [Matrix.det_succ_row_zero, Fin.sum_univ_four]
  simp [Matrix.det_fin_three, surgeryMatrixZ, Matrix.submatrix_apply, Fin.succAbove]
  ring

/-- The presentation map of the integral surgery matrix. -/
def surgeryMap (h a s : ℤ) : ZVector →ₗ[ℤ] ZVector where
  toFun := (surgeryMatrixZ h a s).mulVec
  map_add' := Matrix.mulVec_add _
  map_smul' r x := Matrix.mulVec_smul _ r x

/-- The finite group presented by the surgery matrix. -/
abbrev SurgeryCokernel (h a s : ℤ) := ZVector ⧸ (LinearMap.range (surgeryMap h a s))

/-- The class of the integral covector in the surgery presentation. -/
def cokernelClass (h a s : ℤ) : ZVector →+ SurgeryCokernel h a s :=
  (LinearMap.range (surgeryMap h a s)).mkQ.toAddMonoidHom

/-- Changing an integral representative of a class by the image of the
surgery matrix. -/
def surgeryTranslate (h a s : ℤ) (x y : ZVector) : ZVector :=
  x + (surgeryMatrixZ h a s).mulVec y

/-- The quadratic change under translation by an integral surgery column. -/
theorem quadraticBound_translate {h a s : ℤ} (x y : ZVector) (z : QVector)
    (hz : (surgeryMatrix h a s).mulVec z = fun i => (x i : ℚ)) :
    quadraticBound (surgeryTranslate h a s x y) (fun i => z i + (y i : ℚ)) -
        quadraticBound x z =
      ((2 * ∑ i, y i * x i) + ∑ i, y i * (surgeryMatrixZ h a s).mulVec y i : ℤ) := by
  have hz0 := congrFun hz (0 : Fin 4)
  have hz1 := congrFun hz (1 : Fin 4)
  have hz2 := congrFun hz (2 : Fin 4)
  have hz3 := congrFun hz (3 : Fin 4)
  simp [surgeryMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_four] at hz0 hz1 hz2 hz3
  simp [quadraticBound, surgeryTranslate, surgeryMatrixZ, Matrix.mulVec, dotProduct,
    Fin.sum_univ_four]
  rw [← hz0, ← hz1, ← hz2, ← hz3]
  ring

/-- Translates of an integral representative have quadratic values differing
by an even integer, because the two nonconstant framing weights are even. -/
theorem quadraticBound_translate_even {h a s : ℤ} (hh : h % 2 = 0) (hs : s % 2 = 0)
    (x y : ZVector) (z : QVector)
    (hz : (surgeryMatrix h a s).mulVec z = fun i => (x i : ℚ)) :
    ∃ k : ℤ, quadraticBound (surgeryTranslate h a s x y) (fun i => z i + (y i : ℚ)) -
        quadraticBound x z = 2 * (k : ℚ) := by
  have hf : h = 2 * (h / 2) := by omega
  have hg : s = 2 * (s / 2) := by omega
  rw [quadraticBound_translate x y z hz]
  let k := (∑ i, y i * x i) +
    (h / 2) * (y 0) ^ 2 + y 0 * y 1 + a * y 0 * y 2 + (y 1) ^ 2 +
    (s / 2) * (y 2) ^ 2 + y 2 * y 3 + (y 3) ^ 2
  refine ⟨k, ?_⟩
  have heq : (2 * ∑ i, y i * x i) + ∑ i, y i * (surgeryMatrixZ h a s).mulVec y i =
      2 * k := by
    simp [k, surgeryMatrixZ, Matrix.mulVec, dotProduct, Fin.sum_univ_four]
    conv_lhs => rw [hf, hg]
    ring
  rw [heq]
  push_cast
  rfl

/-- Characteristic covectors reduce to the diagonal entries modulo two. -/
def Characteristic (h a s : ℤ) (ξ : ZVector) : Prop :=
  ∀ i, ξ i % 2 = (surgeryMatrixZ h a s i i) % 2

/-- In the even surgery form, the characteristic covectors are exactly the
vectors `2*x`. -/
theorem characteristic_iff_twice {h a s : ℤ} (hh : h % 2 = 0) (hs : s % 2 = 0)
    (ξ : ZVector) : Characteristic h a s ξ ↔ ∃ x : ZVector, ξ = fun i => 2 * x i := by
  have hdiag (i : Fin 4) : (surgeryMatrixZ h a s i i) % 2 = 0 := by
    fin_cases i <;> simp [surgeryMatrixZ, hh, hs]
  constructor
  · intro hξ
    refine ⟨fun i => ξ i / 2, ?_⟩
    funext i
    have hmod : ξ i % 2 = 0 := (hξ i).trans (hdiag i)
    change ξ i = 2 * (ξ i / 2)
    omega
  · rintro ⟨x, rfl⟩ i
    rw [hdiag]
    change (2 * x i) % 2 = 0
    omega

/-- If `z` solves the surgery equation for `x`, then `2*z` solves it
for the characteristic covector `2*x`. Its normalized square is
`quadraticBound x z`. -/
theorem doubled_characteristic_value {h a s : ℤ} (x : ZVector) (z : QVector)
    (hz : (surgeryMatrix h a s).mulVec z = fun i => (x i : ℚ)) :
    (surgeryMatrix h a s).mulVec (fun i => 2 * z i) = (fun i => ((2 * x i : ℤ) : ℚ)) ∧
      ((∑ i, ((2 * x i : ℤ) : ℚ) * (2 * z i)) - 4) / 4 = quadraticBound x z := by
  constructor
  · change (surgeryMatrix h a s).mulVec ((2 : ℚ) • z) = _
    rw [Matrix.mulVec_smul, hz]
    ext i
    simp [smul_eq_mul]
  · simp [quadraticBound, Fin.sum_univ_four]
    ring

/-- Multiplication by two is an automorphism of the labels for odd-order
boundary homology. Its inverse is multiplication by `(p+1)/2`. -/
def doubleClassesEquiv {p : ℕ} (hp : Odd p) : ZMod p ≃+ ZMod p := by
  let u : ZMod p := (((p + 1) / 2 : ℕ) : ZMod p)
  have hnat : ((p + 1) / 2) * 2 = p + 1 := by
    obtain ⟨k, hk⟩ := hp
    omega
  have hu : u * 2 = 1 := by
    calc
      u * 2 = ((((p + 1) / 2) * 2 : ℕ) : ZMod p) := by simp [u, Nat.cast_mul]
      _ = 1 := by rw [hnat]; simp
  refine
    { toFun := fun j => j + j
      invFun := fun j => u * j
      map_add' := fun x y => add_add_add_comm x y x y
      left_inv := fun j => ?_
      right_inv := fun j => ?_ }
  · change u * (j + j) = j
    rw [← two_mul, ← mul_assoc, hu, one_mul]
  · change u * j + u * j = j
    rw [← two_mul, ← mul_assoc, mul_comm 2 u, hu, one_mul]

/-- The minimum comparison from Owens's theorem uses a single additive
isomorphism from the actual cokernel to the boundary labels. In an even
surgery form the characteristic covectors are `2*x`. The label here
incorporates multiplication by two on the odd-order cokernel, as in Owens's
characteristic-class convention. The minimum is attained at a translated
representative, and is bounded above by each characteristic value. -/
structure OwensMinimum (delta : ℕ) (h a s : ℤ)
    (d : ZMod delta → ℚ) where
  classIso : SurgeryCokernel h a s ≃+ ZMod delta
  minimum : ZMod delta → ℚ
  attained : ∀ x : ZVector, ∀ z : QVector,
    (surgeryMatrix h a s).mulVec z = (fun i => (x i : ℚ)) →
      ∃ y : ZVector, quadraticBound (surgeryTranslate h a s x y) (fun i => z i + (y i : ℚ)) =
        minimum (classIso (cokernelClass h a s x))
  minimizing : ∀ x : ZVector, ∀ z : QVector,
    (surgeryMatrix h a s).mulVec z = (fun i => (x i : ℚ)) →
      minimum (classIso (cokernelClass h a s x)) ≤ quadraticBound x z
  floerComparison : ∀ j : ZMod delta,
    ∃ n : ℕ, minimum j - d j = 2 * (n : ℚ)

/-- The class label of an integral representative of a doubled
characteristic covector. -/
def OwensMinimum.label {delta : ℕ} {h a s : ℤ}
    {d : ZMod delta → ℚ} (w : OwensMinimum delta h a s d) : ZVector →+ ZMod delta :=
  w.classIso.toAddMonoidHom.comp (cokernelClass h a s)

private theorem OwensMinimum.minimizing_even_difference {delta : ℕ} {h a s : ℤ}
    {d : ZMod delta → ℚ} (w : OwensMinimum delta h a s d)
    (hh : h % 2 = 0) (hs : s % 2 = 0) (x : ZVector) (z : QVector)
    (hz : (surgeryMatrix h a s).mulVec z = (fun i => (x i : ℚ))) :
    ∃ n : ℕ, quadraticBound x z - w.minimum (w.label x) = 2 * (n : ℚ) := by
  obtain ⟨y, hy⟩ := w.attained x z hz
  obtain ⟨k, hk⟩ := quadraticBound_translate_even hh hs x y z hz
  change _ = w.minimum (w.label x) at hy
  rw [hy] at hk
  have hmin : w.minimum (w.label x) ≤ quadraticBound x z := w.minimizing x z hz
  have hk_nonpos_rat : (k : ℚ) ≤ 0 := by linarith
  have hk_nonpos : k ≤ 0 := by exact_mod_cast hk_nonpos_rat
  refine ⟨(-k).toNat, ?_⟩
  have hcast : (((-k).toNat : ℕ) : ℤ) = -k := Int.toNat_of_nonneg (by omega)
  rw [← Int.cast_natCast, hcast, Int.cast_neg]
  linarith

/-- Changing the supplied correction term by a pointwise equality does
not alter a minimum witness. This keeps the general Floer input distinct
from the Ozsváth--Szabó lens-space calculation. -/
def OwensMinimum.changeCorrection {delta : ℕ} {h a s : ℤ}
    {d₁ d₂ : ZMod delta → ℚ} (w : OwensMinimum delta h a s d₁)
    (hd : ∀ j, d₁ j = d₂ j) : OwensMinimum delta h a s d₂ where
  classIso := w.classIso
  minimum := w.minimum
  attained := w.attained
  minimizing := w.minimizing
  floerComparison := by
    intro j
    obtain ⟨n, hn⟩ := w.floerComparison j
    exact ⟨n, by rw [← hd j]; exact hn⟩

/-- The nontrivial bridge missing from the previous checkpoint:
Owens's minimum inequality plus characteristic-vector minimality yields
the precise *all-test-vectors* comparison used in the already verified
finite obstruction. Additivity of the spin-centered isomorphism supplies
the doubling requirement, rather than assuming it. -/
theorem minimum_to_comparison {h a s : ℤ} (hr : ReducedAt 245 h a s)
    (w : OwensMinimum 245 h a s (lensCorrection 245 104)) :
    HasCorrectionComparison h a s := by
  refine ⟨(fun x => finiteLabel (w.label x)), ?_, ?_⟩
  · intro x
    change finiteLabel (w.label (x + x)) =
      doubleLabel (finiteLabel (w.label x))
    rw [map_add]
    exact finiteLabel_double (w.label x)
  · intro x z hz
    obtain ⟨n, hn⟩ := w.minimizing_even_difference hr.2.2.2.1 hr.2.2.2.2.1 x z hz
    obtain ⟨k, hk⟩ := w.floerComparison (w.label x)
    refine ⟨n + k, ?_⟩
    have hd : lensCorrection 245 104 (w.label x) =
        dY (finiteLabel (w.label x)) := lensCorrection_245 (w.label x)
    change quadraticBound x z - dY (finiteLabel (w.label x)) =
      2 * ((n + k : ℕ) : ℚ)
    rw [← hd]
    push_cast
    linarith

/-- The five-case contradiction, now starting from the *two premises*
which Owens's theorem and the definition of `m_Q` actually supply. -/
theorem no_owens_minimum_245 {h a s : ℤ}
    (hr : ReducedAt 245 h a s)
    (w : OwensMinimum 245 h a s (lensCorrection 245 104)) : False := by
  have hred : ReducedForm h a s := by
    simpa only [ReducedAt, ReducedForm] using hr
  exact no_reduced_correction_comparison hred (minimum_to_comparison hr w)

end Trefoil.Section3BMinimum
