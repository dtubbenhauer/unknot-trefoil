import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.Linarith
import Mathlib.Data.Finset.Card
import Lean.Elab.Tactic.Omega

/-!
# Elementary lattice facts used in Section 3A

These are internal proofs, not literature hypotheses.  The coordinate-path
normalization of a whole configuration is a separate bridge; proving that
each norm-two vector has two coordinates does not prove that bridge.
-/

namespace Trefoil.LatticeBasics

open scoped BigOperators

/-- Every coordinate of an integral vector of square two is zero or a unit. -/
theorem norm_two_coordinate {ι : Type*} [Fintype ι] [DecidableEq ι]
    (v : ι → ℤ) (hv : ∑ i, v i ^ 2 = 2) (i : ι) :
    v i = -1 ∨ v i = 0 ∨ v i = 1 := by
  have hle : v i ^ 2 ≤ ∑ j, v j ^ 2 :=
    Finset.single_le_sum (fun j _ => sq_nonneg (v j)) (Finset.mem_univ i)
  rw [hv] at hle
  have hlo : -1 ≤ v i := by nlinarith [sq_nonneg (v i + 1)]
  have hhi : v i ≤ 1 := by nlinarith [sq_nonneg (v i - 1)]
  omega

/-- The support of an integral norm-two vector consists of exactly two indices. -/
theorem norm_two_support_card {ι : Type*} [Fintype ι] [DecidableEq ι]
    (v : ι → ℤ) (hv : ∑ i, v i ^ 2 = 2) :
    (Finset.univ.filter (fun i => v i ≠ 0)).card = 2 := by
  have hs : ∀ i, v i ^ 2 = if v i ≠ 0 then (1 : ℤ) else 0 := by
    intro i
    rcases norm_two_coordinate v hv i with h | h | h <;> simp [h]
  have hc : (∑ i, v i ^ 2) =
      ((Finset.univ.filter (fun i => v i ≠ 0)).card : ℤ) := by
    simp_rw [hs]
    rw [← Finset.sum_filter]
    simp
  omega

/-- An explicit two-element support, with no choice of a normal form assumed. -/
theorem norm_two_support_pair {ι : Type*} [Fintype ι] [DecidableEq ι]
    (v : ι → ℤ) (hv : ∑ i, v i ^ 2 = 2) :
    ∃ i j, i ≠ j ∧ Finset.univ.filter (fun k => v k ≠ 0) = {i, j} := by
  exact Finset.card_eq_two.mp (norm_two_support_card v hv)

/-- An odd integral determinant stays nonzero after reduction modulo two. -/
theorem odd_det_mod_two_ne_zero {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℤ) (hodd : Odd M.det) :
    (M.map (Int.castRingHom (ZMod 2))).det ≠ 0 := by
  change ((Int.castRingHom (ZMod 2)).mapMatrix M).det ≠ 0
  rw [← RingHom.map_det]
  change (M.det : ZMod 2) ≠ 0
  intro hzero
  have hdiv := (ZMod.intCast_zmod_eq_zero_iff_dvd M.det 2).mp hzero
  rcases hodd with ⟨k, hk⟩
  rcases hdiv with ⟨l, hl⟩
  omega

/-- The odd-index step used for the joint plumbing/filling basis. -/
theorem odd_det_columns_independent_mod_two {ι : Type*}
    [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℤ) (hodd : Odd M.det) :
    LinearIndependent (ZMod 2) (M.map (Int.castRingHom (ZMod 2))).col := by
  exact Matrix.linearIndependent_cols_of_det_ne_zero (odd_det_mod_two_ne_zero M hodd)

end Trefoil.LatticeBasics
