import Mathlib.Tactic.Linarith
import Mathlib.Data.Fintype.Fin

/-!
# The exhaustive determinant-245 search

This module proves the finite classification in Section 3B of the manuscript.
The bound is derived for arbitrary integer weights before a finite computation
is used. The finite computation is evaluated by Lean's kernel.
-/

namespace Trefoil.Finite

/-- The reduced even forms supplied by Owens's theorem in the determinant-245 case. -/
def ReducedForm (h a s : ℤ) : Prop :=
  0 ≤ a ∧ a < h ∧ h ≤ s ∧ h % 2 = 0 ∧ s % 2 = 0 ∧
    (2 * h - 1) * (2 * s - 1) - 4 * a ^ 2 = 245

instance (h a s : ℤ) : Decidable (ReducedForm h a s) := by
  unfold ReducedForm
  infer_instance

/-- The five forms listed in Section 3B. -/
def FiveCandidates (h a s : ℤ) : Prop :=
  (h = 2 ∧ a = 1 ∧ s = 42) ∨
  (h = 4 ∧ a = 0 ∧ s = 18) ∨
  (h = 8 ∧ a = 5 ∧ s = 12) ∨
  (h = 14 ∧ a = 11 ∧ s = 14) ∨
  (h = 62 ∧ a = 61 ∧ s = 62)

instance (h a s : ℤ) : Decidable (FiveCandidates h a s) := by
  unfold FiveCandidates
  infer_instance

/-- The determinant equation, reduction and parity imply the advertised bound. -/
theorem first_weight_bounds {h a s : ℤ} (hf : ReducedForm h a s) :
    2 ≤ h ∧ h ≤ 62 := by
  rcases hf with ⟨ha0, hah, hhs, he, se, hd⟩
  have h2 : 2 ≤ h := by omega
  have hp : 0 ≤ (2 * h - 1) * (2 * s - 2 * h) :=
    mul_nonneg (by omega) (by omega)
  have ha : 0 ≤ (h - 1 - a) * (h - 1 + a) :=
    mul_nonneg (by omega) (by omega)
  constructor
  · exact h2
  · nlinarith

/-- Solving the determinant equation for the last weight. -/
def lastWeight (h a : ℤ) : ℤ :=
  (245 + 4 * a ^ 2 + (2 * h - 1)) / (2 * (2 * h - 1))

theorem last_weight_eq {h a s : ℤ} (hf : ReducedForm h a s) :
    s = lastWeight h a := by
  have hh := (first_weight_bounds hf).1
  have hd := hf.2.2.2.2.2
  unfold lastWeight
  apply Int.eq_ediv_of_mul_eq_right (by omega : 2 * (2 * h - 1) ≠ 0)
  nlinarith

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- A genuinely finite, kernel-evaluated classification after the bound. -/
theorem bounded_candidates :
    ∀ h a : Fin 63,
      ReducedForm (h.val : ℤ) (a.val : ℤ) (lastWeight h.val a.val) →
      FiveCandidates (h.val : ℤ) (a.val : ℤ) (lastWeight h.val a.val) := by
  decide +kernel

/-- Completeness for unbounded integer inputs; no finite-range premise is assumed. -/
theorem candidates_complete {h a s : ℤ} (hf : ReducedForm h a s) :
    FiveCandidates h a s := by
  have hb := first_weight_bounds hf
  have ha0 := hf.1
  have hah := hf.2.1
  have hs := last_weight_eq hf
  let h' : Fin 63 := ⟨h.toNat, by omega⟩
  let a' : Fin 63 := ⟨a.toNat, by omega⟩
  have hh' : (h'.val : ℤ) = h := by simp [h', Int.toNat_of_nonneg (by omega : 0 ≤ h)]
  have ha' : (a'.val : ℤ) = a := by simp [a', Int.toNat_of_nonneg ha0]
  have hc := bounded_candidates h' a'
  rw [hh', ha'] at hc
  have hf' : ReducedForm h a (lastWeight h a) := by simpa [← hs] using hf
  simpa [← hs] using hc hf'

end Trefoil.Finite
