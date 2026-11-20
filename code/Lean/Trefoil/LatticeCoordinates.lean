import Trefoil.LatticeEmbedding
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Ring

/-!
# Coordinates on the five disjoint blocks

The rows below are the coordinate shapes forced by the root pairings. This
module computes their norms and mutual pairings; `LatticeShapes` derives the
shapes, and `LatticeExtraction` applies these identities to an actual embedding.
-/

namespace Trefoil.LatticeCoordinates

open scoped BigOperators
open LatticeEmbedding

def rowA (m : ℕ) (a z r s t : ℤ) : Blocks m → ℤ
  | .inl i => if i.val + 1 = m then a + 1 else a
  | .inr (.inl _) => z
  | .inr (.inr (.inl _)) => r
  | .inr (.inr (.inr (.inl _))) => s
  | .inr (.inr (.inr (.inr _))) => t

def rowB (m : ℕ) (b g r s t : ℤ) : Blocks m → ℤ
  | .inl _ => b
  | .inr (.inl i) => if i.val = 0 then g - 1 else g
  | .inr (.inr (.inl _)) => r
  | .inr (.inr (.inr (.inl _))) => s
  | .inr (.inr (.inr (.inr _))) => t

def rowC (m : ℕ) (c ell r s t : ℤ) : Blocks m → ℤ
  | .inl _ => c
  | .inr (.inl i) => if i.val = 2 then ell + 1 else ell
  | .inr (.inr (.inl _)) => r
  | .inr (.inr (.inr (.inl _))) => s
  | .inr (.inr (.inr (.inr _))) => t

theorem sum_last (m : ℕ) (hm : 1 ≤ m) (u v : ℤ) :
    (∑ i : Fin m, if i.val + 1 = m then u else v) = (m : ℤ) * v + (u - v) := by
  cases m with
  | zero => omega
  | succ n =>
    have hi (i : Fin n) : i.val ≠ n := Nat.ne_of_lt i.isLt
    simp [Fin.sum_univ_castSucc, hi, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
    ring

theorem long_normA (m : ℕ) (hm : 1 ≤ m) (a : ℤ) :
    (∑ i : Fin m, (if i.val + 1 = m then a + 1 else a)^2) =
      (m : ℤ)*a^2 + 2*a + 1 := by
  calc
    _ = ∑ i : Fin m, if i.val + 1 = m then (a+1)^2 else a^2 := by
      apply Finset.sum_congr rfl
      intro i _
      split_ifs <;> rfl
    _ = _ := by rw [sum_last m hm]; ring

theorem long_pairingA (m : ℕ) (hm : 1 ≤ m) (a b : ℤ) :
    (∑ i : Fin m, (if i.val + 1 = m then a + 1 else a)*b) =
      ((m : ℤ)*a + 1)*b := by
  calc
    _ = ∑ i : Fin m, if i.val + 1 = m then (a+1)*b else a*b := by
      apply Finset.sum_congr rfl
      intro i _
      split_ifs <;> rfl
    _ = _ := by rw [sum_last m hm]; ring

theorem norm_rowA (m : ℕ) (hm : 1 ≤ m) (a z r s t : ℤ) :
    (∑ i, rowA m a z r s t i ^ 2) =
      (m:ℤ)*a^2 + 2*a + 1 + 3*z^2 + 2*r^2 + 2*s^2 + t^2 := by
  simp only [Fintype.sum_sum_type, rowA, Fin.sum_univ_three, Fin.sum_univ_two]
  rw [long_normA m hm]
  simp only [Fintype.sum_unique]
  ring

theorem norm_rowB (m : ℕ) (b g r s t : ℤ) :
    (∑ i, rowB m b g r s t i ^ 2) =
      (m:ℤ)*b^2 + (g-1)^2 + 2*g^2 + 2*r^2 + 2*s^2 + t^2 := by
  simp [Fintype.sum_sum_type, rowB, Fin.sum_univ_three,
    nsmul_eq_mul]
  ring

theorem norm_rowC (m : ℕ) (c ell r s t : ℤ) :
    (∑ i, rowC m c ell r s t i ^ 2) =
      (m:ℤ)*c^2 + 2*ell^2 + (ell+1)^2 + 2*r^2 + 2*s^2 + t^2 := by
  simp [Fintype.sum_sum_type, rowC, Fin.sum_univ_three,
    nsmul_eq_mul]
  ring

theorem pairing_rowAB (m : ℕ) (hm : 1 ≤ m)
    (a z rA sA tA b g rB sB tB : ℤ) :
    LatticeSupports.dot (rowA m a z rA sA tA) (rowB m b g rB sB tB) =
      ((m:ℤ)*a+1)*b + z*(3*g-1) + 2*(rA*rB+sA*sB) + tA*tB := by
  simp only [LatticeSupports.dot, Fintype.sum_sum_type, rowA, rowB,
    Fin.sum_univ_three, Fin.sum_univ_two]
  rw [long_pairingA m hm]
  norm_num
  ring

theorem pairing_rowAC (m : ℕ) (hm : 1 ≤ m)
    (a z rA sA tA c ell rC sC tC : ℤ) :
    LatticeSupports.dot (rowA m a z rA sA tA) (rowC m c ell rC sC tC) =
      ((m:ℤ)*a+1)*c + z*(3*ell+1) + 2*(rA*rC+sA*sC) + tA*tC := by
  simp only [LatticeSupports.dot, Fintype.sum_sum_type, rowA, rowC,
    Fin.sum_univ_three, Fin.sum_univ_two]
  rw [long_pairingA m hm]
  norm_num
  ring

theorem pairing_rowBC (m : ℕ)
    (b g rB sB tB c ell rC sC tC : ℤ) :
    LatticeSupports.dot (rowB m b g rB sB tB) (rowC m c ell rC sC tC) =
      (m:ℤ)*b*c + 3*g*ell + g-ell + 2*(rB*rC+sB*sC) + tB*tC := by
  simp [LatticeSupports.dot, Fintype.sum_sum_type, rowB, rowC,
    Fin.sum_univ_three, nsmul_eq_mul]
  ring

end Trefoil.LatticeCoordinates
