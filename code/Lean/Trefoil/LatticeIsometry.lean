import Trefoil.LatticeCoordinates

/-! Reindexing coordinates and changing coordinate signs preserve the
standard integral norm and pairing. -/

namespace Trefoil.LatticeIsometry

open scoped BigOperators

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

def signedPullback (e : κ ≃ ι) (s : κ → ℤ) (x : ι → ℤ) : κ → ℤ :=
  fun j => s j * x (e j)

theorem dot_signedPullback (e : κ ≃ ι) (s : κ → ℤ)
    (hs : ∀ j, s j ^ 2 = 1) (x y : ι → ℤ) :
    LatticeSupports.dot (signedPullback e s x) (signedPullback e s y) =
      LatticeSupports.dot x y := by
  unfold LatticeSupports.dot signedPullback
  calc
    _ = ∑ j : κ, x (e j) * y (e j) := by
      apply Finset.sum_congr rfl
      intro j _
      calc
        _ = s j ^ 2 * (x (e j) * y (e j)) := by ring
        _ = _ := by rw [hs j]; ring
    _ = _ := e.sum_comp (fun j => x j * y j)

theorem norm_signedPullback (e : κ ≃ ι) (s : κ → ℤ)
    (hs : ∀ j, s j ^ 2 = 1) (x : ι → ℤ) :
    (∑ j, signedPullback e s x j ^ 2) = ∑ i, x i ^ 2 := by
  simpa only [LatticeSupports.dot, pow_two] using dot_signedPullback e s hs x x

end Trefoil.LatticeIsometry
