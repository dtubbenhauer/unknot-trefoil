import Trefoil.LatticeEmbedding
import Trefoil.LatticeExtraction

/-!
# Odd joint-basis determinant and the selected plumbing columns

The odd determinant of a full integral basis gives independence modulo two
for every injectively selected family of columns. The constructor below
uses that fact to supply the independence field of the literal plumbing
embedding; the caller supplies only the basis matrix and its Gram equations.
-/

namespace Trefoil.LatticeOddBasis

open scoped BigOperators
open Trefoil.LatticeEmbedding Trefoil.LatticeSupports

/-- Restrict the modulo-two independent joint basis to any injectively
selected family of columns. -/
theorem selected_columns_independent_mod_two
    {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℤ) (hodd : Odd M.det)
    (choose : κ → ι) (hchoose : Function.Injective choose) :
    LinearIndependent (ZMod 2)
      (fun r => fun j => (M.col (choose r) j : ZMod 2)) := by
  simpa [Function.comp_def, Matrix.col, Matrix.map_apply] using
    (LatticeBasics.odd_det_columns_independent_mod_two M hodd).comp choose hchoose

/-- Build the literal plumbing embedding from an odd-determinant joint basis.
The selected column indexed by `none` is the square-six vertex `B`; the
columns indexed by `some r` are the square-two plumbing roots. Independence
is proved, not supplied as an assumption. -/
def of_odd_basis {m : ℕ}
    (M : Matrix (Ambient m) (Ambient m) ℤ) (hodd : Odd M.det)
    (choose : Option (RootIndex m) → Ambient m)
    (hchoose : Function.Injective choose)
    (A C : Vector m)
    (hroot : ∀ r s,
      dot (M.col (choose (some r))) (M.col (choose (some s))) = rootGram r s)
    (hA : ∑ j, A j ^ 2 = 4)
    (hB : ∑ j, M.col (choose none) j ^ 2 = 6)
    (hC : ∑ j, C j ^ 2 = 3)
    (hAB : dot A (M.col (choose none)) = -1)
    (hAC : dot A C = 0)
    (hBC : dot (M.col (choose none)) C = 0)
    (hAr : ∀ r, dot A (M.col (choose (some r))) = aRootPairing r)
    (hBr : ∀ r, dot (M.col (choose none)) (M.col (choose (some r))) = bRootPairing r)
    (hCr : ∀ r, dot C (M.col (choose (some r))) = cRootPairing r) :
    Embedding m where
  root := fun r => M.col (choose (some r))
  A := A
  B := M.col (choose none)
  C := C
  root_pairing := hroot
  normA := hA
  normB := hB
  normC := hC
  pairingAB := hAB
  pairingAC := hAC
  pairingBC := hBC
  pairingA_root := hAr
  pairingB_root := hBr
  pairingC_root := hCr
  independent := by
    convert selected_columns_independent_mod_two M hodd choose hchoose using 1
    funext r j
    cases r <;> rfl

/-- The Section 3A obstruction stated directly for selected columns of an
odd-determinant integral joint basis. All coordinate and parity reductions
are internal theorems. -/
theorem no_odd_basis_embedding {m : ℕ} (hm : m = 4 ∨ 6 ≤ m)
    (M : Matrix (Ambient m) (Ambient m) ℤ) (hodd : Odd M.det)
    (choose : Option (RootIndex m) → Ambient m)
    (hchoose : Function.Injective choose)
    (A C : Vector m)
    (hroot : ∀ r s,
      dot (M.col (choose (some r))) (M.col (choose (some s))) = rootGram r s)
    (hA : ∑ j, A j ^ 2 = 4)
    (hB : ∑ j, M.col (choose none) j ^ 2 = 6)
    (hC : ∑ j, C j ^ 2 = 3)
    (hAB : dot A (M.col (choose none)) = -1)
    (hAC : dot A C = 0)
    (hBC : dot (M.col (choose none)) C = 0)
    (hAr : ∀ r, dot A (M.col (choose (some r))) = aRootPairing r)
    (hBr : ∀ r, dot (M.col (choose none)) (M.col (choose (some r))) = bRootPairing r)
    (hCr : ∀ r, dot C (M.col (choose (some r))) = cRootPairing r) : False := by
  exact LatticeExtraction.no_embedding hm
    (of_odd_basis M hodd choose hchoose A C hroot hA hB hC hAB hAC hBC hAr hBr hCr)

end Trefoil.LatticeOddBasis
