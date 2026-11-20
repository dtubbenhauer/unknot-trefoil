import Trefoil.LatticeShapes
import Trefoil.LatticeIsometry
import Trefoil.LatticeFrameParity
import Trefoil.LatticeArithmetic

/-!
# The lattice obstruction before coordinate normalization

The normal form and its parity condition are consequences of the integral
Gram data. In particular they are not additional assumptions in the final
nonembedding theorem.
-/

namespace Trefoil.LatticeExtraction

open scoped BigOperators
open LatticeEmbedding LatticeBlocks LatticeCoordinates LatticeIsometry

/-- Extract the displayed integer coordinates from a signed frame. -/
theorem configuration_of_frame {m : ℕ} (hm : 4 ≤ m) (E : Embedding m)
    (F : Frame E) : Nonempty (LatticeConfiguration (m : ℤ)) := by
  let A := signedPullback F.coord F.sign E.A
  let B := signedPullback F.coord F.sign E.B
  let C := signedPullback F.coord F.sign E.C
  have hA : ∀ r, A (leftEndpoint r) - A (rightEndpoint r) = aRootPairing r := by
    intro r
    exact (F.pairing r E.A).symm.trans (E.pairingA_root r)
  have hB : ∀ r, B (leftEndpoint r) - B (rightEndpoint r) = bRootPairing r := by
    intro r
    exact (F.pairing r E.B).symm.trans (E.pairingB_root r)
  have hC : ∀ r, C (leftEndpoint r) - C (rightEndpoint r) = cRootPairing r := by
    intro r
    exact (F.pairing r E.C).symm.trans (E.pairingC_root r)
  obtain ⟨a,z,rA,sA,tA,hAsh⟩ := LatticeShapes.extract_rowA hm A hA
  obtain ⟨b,g,rB,sB,tB,hBsh⟩ := LatticeShapes.extract_rowB hm B hB
  obtain ⟨c,ell,rC,sC,tC,hCsh⟩ := LatticeShapes.extract_rowC hm C hC
  refine ⟨{
    a := a, b := b, c := c, z := z, g := g, ell := ell
    rA := rA, sA := sA, tA := tA
    rB := rB, sB := sB, tB := tB
    rC := rC, sC := sC, tC := tC
    normA := ?_, normB := ?_, normC := ?_
    pairingAB := ?_, pairingAC := ?_, pairingBC := ?_
    independentB := ?_ }⟩
  · rw [← norm_rowA m (by omega), ← hAsh]
    exact (norm_signedPullback F.coord F.sign F.sign_sq E.A).trans E.normA
  · rw [← norm_rowB m, ← hBsh]
    exact (norm_signedPullback F.coord F.sign F.sign_sq E.B).trans E.normB
  · rw [← norm_rowC m, ← hCsh]
    exact (norm_signedPullback F.coord F.sign F.sign_sq E.C).trans E.normC
  · rw [← pairing_rowAB m (by omega), ← hAsh, ← hBsh]
    exact (dot_signedPullback F.coord F.sign F.sign_sq E.A E.B).trans E.pairingAB
  · rw [← pairing_rowAC m (by omega), ← hAsh, ← hCsh]
    exact (dot_signedPullback F.coord F.sign F.sign_sq E.A E.C).trans E.pairingAC
  · rw [← pairing_rowBC m, ← hBsh, ← hCsh]
    exact (dot_signedPullback F.coord F.sign F.sign_sq E.B E.C).trans E.pairingBC
  · apply LatticeParity.independentB_of_not_mem m b g rB sB tB
    change (fun j => (rowB m b g rB sB tB j : ZMod 2)) ∉ LatticeParity.blockRootSpan m
    rw [← hBsh]
    exact LatticeFrameParity.frame_B_not_mem E F

/-- The Gram equations and modulo-two independence cannot occur in the
diagonal lattice for the parameters covered by Section 3A. No coordinate
normal form or parity conclusion is assumed. -/
theorem no_embedding {m : ℕ} (hm : m = 4 ∨ 6 ≤ m) (E : Embedding m) : False := by
  obtain ⟨F⟩ := exists_frame (by omega) E
  obtain ⟨configuration⟩ := configuration_of_frame (by omega) E F
  exact no_lattice_configuration (by omega) configuration

end Trefoil.LatticeExtraction
