import Trefoil.LatticeBlocks
import Trefoil.LatticeParity

/-!
# Modulo-two independence in the derived coordinate frame

The root normal form and the heavy-vertex parity obstruction are consequences
of the original embedding's modulo-two linear independence. Changing coordinate
signs has no effect modulo two.
-/

namespace Trefoil.LatticeFrameParity

open Trefoil.LatticeEmbedding Trefoil.LatticeBlocks Trefoil.LatticeParity

private theorem unit_modTwo {a : ℤ} (ha : a = -1 ∨ a = 0 ∨ a = 1)
    (hne : a ≠ 0) : (a : F₂) = 1 := by
  rcases ha with ha | ha | ha <;> norm_num [ha] at hne ⊢
  decide

/-- Every coordinate sign reduces to one modulo two. -/
theorem frame_sign_modTwo {m : ℕ} (E : Embedding m) (F : Frame E) (j : Blocks m) :
    (F.sign j : F₂) = 1 := by
  have hs := F.sign_sq j
  have hn : F.sign j ≠ 0 := by
    intro h
    rw [h] at hs
    norm_num at hs
  have hsign : F.sign j = -1 ∨ F.sign j = 1 := by
    have hl : -1 ≤ F.sign j := by nlinarith
    have hu : F.sign j ≤ 1 := by nlinarith
    omega
  rcases hsign with h | h <;> norm_num [h]
  decide

/-- The two endpoints of a norm-two root are distinct in the frame. -/
theorem frame_endpoints_ne {m : ℕ} (E : Embedding m) (F : Frame E)
    (r : RootIndex m) : leftEndpoint r ≠ rightEndpoint r := by
  intro h
  have hc := LatticeBasics.norm_two_support_card (E.root r) (root_norm E r)
  change (LatticeSupports.support (E.root r)).card = 2 at hc
  rw [F.root_support r, h] at hc
  simp at hc

/-- Pulling a root back along the frame gives its literal adjacent difference
modulo two. The proof uses the actual integral support and norm. -/
theorem frame_root_modTwo {m : ℕ} (E : Embedding m) (F : Frame E)
    (r : RootIndex m) :
    (fun j => (E.root r (F.coord j) : F₂)) = standardRoot m r := by
  funext j
  have hc := LatticeBasics.norm_two_coordinate (E.root r) (root_norm E r) (F.coord j)
  have hs : E.root r (F.coord j) ≠ 0 ↔ j = leftEndpoint r ∨ j = rightEndpoint r := by
    rw [← LatticeSupports.mem_support, F.root_support]
    simp
  have hne := frame_endpoints_ne E F r
  by_cases hl : j = leftEndpoint r
  · have hv := unit_modTwo hc (hs.mpr (Or.inl hl))
    rw [hv]
    simp [standardRoot, hl, hne]
  · by_cases hr : j = rightEndpoint r
    · have hv := unit_modTwo hc (hs.mpr (Or.inr hr))
      rw [hv]
      norm_num [standardRoot, Pi.single_apply, hl, hr, hne, Ne.symm hne]
      decide
    · have hz : E.root r (F.coord j) = 0 := by
        by_contra h
        exact (hs.mp h).elim hl hr
      simp [hz, standardRoot, hl, hr]

/-- The signed heavy vertex remains outside the norm-two root span. This is
proved from `Embedding.independent` by the bijective coordinate pullback. -/
theorem frame_B_not_mem {m : ℕ} (E : Embedding m) (F : Frame E) :
    (fun j => ((F.sign j * E.B (F.coord j) : ℤ) : F₂)) ∉ blockRootSpan m := by
  let S : Submodule F₂ (Ambient m → F₂) :=
    Submodule.span F₂ (Set.range (fun r : RootIndex m => fun j => (E.root r j : F₂)))
  have hn : (fun j => (E.B j : F₂)) ∉ S := by
    intro hB
    apply E.independent.notMem_span none
    apply Submodule.span_mono ?_ hB
    rintro y ⟨r, rfl⟩
    exact ⟨some r, by simp, rfl⟩
  have htransfer : ∀ x : Blocks m → F₂, x ∈ blockRootSpan m →
      (fun j => x (F.coord.symm j)) ∈ S := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
        rcases hx with ⟨r, rfl⟩
        have heq : (fun j => standardRoot m r (F.coord.symm j)) =
            fun j => (E.root r j : F₂) := by
          funext j
          rw [← frame_root_modTwo E F r]
          simp
        rw [heq]
        exact Submodule.subset_span ⟨r, rfl⟩
    | zero => exact S.zero_mem
    | add x y hx hy ihx ihy => exact S.add_mem ihx ihy
    | smul a x hx ih => exact S.smul_mem a ih
  have hb : (fun j => ((F.sign j * E.B (F.coord j) : ℤ) : F₂)) =
      fun j => (E.B (F.coord j) : F₂) := by
    funext j
    simp only [Int.cast_mul, frame_sign_modTwo, one_mul]
  rw [hb]
  intro hB
  apply hn
  simpa using htransfer (fun j => (E.B (F.coord j) : F₂)) hB

end Trefoil.LatticeFrameParity
