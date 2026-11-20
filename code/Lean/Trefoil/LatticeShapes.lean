import Trefoil.LatticeEmbedding
import Trefoil.LatticeSigns
import Trefoil.LatticeCoordinates
import Mathlib.Tactic.FinCases

/-!
# Heavy-vector shapes from actual root pairings

The coordinate patterns are consequences of successive differences. The
parameters below are selected from the given vector, rather than supplied
as a normal-form hypothesis.
-/

namespace Trefoil.LatticeShapes

open Trefoil.LatticeEmbedding Trefoil.LatticeCoordinates Trefoil.LatticeSigns

private def finiteSequence {n : ℕ} (f : Fin n → ℤ) (i : ℕ) : ℤ :=
  if hi : i < n then f ⟨i, hi⟩ else 0

private theorem finiteSequence_apply {n : ℕ} (f : Fin n → ℤ)
    (i : ℕ) (hi : i < n) : finiteSequence f i = f ⟨i, hi⟩ := by
  simp [finiteSequence, hi]

/-- A finite chain whose successive differences vanish has constant entries. -/
theorem finite_constant {n : ℕ} (hn : 0 < n) (f : Fin n → ℤ)
    (hd : ∀ (i : ℕ) (hi : i+1 < n),
      f ⟨i, by omega⟩ - f ⟨i+1, hi⟩ = 0) :
    ∀ j, f j = f ⟨0, hn⟩ := by
  intro j
  have hseq : ∀ i < n-1, finiteSequence f i - finiteSequence f (i+1) = 0 := by
    intro i hi
    rw [finiteSequence_apply f i (by omega),
      finiteSequence_apply f (i+1) (by omega)]
    exact hd i (by omega)
  have hc := constant_of_zero_differences (n-1) (finiteSequence f)
    hseq j.val (by have := j.isLt; omega)
  simpa only [finiteSequence_apply f j.val j.isLt,
    finiteSequence_apply f 0 hn] using hc

/-- A finite chain with a final pairing of minus one has one final unit jump. -/
theorem finite_last_jump {n : ℕ} (hn : 2 ≤ n) (f : Fin n → ℤ)
    (hd : ∀ (i : ℕ) (hi : i+1 < n),
      f ⟨i, by omega⟩ - f ⟨i+1, hi⟩ = if i+2 = n then -1 else 0) :
    ∀ j, f j = if j.val+1 = n then f ⟨0, by omega⟩ + 1
      else f ⟨0, by omega⟩ := by
  have hseq : ∀ i, i+1 < n-1 →
      finiteSequence f i - finiteSequence f (i+1) = 0 := by
    intro i hi
    rw [finiteSequence_apply f i (by omega),
      finiteSequence_apply f (i+1) (by omega)]
    have hstep := hd i (by omega)
    simpa only [if_neg (show i+2 ≠ n by omega)] using hstep
  have hlast : finiteSequence f (n-1-1) - finiteSequence f (n-1) = -1 := by
    have hstep := hd (n-1-1) (by omega)
    have hi : n-1-1+1 = n-1 := by omega
    have he : n-1-1+2 = n := by omega
    rw [finiteSequence_apply f (n-1-1) (by omega),
      finiteSequence_apply f (n-1) (by omega)]
    simpa only [hi, if_pos he] using hstep
  intro j
  have hc := last_jump_of_differences (n-1) (by omega)
    (finiteSequence f) hseq hlast j.val (by have := j.isLt; omega)
  have hj : j.val = n-1 ↔ j.val+1 = n := by omega
  simpa only [finiteSequence_apply f j.val j.isLt,
    finiteSequence_apply f 0 (by omega), hj] using hc

/-- The two isolated roots force equality on each two-coordinate block. -/
theorem isolated_blocks_constant {m : ℕ} (x : Blocks m → ℤ)
    (h0 : x (leftEndpoint (.inr (.inr 0))) -
      x (rightEndpoint (.inr (.inr 0))) = 0)
    (h1 : x (leftEndpoint (.inr (.inr 1))) -
      x (rightEndpoint (.inr (.inr 1))) = 0) :
    (∀ i : Fin 2, x (.inr (.inr (.inl i))) = x (.inr (.inr (.inl 0)))) ∧
    (∀ i : Fin 2, x (.inr (.inr (.inr (.inl i)))) =
      x (.inr (.inr (.inr (.inl 0))))) := by
  change x (.inr (.inr (.inl 0))) - x (.inr (.inr (.inl 1))) = 0 at h0
  change x (.inr (.inr (.inr (.inl 0)))) -
    x (.inr (.inr (.inr (.inl 1)))) = 0 at h1
  constructor <;> intro i <;> fin_cases i <;> simp_all <;> omega

/-- The root pairings of the first heavy vertex determine its canonical row. -/
theorem extract_rowA {m : ℕ} (hm : 4 ≤ m) (x : Blocks m → ℤ)
    (h : ∀ r, x (leftEndpoint r) - x (rightEndpoint r) = aRootPairing r) :
    ∃ a z r s t, x = rowA m a z r s t := by
  have hlong : ∀ i : Fin m, x (.inl i) =
      if i.val+1 = m then x (.inl ⟨0, by omega⟩) + 1
      else x (.inl ⟨0, by omega⟩) := by
    apply finite_last_jump (by omega) (fun i => x (.inl i))
    intro i hi
    simpa only [leftEndpoint, rightEndpoint, aRootPairing] using
      h (.inl ⟨i, by omega⟩)
  have ht0 := h (.inr (.inl (0 : Fin 2)))
  have ht1 := h (.inr (.inl (1 : Fin 2)))
  change x (.inr (.inl 0)) - x (.inr (.inl 1)) = 0 at ht0
  change x (.inr (.inl 1)) - x (.inr (.inl 2)) = 0 at ht1
  have hp := isolated_blocks_constant x
    (h (.inr (.inr 0))) (h (.inr (.inr 1)))
  refine ⟨x (.inl ⟨0, by omega⟩), x (.inr (.inl 0)),
    x (.inr (.inr (.inl 0))), x (.inr (.inr (.inr (.inl 0)))),
    x (.inr (.inr (.inr (.inr ())))), ?_⟩
  funext u
  rcases u with i | (i | (i | (i | u)))
  · simpa only [rowA] using hlong i
  · fin_cases i <;> simp_all [rowA] <;> omega
  · exact hp.1 i
  · exact hp.2 i
  · cases u; rfl

/-- The root pairings of the second heavy vertex determine its canonical row. -/
theorem extract_rowB {m : ℕ} (hm : 4 ≤ m) (x : Blocks m → ℤ)
    (h : ∀ r, x (leftEndpoint r) - x (rightEndpoint r) = bRootPairing r) :
    ∃ b g r s t, x = rowB m b g r s t := by
  have hlong : ∀ i : Fin m, x (.inl i) = x (.inl ⟨0, by omega⟩) := by
    apply finite_constant (by omega) (fun i => x (.inl i))
    intro i hi
    simpa only [leftEndpoint, rightEndpoint, bRootPairing] using
      h (.inl ⟨i, by omega⟩)
  have ht0 := h (.inr (.inl (0 : Fin 2)))
  have ht1 := h (.inr (.inl (1 : Fin 2)))
  change x (.inr (.inl 0)) - x (.inr (.inl 1)) = -1 at ht0
  change x (.inr (.inl 1)) - x (.inr (.inl 2)) = 0 at ht1
  have hp := isolated_blocks_constant x
    (h (.inr (.inr 0))) (h (.inr (.inr 1)))
  refine ⟨x (.inl ⟨0, by omega⟩), x (.inr (.inl 1)),
    x (.inr (.inr (.inl 0))), x (.inr (.inr (.inr (.inl 0)))),
    x (.inr (.inr (.inr (.inr ())))), ?_⟩
  funext u
  rcases u with i | (i | (i | (i | u)))
  · exact hlong i
  · fin_cases i <;> simp [rowB] <;> omega
  · exact hp.1 i
  · exact hp.2 i
  · cases u; rfl

/-- The root pairings of the third heavy vertex determine its canonical row. -/
theorem extract_rowC {m : ℕ} (hm : 4 ≤ m) (x : Blocks m → ℤ)
    (h : ∀ r, x (leftEndpoint r) - x (rightEndpoint r) = cRootPairing r) :
    ∃ c ell r s t, x = rowC m c ell r s t := by
  have hlong : ∀ i : Fin m, x (.inl i) = x (.inl ⟨0, by omega⟩) := by
    apply finite_constant (by omega) (fun i => x (.inl i))
    intro i hi
    simpa only [leftEndpoint, rightEndpoint, cRootPairing] using
      h (.inl ⟨i, by omega⟩)
  have ht0 := h (.inr (.inl (0 : Fin 2)))
  have ht1 := h (.inr (.inl (1 : Fin 2)))
  change x (.inr (.inl 0)) - x (.inr (.inl 1)) = 0 at ht0
  change x (.inr (.inl 1)) - x (.inr (.inl 2)) = -1 at ht1
  have hp := isolated_blocks_constant x
    (h (.inr (.inr 0))) (h (.inr (.inr 1)))
  refine ⟨x (.inl ⟨0, by omega⟩), x (.inr (.inl 0)),
    x (.inr (.inr (.inl 0))), x (.inr (.inr (.inr (.inl 0)))),
    x (.inr (.inr (.inr (.inr ())))), ?_⟩
  funext u
  rcases u with i | (i | (i | (i | u)))
  · exact hlong i
  · fin_cases i <;> simp [rowC] <;> omega
  · exact hp.1 i
  · exact hp.2 i
  · cases u; rfl

end Trefoil.LatticeShapes
