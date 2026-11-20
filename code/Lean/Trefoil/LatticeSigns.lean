import Trefoil.LatticeSupports
import Mathlib.Tactic.Ring

/-!
# Signed normalization of norm-two support paths

The support path is a proved combinatorial object. This file chooses the
coordinate signs from the actual root entries and derives the corresponding
difference formula for pairing an arbitrary vector with a root. No normal
form is supplied as an unexplained input.
-/

namespace Trefoil.LatticeSigns

open scoped BigOperators
open Trefoil.LatticeSupports

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- Restrict a pairing to the support of its second argument. -/
theorem dot_eq_sum_support (x u : ι → ℤ) :
    dot x u = ∑ a ∈ support u, x a * u a := by
  unfold dot
  symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro a _ ha
  have hu : u a = 0 := by simpa using ha
  simp [hu]

/-- Pairing with a vector supported on two distinct coordinates. -/
theorem dot_pair_support (x u : ι → ℤ) (a b : ι) (hab : a ≠ b)
    (hs : support u = {a,b}) :
    dot x u = x a * u a + x b * u b := by
  rw [dot_eq_sum_support, hs]
  simp [hab]

/-- A nonzero entry of an integral norm-two vector is a unit. -/
theorem norm_two_entry_unit (u : ι → ℤ) (hn : ∑ a, u a ^ 2 = 2)
    (a : ι) (ha : a ∈ support u) : u a = -1 ∨ u a = 1 := by
  have hne : u a ≠ 0 := (mem_support u a).mp ha
  rcases Trefoil.LatticeBasics.norm_two_coordinate u hn a with h | h | h
  · exact Or.inl h
  · exact False.elim (hne h)
  · exact Or.inr h

/-- Consecutive roots share exactly the middle coordinate in the path. -/
theorem adjacent_pairing_on_path (k : ℕ) (v : ℕ → ι → ℤ) (p : ℕ → ι)
    (hs : ∀ i < k, support (v i) = {p i, p (i+1)})
    (hinj : ∀ i j, i ≤ k → j ≤ k → p i = p j → i = j)
    (i : ℕ) (hi : i+1 < k) :
    dot (v i) (v (i+1)) = v i (p (i+1)) * v (i+1) (p (i+1)) := by
  have h12 : p (i+1) ≠ p (i+1+1) := by
    intro h
    have := hinj (i+1) (i+1+1) (by omega) (by omega) h
    omega
  have h02 : p (i+1+1) ≠ p i := by
    intro h
    have := hinj (i+1+1) i (by omega) (by omega) h
    omega
  have hz : v i (p (i+1+1)) = 0 := by
    by_contra hz
    have hm : p (i+1+1) ∈ support (v i) := (mem_support _ _).mpr hz
    rw [hs i (by omega)] at hm
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    rcases hm with hm | hm
    · exact h02 hm
    · exact h12 hm.symm
  rw [dot_pair_support (v i) (v (i+1)) (p (i+1)) (p (i+1+1)) h12
    (hs (i+1) hi), hz]
  simp

/-- The chosen signs depend only on the actual path coordinates. -/
def pathSign (v : ℕ → ι → ℤ) (p : ℕ → ι) (j : ℕ) : ℤ :=
  if j = 0 then v 0 (p 0) else -v (j-1) (p j)

/-- Every selected coordinate sign is a unit. -/
theorem pathSign_unit (k : ℕ) (hk : 1 ≤ k) (v : ℕ → ι → ℤ) (p : ℕ → ι)
    (hn : ∀ i < k, ∑ a, v i a ^ 2 = 2)
    (hs : ∀ i < k, support (v i) = {p i, p (i+1)})
    (j : ℕ) (hj : j ≤ k) : pathSign v p j ^ 2 = 1 := by
  by_cases hj0 : j = 0
  · subst j
    have hu := norm_two_entry_unit (v 0) (hn 0 (by omega)) (p 0)
      (by rw [hs 0 (by omega)]; simp)
    rcases hu with hu | hu <;> simp [pathSign, hu]
  · have hjm : j-1 < k := by omega
    have hjpred : j-1+1 = j := by omega
    have hu := norm_two_entry_unit (v (j-1)) (hn (j-1) hjm) (p j)
      (by rw [hs (j-1) hjm, hjpred]; simp)
    rcases hu with hu | hu <;> simp [pathSign, hj0, hu]

/-- With these signs each root has the expected positive left coefficient. -/
theorem pathSign_left (k : ℕ) (v : ℕ → ι → ℤ) (p : ℕ → ι)
    (hn : ∀ i < k, ∑ a, v i a ^ 2 = 2)
    (hs : ∀ i < k, support (v i) = {p i, p (i+1)})
    (hinj : ∀ i j, i ≤ k → j ≤ k → p i = p j → i = j)
    (hadj : ∀ i, i+1 < k → dot (v i) (v (i+1)) = -1)
    (i : ℕ) (hi : i < k) : v i (p i) = pathSign v p i := by
  cases i with
  | zero => simp [pathSign]
  | succ i =>
      have hi' : i+1 < k := by omega
      have hp := adjacent_pairing_on_path k v p hs hinj i hi'
      rw [hadj i hi'] at hp
      have hu := norm_two_entry_unit (v i) (hn i (by omega)) (p (i+1))
        (by rw [hs i (by omega)]; simp)
      rcases hu with hu | hu
      · simp only [hu] at hp
        simp [pathSign]
        omega
      · simp only [hu] at hp
        simp [pathSign]
        omega

omit [Fintype ι] [DecidableEq ι] in
/-- The negative right coefficient is built into the sign choice. -/
theorem pathSign_right (v : ℕ → ι → ℤ) (p : ℕ → ι) (i : ℕ) :
    v i (p (i+1)) = -pathSign v p (i+1) := by
  simp [pathSign]

/-- Signed normalization of a whole path, including the one-root case.
The conclusion is expressed as a pairing formula, so it applies directly
to each heavy plumbing vertex without introducing a new coordinate basis. -/
theorem signed_chain (k : ℕ) (hk : 1 ≤ k)
    (v : ℕ → ι → ℤ) (p : ℕ → ι)
    (hn : ∀ i < k, ∑ a, v i a ^ 2 = 2)
    (hs : ∀ i < k, support (v i) = {p i, p (i+1)})
    (hinj : ∀ i j, i ≤ k → j ≤ k → p i = p j → i = j)
    (hadj : ∀ i, i+1 < k → dot (v i) (v (i+1)) = -1) :
    ∃ eps : ℕ → ℤ,
      (∀ j ≤ k, eps j ^ 2 = 1) ∧
      ∀ i < k, ∀ x : ι → ℤ,
        dot x (v i) = eps i * x (p i) - eps (i+1) * x (p (i+1)) := by
  refine ⟨pathSign v p, pathSign_unit k hk v p hn hs, ?_⟩
  intro i hi x
  have hne : p i ≠ p (i+1) := by
    intro h
    have := hinj i (i+1) (by omega) (by omega) h
    omega
  rw [dot_pair_support x (v i) (p i) (p (i+1)) hne (hs i hi),
    pathSign_left k v p hn hs hinj hadj i hi, pathSign_right v p i]
  ring

/-- Zero pairings along a path make the signed coordinates constant. -/
theorem constant_of_zero_differences (k : ℕ) (c : ℕ → ℤ)
    (hd : ∀ i < k, c i - c (i+1) = 0) :
    ∀ j ≤ k, c j = c 0 := by
  intro j
  induction j with
  | zero => intro _; rfl
  | succ j ih =>
      intro hj
      have hprev := ih (by omega)
      have hstep := hd j (by omega)
      omega

/-- Pairing by minus one only with the last root adds one at the last
coordinate, while all earlier coordinates agree. -/
theorem last_jump_of_differences (k : ℕ) (hk : 1 ≤ k) (c : ℕ → ℤ)
    (hd : ∀ i, i+1 < k → c i - c (i+1) = 0)
    (hlast : c (k-1) - c k = -1) :
    ∀ j ≤ k, c j = if j = k then c 0 + 1 else c 0 := by
  have hconst : ∀ j ≤ k-1, c j = c 0 :=
    constant_of_zero_differences (k-1) c (fun i hi => hd i (by omega))
  intro j hj
  by_cases heq : j = k
  · subst j
    rw [if_pos rfl]
    have := hconst (k-1) (by omega)
    omega
  · simp only [if_neg heq]
    exact hconst j (by omega)

/-- Pairing by minus one only with the first root subtracts one at the first
coordinate, while all later coordinates agree. -/
theorem first_jump_of_differences (k : ℕ) (hk : 1 ≤ k) (c : ℕ → ℤ)
    (hfirst : c 0 - c 1 = -1)
    (hd : ∀ i, 1 ≤ i → i < k → c i - c (i+1) = 0) :
    c 0 = c 1 - 1 ∧ ∀ j, 1 ≤ j → j ≤ k → c j = c 1 := by
  refine ⟨by omega, ?_⟩
  have hconst := constant_of_zero_differences (k-1) (fun i => c (i+1))
    (fun i hi => hd (i+1) (by omega) (by omega))
  intro j hj hjk
  have hpred : j-1+1 = j := by omega
  simpa only [hpred, Nat.zero_add] using hconst (j-1) (by omega)

end Trefoil.LatticeSigns
