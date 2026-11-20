import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega
import Trefoil.LatticeBasics
import Trefoil.LatticePath

/-!
# From integral Gram data to support intersections

For integral vectors with distinct supports of size two, orthogonality is
equivalent to disjointness. A nonzero pairing means that the supports meet in
exactly one coordinate. These are the hypotheses used by `LatticePath`.

The final two lemmas connect the distinct-support hypothesis with reduction
modulo two. They apply to vectors whose coordinates are zero or units, the
property proved for norm-two vectors in `LatticeBasics`.
-/

namespace Trefoil.LatticeSupports

open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The support of an integral vector in a finite diagonal lattice. -/
def support (u : ι → ℤ) : Finset ι := Finset.univ.filter (fun i => u i ≠ 0)

omit [DecidableEq ι] in
@[simp] theorem mem_support (u : ι → ℤ) (i : ι) : i ∈ support u ↔ u i ≠ 0 := by
  simp [support]

/-- The standard diagonal lattice pairing. -/
def dot (u v : ι → ℤ) : ℤ := ∑ i, u i * v i

theorem dot_eq_sum_inter (u v : ι → ℤ) :
    dot u v = ∑ i ∈ support u ∩ support v, u i * v i := by
  unfold dot
  symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro i _ hni
  by_cases hu : u i = 0
  · simp [hu]
  · have hv : v i = 0 := by
      by_contra hv
      exact hni (by simp [hu,hv])
    simp [hv]

theorem dot_eq_zero_of_disjoint (u v : ι → ℤ)
    (h : Disjoint (support u) (support v)) : dot u v = 0 := by
  rw [dot_eq_sum_inter, Finset.disjoint_iff_inter_eq_empty.mp h]
  simp

theorem dot_ne_zero_of_inter_card_one (u v : ι → ℤ)
    (h : (support u ∩ support v).card = 1) : dot u v ≠ 0 := by
  obtain ⟨i,hi⟩ := Finset.card_eq_one.mp h
  have him : i ∈ support u ∩ support v := by rw [hi]; simp
  have hu : u i ≠ 0 := (mem_support u i).mp (Finset.mem_inter.mp him).1
  have hv : v i ≠ 0 := (mem_support v i).mp (Finset.mem_inter.mp him).2
  rw [dot_eq_sum_inter, hi]
  simpa using mul_ne_zero hu hv

private theorem inter_card_ne_two (u v : ι → ℤ)
    (hu : (support u).card = 2) (hv : (support v).card = 2)
    (hne : support u ≠ support v) : (support u ∩ support v).card ≠ 2 := by
  intro h
  have hleft : support u ∩ support v = support u :=
    Finset.eq_of_subset_of_card_le Finset.inter_subset_left (by omega)
  have hright : support u ∩ support v = support v :=
    Finset.eq_of_subset_of_card_le Finset.inter_subset_right (by omega)
  exact hne (hleft.symm.trans hright)

/-- With repeated supports excluded, zero pairing is exactly disjointness. -/
theorem dot_zero_iff_disjoint (u v : ι → ℤ)
    (hu : (support u).card = 2) (hv : (support v).card = 2)
    (hne : support u ≠ support v) :
    dot u v = 0 ↔ Disjoint (support u) (support v) := by
  constructor
  · intro hdot
    have hle : (support u ∩ support v).card ≤ 2 := by
      have := Finset.card_le_card (Finset.inter_subset_left : support u ∩ support v ⊆ support u)
      omega
    have hnotTwo := inter_card_ne_two u v hu hv hne
    have hnotOne : (support u ∩ support v).card ≠ 1 := by
      intro h
      exact dot_ne_zero_of_inter_card_one u v h hdot
    have hzero : (support u ∩ support v).card = 0 := by omega
    exact Finset.disjoint_iff_inter_eq_empty.mpr (Finset.card_eq_zero.mp hzero)
  · exact dot_eq_zero_of_disjoint u v

/-- A nonzero Gram entry between two distinct norm-two supports makes a
single shared coordinate. No numerical or finite-sampling premise is used. -/
theorem inter_card_one_of_dot_ne_zero (u v : ι → ℤ)
    (hu : (support u).card = 2) (hv : (support v).card = 2)
    (hne : support u ≠ support v) (hdot : dot u v ≠ 0) :
    (support u ∩ support v).card = 1 := by
  have hle : (support u ∩ support v).card ≤ 2 := by
    have := Finset.card_le_card (Finset.inter_subset_left : support u ∩ support v ⊆ support u)
    omega
  have hnotTwo := inter_card_ne_two u v hu hv hne
  have hnotZero : (support u ∩ support v).card ≠ 0 := by
    intro h
    apply hdot
    apply dot_eq_zero_of_disjoint
    exact Finset.disjoint_iff_inter_eq_empty.mpr (Finset.card_eq_zero.mp h)
  omega

omit [DecidableEq ι] in
/-- Unit-coordinate vectors with the same support have the same reduction
modulo two, regardless of their individual signs. -/
theorem modTwo_eq_of_support_eq (u v : ι → ℤ)
    (hu : ∀ i, u i = -1 ∨ u i = 0 ∨ u i = 1)
    (hv : ∀ i, v i = -1 ∨ v i = 0 ∨ v i = 1)
    (hs : support u = support v) :
    (fun i => (u i : ZMod 2)) = (fun i => (v i : ZMod 2)) := by
  funext i
  have hm : (u i ≠ 0) ↔ (v i ≠ 0) := by
    rw [← mem_support u i, ← mem_support v i, hs]
  rcases hu i with hu' | hu' | hu' <;>
    rcases hv i with hv' | hv' | hv' <;>
    norm_num [hu',hv'] at hm ⊢
  all_goals decide

omit [DecidableEq ι] in
/-- Distinct reduced columns therefore have distinct supports. -/
theorem support_ne_of_modTwo_ne (u v : ι → ℤ)
    (hu : ∀ i, u i = -1 ∨ u i = 0 ∨ u i = 1)
    (hv : ∀ i, v i = -1 ∨ v i = 0 ∨ v i = 1)
    (h : (fun i => (u i : ZMod 2)) ≠ (fun i => (v i : ZMod 2))) :
    support u ≠ support v := by
  intro hs
  exact h (modTwo_eq_of_support_eq u v hu hv hs)

/-- Actual integral norm-two vectors with the chain Gram data and distinct
mod-two reductions have an injective ordered path of supports.

The distinct-reduction premise is a necessary consequence of the joint
basis's mod-two linear independence. The theorem proves the support-path
reduction itself; signed coordinate normalization and combining different
chains are separate steps. -/
theorem norm_two_chain_support_path (n : ℕ) (v : ℕ → ι → ℤ)
    (hnorm : ∀ i < n+2, ∑ k, v i k ^ 2 = 2)
    (hred : ∀ i j, i < n+2 → j < n+2 → i ≠ j →
      (fun k => (v i k : ZMod 2)) ≠ (fun k => (v j k : ZMod 2)))
    (hadj : ∀ i, i+1 < n+2 → dot (v i) (v (i+1)) = -1)
    (hfar : ∀ i j, i+1 < j → j < n+2 → dot (v i) (v j) = 0) :
    ∃ p : ℕ → ι,
      (∀ i < n+2, support (v i) = {p i, p (i+1)}) ∧
      (∀ i j, i ≤ n+2 → j ≤ n+2 → p i = p j → i = j) := by
  have hcard : ∀ i < n+2, (support (v i)).card = 2 := by
    intro i hi
    exact Trefoil.LatticeBasics.norm_two_support_card (v i) (hnorm i hi)
  have hne : ∀ i j, i < n+2 → j < n+2 → i ≠ j →
      support (v i) ≠ support (v j) := by
    intro i j hi hj hij
    apply support_ne_of_modTwo_ne (v i) (v j)
    · exact fun k => Trefoil.LatticeBasics.norm_two_coordinate (v i) (hnorm i hi) k
    · exact fun k => Trefoil.LatticeBasics.norm_two_coordinate (v j) (hnorm j hj) k
    · exact hred i j hi hj hij
  apply Trefoil.LatticePath.supports_form_path n (fun i => support (v i)) hcard
  · intro i hi
    apply inter_card_one_of_dot_ne_zero (v i) (v (i+1))
      (hcard i (by omega)) (hcard (i+1) hi)
      (hne i (i+1) (by omega) hi (by omega))
    rw [hadj i hi]
    norm_num
  · intro i j hij hj
    apply (dot_zero_iff_disjoint (v i) (v j) (hcard i (by omega)) (hcard j hj)
      (hne i j (by omega) hj (by omega))).mp
    exact hfar i j hij hj

end Trefoil.LatticeSupports
