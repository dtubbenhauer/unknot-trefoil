import Mathlib.Data.Finset.Card
import Mathlib.Logic.Function.Basic
import Mathlib.Tactic.IntervalCases
import Lean.Elab.Tactic.Omega

/-!
# The support-path argument

The hypotheses describe the supports of distinct integral norm-two vectors in
a chain: each support has size two, adjacent supports meet once, and all
nonadjacent supports are disjoint.  This file proves the combinatorial path
step, independently of any topological reference.
-/

namespace Trefoil.LatticePath

/-- Extend a support path of at least two edges by its uniquely fresh endpoint. -/
theorem fresh_endpoint {ι : Type*} [DecidableEq ι]
    (e : ℕ → Finset ι) (v : ℕ → ι) (s : Finset ι) (k : ℕ)
    (hk : 2 ≤ k)
    (hpath : ∀ i < k, e i = {v i, v (i+1)})
    (hs : s.card = 2)
    (hadj : (e (k-1) ∩ s).card = 1)
    (hfar : ∀ i, i+1 < k → Disjoint (e i) s) :
    ∃ w, s = {v k, w} ∧ ∀ j ≤ k, w ≠ v j := by
  have hlast : k-1 < k := by omega
  have hprev : k-2 < k := by omega
  have hprevfar : k-2+1 < k := by omega
  have hlastidx : k-1+1 = k := by omega
  have hprevidx : k-2+1 = k-1 := by omega
  have hne : (e (k-1) ∩ s).Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨x, hx⟩ := hne
  obtain ⟨hxold, hxs⟩ := Finset.mem_inter.mp hx
  have hxs' : x = v (k-1) ∨ x = v k := by
    rw [hpath (k-1) hlast] at hxold
    simpa [hlastidx] using hxold
  have hvk : v k ∈ s := by
    rcases hxs' with hx | hx
    · have hvmem : v (k-1) ∈ e (k-2) := by
        rw [hpath (k-2) hprev]
        simp [hprevidx]
      exact False.elim ((Finset.disjoint_left.mp (hfar (k-2) hprevfar))
        hvmem (hx ▸ hxs))
    · exact hx ▸ hxs
  obtain ⟨a, b, hab, hsab⟩ := Finset.card_eq_two.mp hs
  have hv : v k = a ∨ v k = b := by simpa [hsab] using hvk
  have hpair : ∃ w, s = {v k, w} ∧ w ≠ v k := by
    rcases hv with hv | hv
    · subst a
      exact ⟨b, hsab, Ne.symm hab⟩
    · subst b
      exact ⟨a, by simpa [Finset.pair_comm] using hsab, hab⟩
  obtain ⟨w, hsw, hw⟩ := hpair
  refine ⟨w, hsw, ?_⟩
  intro j hj heq
  by_cases hjk : j = k
  · subst j
    exact hw heq
  have hjlt : j < k := by omega
  have hwmem : w ∈ s := by simp [hsw]
  by_cases hjlast : j = k-1
  · have hvj : v j ∈ e (k-2) := by
      rw [hpath (k-2) hprev, hjlast]
      simp [hprevidx]
    exact (Finset.disjoint_left.mp (hfar (k-2) hprevfar)) hvj (heq ▸ hwmem)
  · have hjfar : j+1 < k := by omega
    have hvj : v j ∈ e j := by rw [hpath j hjlt]; simp
    exact (Finset.disjoint_left.mp (hfar j hjfar)) hvj (heq ▸ hwmem)

private theorem pair_of_mem {ι : Type*} [DecidableEq ι]
    {s : Finset ι} (hs : s.card = 2) {b : ι} (hb : b ∈ s) :
    ∃ a, s = {b,a} ∧ b ≠ a := by
  obtain ⟨x,y,hxy,h⟩ := Finset.card_eq_two.mp hs
  have hb' : b = x ∨ b = y := by simpa [h] using hb
  rcases hb' with hb' | hb'
  · subst x
    exact ⟨y,h,hxy⟩
  · subst y
    exact ⟨x,by simpa [Finset.pair_comm] using h,Ne.symm hxy⟩

private theorem two_edges {ι : Type*} [DecidableEq ι]
    (e : ℕ → Finset ι) (h0 : (e 0).card = 2) (h1 : (e 1).card = 2)
    (h01 : (e 0 ∩ e 1).card = 1) :
    ∃ v : ℕ → ι,
      (∀ i < 2, e i = {v i, v (i+1)}) ∧
      (∀ i j, i ≤ 2 → j ≤ 2 → v i = v j → i = j) := by
  obtain ⟨b,hb⟩ := Finset.card_eq_one.mp h01
  have hbm : b ∈ e 0 ∩ e 1 := by rw [hb]; simp
  obtain ⟨hb0,hb1⟩ := Finset.mem_inter.mp hbm
  obtain ⟨a,he0,hba⟩ := pair_of_mem h0 hb0
  obtain ⟨c,he1,hbc⟩ := pair_of_mem h1 hb1
  have hac : a ≠ c := by
    intro hac
    have ha : a ∈ e 0 ∩ e 1 := by simp [he0,he1,hac]
    have hab : a = b := by simpa [hb] using ha
    exact hba hab.symm
  let v : ℕ → ι := fun i => if i = 0 then a else if i = 1 then b else c
  refine ⟨v,?_,?_⟩
  · intro i hi
    interval_cases i <;> simp [v,he0,he1,Finset.pair_comm]
  · intro i j hi hj hij
    interval_cases i <;> interval_cases j <;>
      simp_all [v,Ne.symm hba,Ne.symm hbc,Ne.symm hac]

/-- Distinct two-coordinate supports with chain intersections form an actual
ordered simple path.  This is uniform in the length, not a finite case check. -/
theorem supports_form_path {ι : Type*} [DecidableEq ι]
    (n : ℕ) (e : ℕ → Finset ι)
    (hcard : ∀ i < n+2, (e i).card = 2)
    (hadj : ∀ i, i+1 < n+2 → (e i ∩ e (i+1)).card = 1)
    (hfar : ∀ i j, i+1 < j → j < n+2 → Disjoint (e i) (e j)) :
    ∃ v : ℕ → ι,
      (∀ i < n+2, e i = {v i, v (i+1)}) ∧
      (∀ i j, i ≤ n+2 → j ≤ n+2 → v i = v j → i = j) := by
  induction n generalizing e with
  | zero =>
      exact two_edges e (hcard 0 (by omega)) (hcard 1 (by omega))
        (hadj 0 (by omega))
  | succ n ih =>
      obtain ⟨v,hpath,hinj⟩ := ih e
        (fun i hi => hcard i (by omega))
        (fun i hi => hadj i (by omega))
        (fun i j hij hj => hfar i j hij (by omega))
      have hAdj : (e (n+2-1) ∩ e (n+2)).card = 1 := by
        have hx : n+2-1+1 = n+2 := by omega
        simpa [hx] using hadj (n+2-1) (by omega)
      obtain ⟨w,hew,hw⟩ := fresh_endpoint e v (e (n+2)) (n+2)
        (by omega) hpath (hcard (n+2) (by omega)) hAdj
        (fun i hi => hfar i (n+2) hi (by omega))
      let v' : ℕ → ι := Function.update v (n+3) w
      refine ⟨v',?_,?_⟩
      · intro i hi
        by_cases hold : i < n+2
        · have hi' : i ≠ n+3 := by omega
          have hi1' : i+1 ≠ n+3 := by omega
          have hi2' : i ≠ n+2 := by omega
          simpa [v',Function.update,hi',hi1',hi2'] using hpath i hold
        · have hi' : i = n+2 := by omega
          subst i
          have hne : n+2 ≠ n+3 := by omega
          simpa [v',Function.update,hne,Nat.add_assoc] using hew
      · intro i j hi hj hij
        by_cases hi' : i = n+3
        · subst i
          by_cases hj' : j = n+3
          · exact hj'.symm
          · have hjold : j ≤ n+2 := by omega
            have heq : w = v j := by simpa [v',Function.update,hj'] using hij
            exact False.elim (hw j hjold heq)
        · by_cases hj' : j = n+3
          · subst j
            have hiold : i ≤ n+2 := by omega
            have heq : v i = w := by simpa [v',Function.update,hi'] using hij
            exact False.elim (hw i hiold heq.symm)
          · have hiold : i ≤ n+2 := by omega
            have hjold : j ≤ n+2 := by omega
            apply hinj i j hiold hjold
            simpa [v',Function.update,hi',hj'] using hij

end Trefoil.LatticePath
