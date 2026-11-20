import Trefoil.Arithmetic
import Trefoil.LatticeEmbedding

/-!
# The explicit plumbing in Section 3A

The weights are given in surgery order. Integral Gram entries use alternating
signs for adjacent core classes, so each adjacent pairing is `-1`.
The geometric theorem realizing a framed linear chain is applied separately.
-/

namespace Trefoil.Section3APlumbing

open Trefoil.LatticeEmbedding
open scoped BigOperators

def plumbingWeights (m : ℕ) : List ℤ :=
  List.replicate (m - 1) 2 ++ [4, 6, 2, 2, 3]

theorem plumbing_fraction (m : ℕ) (hm : 1 ≤ m) :
    Arithmetic.minusPair (plumbingWeights m) =
      (104 * (m : ℤ) + 37, 104 * (m : ℤ) + 37 - 104) := by
  rw [plumbingWeights, Arithmetic.plumbing_pair]
  have hcast : ((m - 1 : ℕ) : ℤ) = (m : ℤ) - 1 := by omega
  rw [hcast]
  apply Prod.ext <;> simp <;> ring

def plumbingRank (m : ℕ) : ℕ := (m - 1) + 5

@[simp] theorem plumbingWeights_length (m : ℕ) :
    (plumbingWeights m).length = plumbingRank m := by
  simp [plumbingWeights, plumbingRank]

abbrev PlumbingIndex (m : ℕ) := Fin (plumbingRank m)

abbrev JointIndex (m : ℕ) := PlumbingIndex m ⊕ Fin 4

theorem joint_card (m : ℕ) (hm : 1 ≤ m) :
    Fintype.card (JointIndex m) = m + 8 := by
  simp [plumbingRank]
  omega

def plumbingWeight (m : ℕ) (i : PlumbingIndex m) : ℤ :=
  (plumbingWeights m)[i.val]'(by simpa only [plumbingWeights_length] using i.isLt)

def longVertex (m : ℕ) (i : Fin (m - 1)) : PlumbingIndex m :=
  ⟨i.val, by unfold plumbingRank; omega⟩

def tailVertex (m : ℕ) (i : Fin 5) : PlumbingIndex m :=
  ⟨(m - 1) + i.val, by unfold plumbingRank; omega⟩

@[simp] theorem weight_longVertex (m : ℕ) (i : Fin (m - 1)) :
    plumbingWeight m (longVertex m i) = 2 := by
  unfold plumbingWeight plumbingWeights
  rw [List.getElem_append_left (by simp [longVertex])]
  simp

private def tailWeight : Fin 5 → ℤ
  | 0 => 4
  | 1 => 6
  | 2 => 2
  | 3 => 2
  | 4 => 3

@[simp] theorem weight_tailVertex (m : ℕ) (i : Fin 5) :
    plumbingWeight m (tailVertex m i) = tailWeight i := by
  unfold plumbingWeight plumbingWeights
  rw [List.getElem_append_right (by simp [tailVertex])]
  fin_cases i <;> simp [tailVertex, tailWeight]

theorem plumbingWeight_ge_two (m : ℕ) (i : PlumbingIndex m) :
    2 ≤ plumbingWeight m i := by
  by_cases hi : i.val < m - 1
  · let j : Fin (m - 1) := ⟨i.val, hi⟩
    have he : i = longVertex m j := Fin.ext rfl
    rw [he, weight_longVertex]
  · let j : Fin 5 := ⟨i.val - (m - 1), by
      have h := i.isLt
      unfold plumbingRank at h
      omega⟩
    have he : i = tailVertex m j := Fin.ext (by
      change i.val = m - 1 + (i.val - (m - 1))
      omega)
    rw [he, weight_tailVertex]
    have ht : ∀ k : Fin 5, 2 ≤ tailWeight k := by decide
    exact ht j

def pathGram {n : ℕ} (weight : Fin n → ℤ) (i j : Fin n) : ℤ :=
  if i = j then weight i
  else if i.val + 1 = j.val ∨ j.val + 1 = i.val then -1 else 0

def plumbingGram (m : ℕ) : PlumbingIndex m → PlumbingIndex m → ℤ :=
  pathGram (plumbingWeight m)

def chainGram (weights : List ℤ) : Fin weights.length → Fin weights.length → ℤ :=
  pathGram (fun i => weights[i])

theorem chainGram_plumbing (m : ℕ) (i j : PlumbingIndex m) :
    chainGram (plumbingWeights m) (Fin.cast (plumbingWeights_length m).symm i)
      (Fin.cast (plumbingWeights_length m).symm j) = plumbingGram m i j := by
  simp [chainGram, plumbingGram, pathGram, Fin.ext_iff, plumbingWeight]

theorem pathGram_symm {n : ℕ} (weight : Fin n → ℤ) (i j : Fin n) :
    pathGram weight i j = pathGram weight j i := by
  by_cases hij : i = j
  · subst j
    rfl
  · simp [pathGram, hij, Ne.symm hij, or_comm]

def jointGram (m : ℕ) (owensGram : Fin 4 → Fin 4 → ℤ) :
    JointIndex m → JointIndex m → ℤ
  | .inl i, .inl j => plumbingGram m i j
  | .inr i, .inr j => owensGram i j
  | _, _ => 0

def owensRoot (i : Fin 2) : Fin 4 :=
  ⟨i.val, by omega⟩

def plumbingA (m : ℕ) : JointIndex m := .inl (tailVertex m 0)

def plumbingB (m : ℕ) : JointIndex m := .inl (tailVertex m 1)

def plumbingC (m : ℕ) : JointIndex m := .inl (tailVertex m 4)

def jointRoot (m : ℕ) : RootIndex m → JointIndex m
  | .inl i => .inl (longVertex m i)
  | .inr (.inl i) => .inl (tailVertex m ⟨2 + i.val, by omega⟩)
  | .inr (.inr i) => .inr (owensRoot i)

@[simp] theorem longVertex_val (m : ℕ) (i : Fin (m - 1)) :
    (longVertex m i).val = i.val := rfl

@[simp] theorem tailVertex_val (m : ℕ) (i : Fin 5) :
    (tailVertex m i).val = (m - 1) + i.val := rfl

@[simp] theorem owensRoot_val (i : Fin 2) : (owensRoot i).val = i.val := rfl

@[simp] theorem longVertex_eq_iff (m : ℕ) (i j : Fin (m - 1)) :
    longVertex m i = longVertex m j ↔ i = j := by
  simp [Fin.ext_iff, longVertex]

@[simp] theorem tailVertex_eq_iff (m : ℕ) (i j : Fin 5) :
    tailVertex m i = tailVertex m j ↔ i = j := by
  simp [Fin.ext_iff, tailVertex]

@[simp] theorem longVertex_ne_tailVertex (m : ℕ) (i : Fin (m - 1)) (j : Fin 5) :
    longVertex m i ≠ tailVertex m j := by
  have hi := i.isLt
  simp only [ne_eq, Fin.ext_iff, longVertex, tailVertex]
  omega

@[simp] theorem tailVertex_ne_longVertex (m : ℕ) (i : Fin (m - 1)) (j : Fin 5) :
    tailVertex m j ≠ longVertex m i :=
  Ne.symm (longVertex_ne_tailVertex m i j)

def selectedIndex (m : ℕ) : Option (RootIndex m) → JointIndex m
  | none => plumbingB m
  | some r => jointRoot m r

theorem selectedIndex_injective (m : ℕ) : Function.Injective (selectedIndex m) := by
  intro r s h
  rcases r with _ | (i | i | i) <;> rcases s with _ | (j | j | j)
  all_goals simp [selectedIndex, jointRoot, plumbingB, Fin.ext_iff] at h ⊢
  all_goals first | exact h | contradiction | omega

theorem jointGram_root (m : ℕ) (owensGram : Fin 4 → Fin 4 → ℤ)
    (howens : ∀ i j : Fin 2, owensGram (owensRoot i) (owensRoot j) =
      if i = j then 2 else 0) (r s : RootIndex m) :
    jointGram m owensGram (jointRoot m r) (jointRoot m s) = rootGram r s := by
  rcases r with i | i | i <;> rcases s with j | j | j
  · simp [jointGram, jointRoot, plumbingGram, pathGram, rootGram]
  · have hi := i.isLt
    fin_cases j <;>
      simp [jointGram, jointRoot, plumbingGram, pathGram, rootGram] <;>
      omega
  · simp [jointGram, jointRoot, rootGram]
  · have hj := j.isLt
    fin_cases i <;>
      simp [jointGram, jointRoot, plumbingGram, pathGram, rootGram] <;>
      omega
  · fin_cases i <;> fin_cases j <;>
      norm_num [jointGram, jointRoot, plumbingGram, pathGram, rootGram,
        Fin.ext_iff, tailWeight, Nat.add_assoc]
  · simp [jointGram, jointRoot, rootGram]
  · simp [jointGram, jointRoot, rootGram]
  · simp [jointGram, jointRoot, rootGram]
  · simpa [jointGram, jointRoot, rootGram] using howens i j

@[simp] theorem jointGram_AA (m : ℕ) (owensGram : Fin 4 → Fin 4 → ℤ) :
    jointGram m owensGram (plumbingA m) (plumbingA m) = 4 := by
  simp [jointGram, plumbingA, plumbingGram, pathGram, tailWeight]

@[simp] theorem jointGram_BB (m : ℕ) (owensGram : Fin 4 → Fin 4 → ℤ) :
    jointGram m owensGram (plumbingB m) (plumbingB m) = 6 := by
  simp [jointGram, plumbingB, plumbingGram, pathGram, tailWeight]

@[simp] theorem jointGram_CC (m : ℕ) (owensGram : Fin 4 → Fin 4 → ℤ) :
    jointGram m owensGram (plumbingC m) (plumbingC m) = 3 := by
  simp [jointGram, plumbingC, plumbingGram, pathGram, tailWeight]

@[simp] theorem jointGram_AB (m : ℕ) (owensGram : Fin 4 → Fin 4 → ℤ) :
    jointGram m owensGram (plumbingA m) (plumbingB m) = -1 := by
  simp [jointGram, plumbingA, plumbingB, plumbingGram, pathGram,
    Fin.ext_iff, Nat.add_assoc]

@[simp] theorem jointGram_AC (m : ℕ) (owensGram : Fin 4 → Fin 4 → ℤ) :
    jointGram m owensGram (plumbingA m) (plumbingC m) = 0 := by
  simp [jointGram, plumbingA, plumbingC, plumbingGram, pathGram,
    Fin.ext_iff, Nat.add_assoc]

@[simp] theorem jointGram_BC (m : ℕ) (owensGram : Fin 4 → Fin 4 → ℤ) :
    jointGram m owensGram (plumbingB m) (plumbingC m) = 0 := by
  simp [jointGram, plumbingB, plumbingC, plumbingGram, pathGram,
    Fin.ext_iff, Nat.add_assoc]

theorem jointGram_A_root (m : ℕ) (hm : 1 ≤ m) (owensGram : Fin 4 → Fin 4 → ℤ)
    (r : RootIndex m) :
    jointGram m owensGram (plumbingA m) (jointRoot m r) = aRootPairing r := by
  rcases r with i | i | i
  · have hi := i.isLt
    simp [jointGram, jointRoot, plumbingA, plumbingGram, pathGram, aRootPairing]
    have h : (m - 1 + 1 = i.val ∨ i.val + 1 = m - 1) ↔ i.val + 2 = m := by
      omega
    simp only [h]
  · fin_cases i <;> simp [jointGram, jointRoot, plumbingA, plumbingGram,
      pathGram, aRootPairing, Fin.ext_iff, Nat.add_assoc]
  · simp [jointGram, jointRoot, plumbingA, aRootPairing]

theorem jointGram_B_root (m : ℕ) (owensGram : Fin 4 → Fin 4 → ℤ)
    (r : RootIndex m) :
    jointGram m owensGram (plumbingB m) (jointRoot m r) = bRootPairing r := by
  rcases r with i | i | i
  · have hi := i.isLt
    simp [jointGram, jointRoot, plumbingB, plumbingGram, pathGram, bRootPairing]
    omega
  · fin_cases i <;> simp [jointGram, jointRoot, plumbingB, plumbingGram,
      pathGram, bRootPairing, Fin.ext_iff, Nat.add_assoc]
  · simp [jointGram, jointRoot, plumbingB, bRootPairing]

theorem jointGram_C_root (m : ℕ) (owensGram : Fin 4 → Fin 4 → ℤ)
    (r : RootIndex m) :
    jointGram m owensGram (plumbingC m) (jointRoot m r) = cRootPairing r := by
  rcases r with i | i | i
  · have hi := i.isLt
    simp [jointGram, jointRoot, plumbingC, plumbingGram, pathGram, cRootPairing]
    omega
  · fin_cases i <;> simp [jointGram, jointRoot, plumbingC, plumbingGram,
      pathGram, cRootPairing, Fin.ext_iff, Nat.add_assoc]
  · simp [jointGram, jointRoot, plumbingC, cRootPairing]

/-- Evaluate the tridiagonal integral form in a coordinate vector. -/
def pathQuad {n : ℕ} (w x : Fin n → ℤ) : ℤ :=
  ∑ i, ∑ j, x i * pathGram w i j * x j

private theorem pathGram_succ_succ {n : ℕ} (w : Fin (n + 1) → ℤ) (i j : Fin n) :
    pathGram w i.succ j.succ = pathGram (w ∘ Fin.succ) i j := by
  simp [pathGram]

private theorem first_path_row {n : ℕ} (w x : Fin (n + 2) → ℤ) :
    (∑ j : Fin (n + 1), x 0 * pathGram w 0 j.succ * x j.succ) =
      -(x 0 * x (Fin.succ (0 : Fin (n + 1)))) := by
  have hentry (j : Fin (n + 1)) :
      pathGram w 0 j.succ = if j = 0 then -1 else 0 := by
    have hne : (0 : Fin (n + 2)) ≠ j.succ := by
      intro h
      have hv := congrArg Fin.val h
      simp at hv
    have he :
        ((0 : Fin (n + 2)).val + 1 = j.succ.val ∨
          j.succ.val + 1 = (0 : Fin (n + 2)).val) ↔ j = 0 := by
      simp only [Fin.ext_iff, Fin.val_zero, Fin.val_succ, Nat.zero_add]
      omega
    simp only [pathGram, if_neg hne, he]
  simp_rw [hentry]
  rw [Finset.sum_eq_single (0 : Fin (n + 1))]
  · simp
  · intro j _ hj
    simp [hj]
  · simp

private theorem pathQuad_succ {n : ℕ} (w x : Fin (n + 2) → ℤ) :
    pathQuad w x =
      w 0 * x 0 ^ 2 - 2 * x 0 * x (Fin.succ (0 : Fin (n + 1))) +
        pathQuad (w ∘ Fin.succ) (x ∘ Fin.succ) := by
  have hrow (i : Fin (n + 1)) :
      (∑ j : Fin (n + 2), x i.succ * pathGram w i.succ j * x j) =
        x i.succ * pathGram w i.succ 0 * x 0 +
          ∑ j : Fin (n + 1), x i.succ * pathGram (w ∘ Fin.succ) i j * x j.succ := by
    rw [Fin.sum_univ_succ]
    simp only [pathGram_succ_succ]
  have hcol :
      (∑ i : Fin (n + 1), x i.succ * pathGram w i.succ 0 * x 0) =
        -(x 0 * x (Fin.succ (0 : Fin (n + 1)))) := by
    rw [← first_path_row w x]
    apply Finset.sum_congr rfl
    intro i _
    rw [pathGram_symm w i.succ 0]
    ring
  unfold pathQuad
  rw [Fin.sum_univ_succ (f := fun i => ∑ j, x i * pathGram w i j * x j)]
  simp_rw [hrow]
  rw [Finset.sum_add_distrib, hcol]
  rw [Fin.sum_univ_succ (f := fun j => x 0 * pathGram w 0 j * x j),
    first_path_row]
  have h0 : pathGram w 0 0 = w 0 := by simp [pathGram]
  rw [h0]
  simp only [Function.comp_apply]
  ring

/-- Completing the square on the leading edge bounds the form below by
the square at the first vertex. Equality forces every coordinate to vanish. -/
private theorem pathQuad_first_bound {n : ℕ} (w x : Fin (n + 1) → ℤ)
    (hw : ∀ i, 2 ≤ w i) :
    x 0 ^ 2 ≤ pathQuad w x ∧ (pathQuad w x = x 0 ^ 2 → x = 0) := by
  induction n with
  | zero =>
      have hw0 := hw 0
      have hid : pathQuad w x - x 0 ^ 2 = (w 0 - 1) * x 0 ^ 2 := by
        simp [pathQuad, pathGram]
        ring
      have hwpos : 0 < w 0 - 1 := by omega
      constructor
      · have hn := mul_nonneg hwpos.le (sq_nonneg (x 0))
        linarith only [hid, hn]
      · intro he
        have hp : (w 0 - 1) * x 0 ^ 2 = 0 := by linarith only [hid, he]
        have hx : x 0 = 0 :=
          pow_eq_zero ((mul_eq_zero.mp hp).resolve_left (ne_of_gt hwpos))
        funext i
        rw [show i = 0 from Fin.ext (by
          have hi := i.isLt
          omega)]
        exact hx
  | succ n ih =>
      let x₁ := x (Fin.succ (0 : Fin (n + 1)))
      let q₁ := pathQuad (w ∘ Fin.succ) (x ∘ Fin.succ)
      have ht := ih (w ∘ Fin.succ) (x ∘ Fin.succ) (fun i => hw i.succ)
      have hid : pathQuad w x - x 0 ^ 2 =
          (w 0 - 2) * x 0 ^ 2 + (x 0 - x₁) ^ 2 + (q₁ - x₁ ^ 2) := by
        rw [pathQuad_succ]
        dsimp [x₁, q₁]
        ring
      have hw0 := hw 0
      have ha := mul_nonneg (by omega : 0 ≤ w 0 - 2) (sq_nonneg (x 0))
      have hb := sq_nonneg (x 0 - x₁)
      have hc : x₁ ^ 2 ≤ q₁ := ht.1
      constructor
      · linarith only [hid, ha, hb, hc]
      · intro he
        have hq : q₁ = x₁ ^ 2 := by linarith only [hid, he, ha, hb, hc]
        have htail : x ∘ Fin.succ = 0 := ht.2 hq
        have hx₁ : x₁ = 0 := congrFun htail 0
        have hsq : (x 0 - x₁) ^ 2 = 0 := by linarith only [hid, he, ha, hq, hb]
        have hfirst : x 0 = 0 := by
          simpa [hx₁] using (pow_eq_zero hsq : x 0 - x₁ = 0)
        funext i
        refine Fin.cases hfirst (fun j => ?_) i
        exact congrFun htail j

theorem pathGram_positiveDefinite {n : ℕ} (w : Fin (n + 1) → ℤ)
    (hw : ∀ i, 2 ≤ w i) (x : Fin (n + 1) → ℤ) (hx : x ≠ 0) :
    0 < ∑ i, ∑ j, x i * pathGram w i j * x j := by
  change 0 < pathQuad w x
  have hb := pathQuad_first_bound w x hw
  by_contra! hnon
  apply hx
  apply hb.2
  linarith only [hnon, hb.1, sq_nonneg (x 0)]

theorem plumbing_positiveDefinite (m : ℕ) (x : PlumbingIndex m → ℤ) (hx : x ≠ 0) :
    0 < ∑ i, ∑ j, x i * plumbingGram m i j * x j :=
  pathGram_positiveDefinite (plumbingWeight m) (plumbingWeight_ge_two m) x hx

private theorem pathGram_zero_succ {n : ℕ} (w : Fin (n + 2) → ℤ) (j : Fin (n + 1)) :
    pathGram w 0 j.succ = if j = 0 then -1 else 0 := by
  have hne : (0 : Fin (n + 2)) ≠ j.succ := (Fin.succ_ne_zero j).symm
  have he :
      ((0 : Fin (n + 2)).val + 1 = j.succ.val ∨
        j.succ.val + 1 = (0 : Fin (n + 2)).val) ↔ j = 0 := by
    simp only [Fin.ext_iff, Fin.val_zero, Fin.val_succ, Nat.zero_add]
    omega
  simp only [pathGram, if_neg hne, he]

private theorem pathGram_det_succ_succ {n : ℕ} (w : Fin (n + 2) → ℤ) :
    Matrix.det (pathGram w) =
      w 0 * Matrix.det (pathGram (w ∘ (Fin.succ : Fin (n + 1) → Fin (n + 2)))) -
        Matrix.det (pathGram (w ∘ Fin.succ ∘ (Fin.succ : Fin n → Fin (n + 1)))) := by
  let M : Matrix (Fin (n + 2)) (Fin (n + 2)) ℤ := pathGram w
  let N := M.submatrix Fin.succ (Fin.succ (0 : Fin (n + 1))).succAbove
  have hdbl : N.submatrix Fin.succ Fin.succ =
      pathGram (w ∘ Fin.succ ∘ (Fin.succ : Fin n → Fin (n + 1))) := by
    ext i j
    simp [N, M, Matrix.submatrix_apply, pathGram_succ_succ]
    rfl
  have hcol (i : Fin (n + 1)) : N i 0 = if i = 0 then -1 else 0 := by
    change pathGram w i.succ ((Fin.succ (0 : Fin (n + 1))).succAbove 0) = _
    rw [Fin.succ_succAbove_zero, pathGram_symm]
    exact pathGram_zero_succ w i
  have hN : N.det = -Matrix.det
      (pathGram (w ∘ Fin.succ ∘ (Fin.succ : Fin n → Fin (n + 1)))) := by
    rw [Matrix.det_succ_column_zero, Finset.sum_eq_single (0 : Fin (n + 1))]
    · simp [hcol, hdbl]
    · intro i _ hi
      simp [hcol, hi]
    · simp
  have hM : M.submatrix Fin.succ Fin.succ =
      pathGram (w ∘ (Fin.succ : Fin (n + 1) → Fin (n + 2))) := by
    ext i j
    exact pathGram_succ_succ w i j
  change M.det = _
  rw [Matrix.det_succ_row_zero, Fin.sum_univ_succ]
  have hrow (j : Fin (n + 1)) : M 0 j.succ = if j = 0 then -1 else 0 :=
    pathGram_zero_succ w j
  have h0 : M 0 0 = w 0 := by simp [M, pathGram]
  rw [Finset.sum_eq_single (0 : Fin (n + 1))]
  · have hentry : M 0 (1 : Fin (n + 2)) = -1 := by simpa using hrow 0
    simp [h0, hentry, hM, ← hN, N, sub_eq_add_neg]
  · intro j _ hj
    simp [hrow, hj]
  · simp

private theorem chainGram_cons_cons_det (a b : ℤ) (ws : List ℤ) :
    Matrix.det (chainGram (a :: b :: ws)) =
      a * Matrix.det (chainGram (b :: ws)) - Matrix.det (chainGram ws) := by
  exact pathGram_det_succ_succ (fun i => (a :: b :: ws)[i])

theorem chainGram_det (ws : List ℤ) :
    Matrix.det (chainGram ws) = (Arithmetic.minusPair ws).1 := by
  suffices h :
      Matrix.det (chainGram ws) = (Arithmetic.minusPair ws).1 ∧
        (match ws with | [] => 0 | _ :: ts => Matrix.det (chainGram ts)) =
          (Arithmetic.minusPair ws).2 from h.1
  induction ws with
  | nil => simp [Arithmetic.minusPair]
  | cons a ws ih =>
    constructor
    · cases ws with
      | nil => simp [chainGram, pathGram, Arithmetic.minusPair]
      | cons b ws =>
        have hminor : Matrix.det (chainGram ws) = (Arithmetic.minusPair (b :: ws)).2 := ih.2
        rw [chainGram_cons_cons_det, ih.1, hminor]
        rfl
    · exact ih.1

theorem plumbing_det (m : ℕ) (hm : 1 ≤ m) :
    Matrix.det (plumbingGram m) = 104 * (m : ℤ) + 37 := by
  have h :
      Matrix.submatrix (chainGram (plumbingWeights m))
        (finCongr (plumbingWeights_length m).symm)
        (finCongr (plumbingWeights_length m).symm) = plumbingGram m := by
    ext i j
    exact chainGram_plumbing m i j
  rw [← h, Matrix.det_submatrix_equiv_self, chainGram_det, plumbing_fraction m hm]

theorem joint_det (m : ℕ) (hm : 1 ≤ m) (owensGram : Fin 4 → Fin 4 → ℤ) :
    Matrix.det (jointGram m owensGram) = (104 * (m : ℤ) + 37) * Matrix.det owensGram := by
  have h : jointGram m owensGram = Matrix.fromBlocks (plumbingGram m) 0 0 owensGram := by
    ext i j
    cases i <;> cases j <;> rfl
  rw [h, Matrix.det_fromBlocks_zero₂₁, plumbing_det m hm]

end Trefoil.Section3APlumbing
