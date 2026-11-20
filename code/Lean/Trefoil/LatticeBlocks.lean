import Trefoil.LatticeEmbedding
import Trefoil.LatticeSigns
import Mathlib.Data.Fintype.EquivFin

/-!
# A global signed coordinate frame from the plumbing Gram matrix

The four root chains have disjoint supports. Their ordered support paths use
exactly all but one ambient coordinate. Extending by that remaining coordinate
produces a signed coordinate frame; its existence is proved from the literal
integral Gram data.
-/

namespace Trefoil.LatticeBlocks

open scoped BigOperators
open Trefoil.LatticeEmbedding Trefoil.LatticeSupports

/-- A signed coordinate frame derived from the integral embedding. -/
structure Frame {m : ℕ} (E : Embedding m) where
  coord : Blocks m ≃ Ambient m
  sign : Blocks m → ℤ
  sign_sq : ∀ j, sign j ^ 2 = 1
  root_support : ∀ r, support (E.root r) =
    {coord (leftEndpoint r), coord (rightEndpoint r)}
  pairing : ∀ r x, dot x (E.root r) =
    sign (leftEndpoint r) * x (coord (leftEndpoint r)) -
    sign (rightEndpoint r) * x (coord (rightEndpoint r))

/-- The coordinate type before adding the unused coordinate. -/
abbrev Used (m : ℕ) := Fin m ⊕ (Fin 3 ⊕ (Fin 2 ⊕ Fin 2))

/-- Reassociate the final singleton without changing the four blocks. -/
def splitLast (m : ℕ) : Blocks m ≃ Used m ⊕ Unit where
  toFun
    | .inl i => .inl (.inl i)
    | .inr (.inl i) => .inl (.inr (.inl i))
    | .inr (.inr (.inl i)) => .inl (.inr (.inr (.inl i)))
    | .inr (.inr (.inr (.inl i))) => .inl (.inr (.inr (.inr i)))
    | .inr (.inr (.inr (.inr u))) => .inr u
  invFun
    | .inl (.inl i) => .inl i
    | .inl (.inr (.inl i)) => .inr (.inl i)
    | .inl (.inr (.inr (.inl i))) => .inr (.inr (.inl i))
    | .inl (.inr (.inr (.inr i))) => .inr (.inr (.inr (.inl i)))
    | .inr u => .inr (.inr (.inr (.inr u)))
  left_inv := by rintro (i | i | i | i | u) <;> rfl
  right_inv := by rintro ((i | i | i | i) | u) <;> rfl

private theorem extend_injection {α β : Type*} [Fintype α] [Fintype β]
    (f : α → β) (hf : Function.Injective f)
    (hc : Fintype.card β = Fintype.card α + 1) :
    ∃ e : α ⊕ Unit ≃ β, ∀ a, e (.inl a) = f a := by
  classical
  have hns : ¬ Function.Surjective f := by
    intro hs
    have := Fintype.card_le_of_surjective f hs
    omega
  obtain ⟨b,hb⟩ : ∃ b, ∀ a, f a ≠ b := by
    simpa only [Function.Surjective, not_forall, not_exists] using hns
  let g : α ⊕ Unit → β := Sum.elim f (fun _ => b)
  have hg : Function.Injective g := by
    rintro (a | u) (a' | u') h
    · exact congrArg Sum.inl (hf h)
    · exact False.elim (hb a h)
    · exact False.elim (hb a' h.symm)
    · exact congrArg Sum.inr (Subsingleton.elim _ _)
  have hgcard : Fintype.card (α ⊕ Unit) = Fintype.card β := by
    simp only [Fintype.card_sum, Fintype.card_unit]
    omega
  let e := Equiv.ofBijective g ((Fintype.bijective_iff_injective_and_card g).mpr ⟨hg,hgcard⟩)
  exact ⟨e, fun _ => rfl⟩

/-- Every vertex on a nonempty support path belongs to a root support. -/
private theorem path_covered {m k : ℕ} (hk : 1 ≤ k) (E : Embedding m)
    (r : Fin k → RootIndex m) (p : ℕ → Ambient m)
    (hs : ∀ i, support (E.root (r i)) = {p i.val, p (i.val+1)})
    (j : ℕ) (hj : j ≤ k) :
    ∃ i : Fin k, p j ∈ support (E.root (r i)) := by
  by_cases hlt : j < k
  · refine ⟨⟨j,hlt⟩,?_⟩
    rw [hs]
    simp
  · have heq : j = k := by omega
    have hlast : k-1 < k := by omega
    refine ⟨⟨k-1,hlast⟩,?_⟩
    rw [hs]
    have hstep : k-1+1 = j := by omega
    simp [hstep]

/-- Orthogonality of two root families separates their entire support paths. -/
private theorem paths_separated {m k l : ℕ} (hk : 1 ≤ k) (hl : 1 ≤ l)
    (E : Embedding m) (r : Fin k → RootIndex m) (s : Fin l → RootIndex m)
    (p q : ℕ → Ambient m)
    (hp : ∀ i, support (E.root (r i)) = {p i.val, p (i.val+1)})
    (hq : ∀ i, support (E.root (s i)) = {q i.val, q (i.val+1)})
    (hne : ∀ i j, r i ≠ s j) (hz : ∀ i j, rootGram (r i) (s j) = 0)
    (a b : ℕ) (ha : a ≤ k) (hb : b ≤ l) : p a ≠ q b := by
  intro heq
  obtain ⟨i,hi⟩ := path_covered hk E r p hp a ha
  obtain ⟨j,hj⟩ := path_covered hl E s q hq b hb
  have hd := root_supports_disjoint E (hne i j) (hz i j)
  exact (Finset.disjoint_left.mp hd) hi (heq ▸ hj)

private theorem sum_injective {α β γ : Type*} (f : α → γ) (g : β → γ)
    (hf : Function.Injective f) (hg : Function.Injective g)
    (hfg : ∀ a b, f a ≠ g b) : Function.Injective (Sum.elim f g) := by
  rintro (a | b) (a' | b') h
  · exact congrArg Sum.inl (hf h)
  · exact False.elim (hfg a b' h)
  · exact False.elim (hfg a' b h.symm)
  · exact congrArg Sum.inr (hg h)

/-- Finite-index form of the support-path and signed normalization lemmas. -/
private theorem finite_signed_chain {ι : Type*} [Fintype ι] [DecidableEq ι]
    (k : ℕ) (hk : 1 ≤ k) (v : Fin k → ι → ℤ)
    (hn : ∀ i, ∑ a, v i a ^ 2 = 2)
    (hred : Function.Injective (fun i => fun a => (v i a : ZMod 2)))
    (hadj : ∀ i j, i.val+1 = j.val → dot (v i) (v j) = -1)
    (hfar : ∀ i j, i.val+1 < j.val → dot (v i) (v j) = 0) :
    ∃ p : ℕ → ι, ∃ eps : ℕ → ℤ,
      (∀ i, support (v i) = {p i.val, p (i.val+1)}) ∧
      (∀ i j, i ≤ k → j ≤ k → p i = p j → i = j) ∧
      (∀ j ≤ k, eps j ^ 2 = 1) ∧
      (∀ i x, dot x (v i) = eps i.val * x (p i.val) -
        eps (i.val+1) * x (p (i.val+1))) := by
  classical
  let w : ℕ → ι → ℤ := fun i => if h : i < k then v ⟨i,h⟩ else 0
  have hw (i : Fin k) : w i.val = v i := by simp [w,i.isLt]
  have hwn : ∀ i < k, ∑ a, w i a ^ 2 = 2 := by
    intro i hi
    simpa [w,hi] using hn ⟨i,hi⟩
  have hwa : ∀ i, i+1 < k → dot (w i) (w (i+1)) = -1 := by
    intro i hi
    have hi0 : i < k := by omega
    simpa [w,hi0,hi] using hadj ⟨i,hi0⟩ ⟨i+1,hi⟩ rfl
  obtain ⟨p,hps,hpi⟩ : ∃ p : ℕ → ι,
      (∀ i < k, support (w i) = {p i,p (i+1)}) ∧
      (∀ i j, i ≤ k → j ≤ k → p i = p j → i = j) := by
    by_cases hk1 : k = 1
    · obtain ⟨a,b,hab,hs⟩ := LatticeBasics.norm_two_support_pair (w 0) (hwn 0 (by omega))
      let p : ℕ → ι := fun i => if i = 0 then a else b
      refine ⟨p,?_,?_⟩
      · intro i hi
        have hi0 : i = 0 := by omega
        subst i
        simpa [support,p] using hs
      · intro i j hi hj heq
        by_cases hi0 : i = 0 <;> by_cases hj0 : j = 0
        · omega
        · have : a = b := by simpa [p,hi0,hj0] using heq
          exact False.elim (hab this)
        · have : b = a := by simpa [p,hi0,hj0] using heq
          exact False.elim (hab this.symm)
        · omega
    · have heq : k-2+2 = k := by omega
      have h := norm_two_chain_support_path (k-2) w
      simp only [heq] at h
      apply h
      · simpa only [heq] using hwn
      · intro i j hi hj hij he
        have hi' : i < k := by omega
        have hj' : j < k := by omega
        have hr : (⟨i,hi'⟩ : Fin k) = ⟨j,hj'⟩ := hred (by simpa [w,hi',hj'] using he)
        exact hij (congrArg Fin.val hr)
      · simpa only [heq] using hwa
      · intro i j hij hj
        have hi' : i < k := by omega
        have hj' : j < k := by omega
        simpa [w,hi',hj'] using hfar ⟨i,hi'⟩ ⟨j,hj'⟩ hij
  obtain ⟨eps,hu,hd⟩ := LatticeSigns.signed_chain k hk w p hwn hps hpi hwa
  refine ⟨p,eps,?_,hpi,hu,?_⟩
  · intro i
    simpa only [hw] using hps i.val i.isLt
  · intro i x
    simpa only [hw] using hd i.val i.isLt x

private structure PathData {m : ℕ} (E : Embedding m) (k : ℕ)
    (r : Fin k → RootIndex m) where
  p : ℕ → Ambient m
  eps : ℕ → ℤ
  support : ∀ i, LatticeSupports.support (E.root (r i)) = {p i.val,p (i.val+1)}
  injective : ∀ i j, i ≤ k → j ≤ k → p i = p j → i = j
  unit : ∀ j ≤ k, eps j ^ 2 = 1
  pairing : ∀ i x, dot x (E.root (r i)) =
    eps i.val * x (p i.val) - eps (i.val+1) * x (p (i.val+1))

private theorem root_path {m k : ℕ} (E : Embedding m) (hk : 1 ≤ k)
    (r : Fin k → RootIndex m) (hr : Function.Injective r)
    (ha : ∀ i j, i.val+1 = j.val → rootGram (r i) (r j) = -1)
    (hf : ∀ i j, i.val+1 < j.val → rootGram (r i) (r j) = 0) :
    Nonempty (PathData E k r) := by
  obtain ⟨p,eps,hs,hi,hu,hd⟩ := finite_signed_chain k hk (fun i => E.root (r i))
    (fun i => root_norm E (r i))
    (fun _ _ h => hr (root_mod_two_injective E h))
    (fun i j h => (E.root_pairing (r i) (r j)).trans (ha i j h))
    (fun i j h => (E.root_pairing (r i) (r j)).trans (hf i j h))
  exact ⟨⟨p,eps,hs,hi,hu,hd⟩⟩

private def longRoot {m : ℕ} (i : Fin (m-1)) : RootIndex m := .inl i
private def tripleRoot {m : ℕ} (i : Fin 2) : RootIndex m := .inr (.inl i)
private def pairRoot {m : ℕ} (t : Fin 2) (_ : Fin 1) : RootIndex m := .inr (.inr t)

private theorem long_path {m : ℕ} (hm : 4 ≤ m) (E : Embedding m) :
    Nonempty (PathData E (m-1) longRoot) := by
  apply root_path E (by omega) longRoot (by intro i j h; exact Sum.inl.inj h)
  · intro i j hij
    have hne : i ≠ j := by intro h; have := congrArg Fin.val h; omega
    simp [longRoot,rootGram,hne,hij]
  · intro i j hij
    have hne : i ≠ j := by intro h; have := congrArg Fin.val h; omega
    have hforward : ¬ i.val+1 = j.val := by omega
    have hback : ¬ j.val+1 = i.val := by omega
    simp [longRoot,rootGram,hne,hforward,hback]

private theorem triple_path {m : ℕ} (E : Embedding m) :
    Nonempty (PathData E 2 tripleRoot) := by
  apply root_path E (by omega) tripleRoot
    (by intro i j h; exact Sum.inl.inj (Sum.inr.inj h))
  · intro i j hij
    have hne : i ≠ j := by intro h; have := congrArg Fin.val h; omega
    simp [tripleRoot,rootGram,hne]
  · intro i j hij
    have := j.isLt
    omega

private theorem pair_path {m : ℕ} (E : Embedding m) (t : Fin 2) :
    Nonempty (PathData E 1 (pairRoot t)) := by
  apply root_path E (by omega) (pairRoot t)
    (by intro i j _; exact Subsingleton.elim _ _)
  · intro i j hij
    have := i.isLt
    have := j.isLt
    omega
  · intro i j hij
    have := j.isLt
    omega

/-- The plumbing Gram data determine a global signed coordinate frame.
This is a conclusion of the lattice lemmas, not an additional embedding input. -/
theorem exists_frame {m : ℕ} (hm : 4 ≤ m) (E : Embedding m) :
    Nonempty (Frame E) := by
  classical
  obtain ⟨L⟩ := long_path hm E
  obtain ⟨T⟩ := triple_path E
  obtain ⟨P⟩ := pair_path E 0
  obtain ⟨Q⟩ := pair_path E 1
  have hLT := paths_separated (by omega : 1 ≤ m-1) (by decide : 1 ≤ 2) E
    longRoot tripleRoot L.p T.p L.support T.support
    (by intro i j; simp [longRoot,tripleRoot])
    (by intro i j; simp [longRoot,tripleRoot,rootGram])
  have hLP := paths_separated (by omega : 1 ≤ m-1) (by decide : 1 ≤ 1) E
    longRoot (pairRoot 0) L.p P.p L.support P.support
    (by intro i j; simp [longRoot,pairRoot])
    (by intro i j; simp [longRoot,pairRoot,rootGram])
  have hLQ := paths_separated (by omega : 1 ≤ m-1) (by decide : 1 ≤ 1) E
    longRoot (pairRoot 1) L.p Q.p L.support Q.support
    (by intro i j; simp [longRoot,pairRoot])
    (by intro i j; simp [longRoot,pairRoot,rootGram])
  have hTP := paths_separated (by decide : 1 ≤ 2) (by decide : 1 ≤ 1) E
    tripleRoot (pairRoot 0) T.p P.p T.support P.support
    (by intro i j; simp [tripleRoot,pairRoot])
    (by intro i j; simp [tripleRoot,pairRoot,rootGram])
  have hTQ := paths_separated (by decide : 1 ≤ 2) (by decide : 1 ≤ 1) E
    tripleRoot (pairRoot 1) T.p Q.p T.support Q.support
    (by intro i j; simp [tripleRoot,pairRoot])
    (by intro i j; simp [tripleRoot,pairRoot,rootGram])
  have hPQ := paths_separated (by decide : 1 ≤ 1) (by decide : 1 ≤ 1) E
    (pairRoot 0) (pairRoot 1) P.p Q.p P.support Q.support
    (by intro i j; simp [pairRoot])
    (by intro i j; simp [pairRoot,rootGram])
  let fL : Fin m → Ambient m := fun i => L.p i.val
  let fT : Fin 3 → Ambient m := fun i => T.p i.val
  let fP : Fin 2 → Ambient m := fun i => P.p i.val
  let fQ : Fin 2 → Ambient m := fun i => Q.p i.val
  have hiL : Function.Injective fL := by
    intro i j h
    apply Fin.ext
    exact L.injective i.val j.val (by have := i.isLt; omega) (by have := j.isLt; omega) h
  have hiT : Function.Injective fT := by
    intro i j h
    apply Fin.ext
    exact T.injective i.val j.val (by have := i.isLt; omega) (by have := j.isLt; omega) h
  have hiP : Function.Injective fP := by
    intro i j h
    apply Fin.ext
    exact P.injective i.val j.val (by have := i.isLt; omega) (by have := j.isLt; omega) h
  have hiQ : Function.Injective fQ := by
    intro i j h
    apply Fin.ext
    exact Q.injective i.val j.val (by have := i.isLt; omega) (by have := j.isLt; omega) h
  let f : Used m → Ambient m := Sum.elim fL (Sum.elim fT (Sum.elim fP fQ))
  have hf : Function.Injective f := by
    apply sum_injective fL (Sum.elim fT (Sum.elim fP fQ)) hiL
    · apply sum_injective fT (Sum.elim fP fQ) hiT
      · apply sum_injective fP fQ hiP hiQ
        intro i j
        exact hPQ i.val j.val (by have := i.isLt; omega) (by have := j.isLt; omega)
      · intro i
        rintro (j | j)
        · exact hTP i.val j.val (by have := i.isLt; omega) (by have := j.isLt; omega)
        · exact hTQ i.val j.val (by have := i.isLt; omega) (by have := j.isLt; omega)
    · intro i
      rintro (j | j | j)
      · exact hLT i.val j.val (by have := i.isLt; omega) (by have := j.isLt; omega)
      · exact hLP i.val j.val (by have := i.isLt; omega) (by have := j.isLt; omega)
      · exact hLQ i.val j.val (by have := i.isLt; omega) (by have := j.isLt; omega)
  obtain ⟨e,he⟩ := extend_injection f hf (by
    simp [Ambient,Used,Fintype.card_sum,Nat.add_assoc])
  let coord : Blocks m ≃ Ambient m := (splitLast m).trans e
  let eps : Blocks m → ℤ := Sum.elim (fun i => L.eps i.val)
    (Sum.elim (fun i => T.eps i.val)
      (Sum.elim (fun i => P.eps i.val)
        (Sum.elim (fun i => Q.eps i.val) (fun _ => 1))))
  have hcL (i : Fin m) : coord (.inl i) = L.p i.val := by
    change e (.inl (.inl i)) = L.p i.val
    rw [he]
    rfl
  have hcT (i : Fin 3) : coord (.inr (.inl i)) = T.p i.val := by
    change e (.inl (.inr (.inl i))) = T.p i.val
    rw [he]
    rfl
  have hcP (i : Fin 2) : coord (.inr (.inr (.inl i))) = P.p i.val := by
    change e (.inl (.inr (.inr (.inl i)))) = P.p i.val
    rw [he]
    rfl
  have hcQ (i : Fin 2) : coord (.inr (.inr (.inr (.inl i)))) = Q.p i.val := by
    change e (.inl (.inr (.inr (.inr i)))) = Q.p i.val
    rw [he]
    rfl
  refine ⟨{coord := coord, sign := eps, sign_sq := ?_, root_support := ?_, pairing := ?_}⟩
  · rintro (i | i | i | i | u)
    · exact L.unit i.val (by have := i.isLt; omega)
    · exact T.unit i.val (by have := i.isLt; omega)
    · exact P.unit i.val (by have := i.isLt; omega)
    · exact Q.unit i.val (by have := i.isLt; omega)
    · simp [eps]
  · rintro (i | i | i)
    · simpa [longRoot,leftEndpoint,rightEndpoint,hcL] using L.support i
    · simpa [tripleRoot,leftEndpoint,rightEndpoint,hcT] using T.support i
    · by_cases hi : i.val = 0
      · have hi' : i = 0 := Fin.ext hi
        subst i
        simpa [pairRoot,leftEndpoint,rightEndpoint,hcP] using P.support (0 : Fin 1)
      · have hi' : i = 1 := Fin.ext (by have := i.isLt; omega)
        subst i
        simpa [pairRoot,leftEndpoint,rightEndpoint,hcQ] using Q.support (0 : Fin 1)
  · rintro (i | i | i) x
    · simpa [longRoot,leftEndpoint,rightEndpoint,eps,hcL] using L.pairing i x
    · simpa [tripleRoot,leftEndpoint,rightEndpoint,eps,hcT] using T.pairing i x
    · by_cases hi : i.val = 0
      · have hi' : i = 0 := Fin.ext hi
        subst i
        simpa [pairRoot,leftEndpoint,rightEndpoint,eps,hcP] using P.pairing (0 : Fin 1) x
      · have hi' : i = 1 := Fin.ext (by have := i.isLt; omega)
        subst i
        simpa [pairRoot,leftEndpoint,rightEndpoint,eps,hcQ] using Q.pairing (0 : Fin 1) x

end Trefoil.LatticeBlocks
