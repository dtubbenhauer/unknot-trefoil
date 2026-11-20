import Mathlib.Tactic.Linarith
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# The integral coordinate obstruction in Section 3A

This file proves the contradiction *after* the norm-two chains have been put in
the displayed signed-coordinate normal form.  Its hypotheses are explicit
integer equations, not an assertion that the paper's obstruction is valid.
The reduction of integral Gram data with modulo-two independence to this
normal form is proved in `LatticeExtraction`; it is not a literature input.
-/

namespace Trefoil

/-- Integer coordinates on the blocks of sizes `m, 3, 2, 2, 1` in Figure 6.
The three rows are the vertices of weights four, six and three. -/
structure LatticeConfiguration (m : ℤ) where
  a : ℤ
  b : ℤ
  c : ℤ
  z : ℤ
  g : ℤ
  ell : ℤ
  rA : ℤ
  sA : ℤ
  tA : ℤ
  rB : ℤ
  sB : ℤ
  tB : ℤ
  rC : ℤ
  sC : ℤ
  tC : ℤ
  normA : m * a^2 + 2*a + 1 + 3*z^2 + 2*rA^2 + 2*sA^2 + tA^2 = 4
  normB : m * b^2 + (g-1)^2 + 2*g^2 + 2*rB^2 + 2*sB^2 + tB^2 = 6
  normC : m * c^2 + 2*ell^2 + (ell+1)^2 + 2*rC^2 + 2*sC^2 + tC^2 = 3
  pairingAB : (m*a+1)*b + z*(3*g-1) + 2*(rA*rB+sA*sB) + tA*tB = -1
  pairingAC : (m*a+1)*c + z*(3*ell+1) + 2*(rA*rC+sA*sC) + tA*tC = 0
  pairingBC : m*b*c + 3*g*ell + g-ell + 2*(rB*rC+sB*sC) + tB*tC = 0
  independentB : ¬ ((m*b)%2 = 0 ∧ (3*g-1)%2 = 0 ∧ tB%2 = 0)

private theorem integer_square_ge_one {x : ℤ} (h : x ≠ 0) : 1 ≤ x^2 := by
  have hx : x ≤ -1 ∨ 1 ≤ x := by omega
  rcases hx with hx | hx
  · nlinarith [sq_nonneg (x+1)]
  · nlinarith [sq_nonneg (x-1)]

private theorem integer_zero_of_square_lt_one {x : ℤ} (h : x^2 < 1) : x = 0 := by
  by_contra hn
  have := integer_square_ge_one hn
  omega

private theorem integer_square_le_two {x : ℤ} (h : x^2 ≤ 2) :
    x = -1 ∨ x = 0 ∨ x = 1 := by
  have hl : -1 ≤ x := by
    by_contra hn
    have hx : x ≤ -2 := by omega
    nlinarith [sq_nonneg (x+2)]
  have hu : x ≤ 1 := by
    by_contra hn
    have hx : 2 ≤ x := by omega
    nlinarith [sq_nonneg (x-2)]
  omega

private theorem integer_square_eq_one {x : ℤ} (h : x^2 = 1) :
    x = -1 ∨ x = 1 := by
  have hx := integer_square_le_two (x := x) (by omega)
  rcases hx with hx | hx | hx
  · exact Or.inl hx
  · subst x; norm_num at h
  · exact Or.inr hx

/-- The long block of the weight-four vertex has squared norm one or three. -/
theorem weightFour_long_block {m a z r s t : ℤ}
    (hm : m = 4 ∨ 6 ≤ m)
    (h : m*a^2+2*a+1+3*z^2+2*r^2+2*s^2+t^2 = 4) :
    (a = 0 ∨ (m = 4 ∧ a = -1)) ∧
      (m*a^2+2*a+1 = 1 ∨ m*a^2+2*a+1 = 3) := by
  have hm4 : 4 ≤ m := by omega
  have hmul : 0 ≤ (m-4)*a^2 := mul_nonneg (by omega) (sq_nonneg a)
  have hq : 4*a^2+2*a ≤ 3 := by
    nlinarith [sq_nonneg z, sq_nonneg r, sq_nonneg s, sq_nonneg t]
  have haL : -1 ≤ a := by
    by_contra hn
    have ha : a ≤ -2 := by omega
    nlinarith [sq_nonneg (a+1)]
  have haU : a ≤ 0 := by
    by_contra hn
    have ha : 1 ≤ a := by omega
    nlinarith [sq_nonneg (a-1)]
  have ha : a = -1 ∨ a = 0 := by omega
  rcases ha with rfl | rfl
  · have hm' : m = 4 := by
      rcases hm with hm | hm
      · exact hm
      · nlinarith [sq_nonneg z, sq_nonneg r, sq_nonneg s, sq_nonneg t]
    subst m
    norm_num
  · norm_num

/-- The small-weight long blocks have the only possibilities used in Section 3A. -/
theorem smallWeight_long_blocks {m b c g ell rB sB tB rC sC tC : ℤ}
    (hm : m = 4 ∨ 6 ≤ m)
    (hB : m*b^2+(g-1)^2+2*g^2+2*rB^2+2*sB^2+tB^2 = 6)
    (hC : m*c^2+2*ell^2+(ell+1)^2+2*rC^2+2*sC^2+tC^2 = 3) :
    c = 0 ∧ (b = 0 ∨ (m = 4 ∧ b^2 = 1)) := by
  have hm4 : 4 ≤ m := by omega
  have hcMul : 0 ≤ (m-4)*c^2 := mul_nonneg (by omega) (sq_nonneg c)
  have hcSmall : c^2 < 1 := by
    nlinarith [sq_nonneg ell, sq_nonneg (ell+1), sq_nonneg rC,
      sq_nonneg sC, sq_nonneg tC]
  have hc := integer_zero_of_square_lt_one hcSmall
  refine ⟨hc, ?_⟩
  by_cases hb : b = 0
  · exact Or.inl hb
  have hb1 := integer_square_ge_one hb
  have hg : 1 ≤ (g-1)^2+2*g^2 := by
    by_cases hg0 : g = 0
    · subst g; norm_num
    · have := integer_square_ge_one hg0
      nlinarith [sq_nonneg (g-1)]
  rcases hm with hm | hm
  · subst m
    have hbSq : b^2 = 1 := by
      nlinarith [sq_nonneg rB, sq_nonneg sB, sq_nonneg tB]
    exact Or.inr ⟨rfl, hbSq⟩
  · have hmul : 0 ≤ (m-6)*b^2 := mul_nonneg (by omega) (sq_nonneg b)
    nlinarith [sq_nonneg rB, sq_nonneg sB, sq_nonneg tB]

private theorem integer_square_le_three {x : ℤ} (h : x^2 ≤ 3) :
    x = -1 ∨ x = 0 ∨ x = 1 := by
  have hl : -1 ≤ x := by
    by_contra hn
    have hx : x ≤ -2 := by omega
    nlinarith [sq_nonneg (x+2)]
  have hu : x ≤ 1 := by
    by_contra hn
    have hx : 2 ≤ x := by omega
    nlinarith [sq_nonneg (x-2)]
  omega

private theorem residual_one {r s t : ℤ}
    (h : 2*r^2+2*s^2+t^2 = 1) : r = 0 ∧ s = 0 ∧ t^2 = 1 := by
  have hr : r = 0 := integer_zero_of_square_lt_one (by nlinarith [sq_nonneg s, sq_nonneg t])
  have hs : s = 0 := integer_zero_of_square_lt_one (by nlinarith [sq_nonneg r, sq_nonneg t])
  refine ⟨hr, hs, ?_⟩
  simpa [hr, hs] using h

private theorem residual_two {r s t : ℤ}
    (h : 2*r^2+2*s^2+t^2 = 2) : t = 0 ∧ r^2+s^2 = 1 := by
  have ht := integer_square_le_two (x := t) (by nlinarith [sq_nonneg r, sq_nonneg s])
  rcases ht with rfl | rfl | rfl
  · norm_num at h; omega
  · constructor
    · rfl
    · nlinarith
  · norm_num at h; omega

/-- The weight-four and weight-three vertices force exactly the shape used
in the paper: `z = ell = 0`, a singleton unit in `A`, and one unit pair in `C`. -/
theorem weightFour_weightThree_shapes {k z ell rA sA tA rC sC tC : ℤ}
    (hk : k = 1 ∨ k = 3)
    (hA : k+3*z^2+2*rA^2+2*sA^2+tA^2 = 4)
    (hC : 2*ell^2+(ell+1)^2+2*rC^2+2*sC^2+tC^2 = 3)
    (hAC : z*(3*ell+1)+2*(rA*rC+sA*sC)+tA*tC = 0) :
    ell = 0 ∧ z = 0 ∧ tA^2 = 1 ∧ tC = 0 ∧ rC^2+sC^2 = 1 := by
  have hk1 : 1 ≤ k := by omega
  have hellL : -1 ≤ ell := by
    by_contra hn
    have hl : ell ≤ -2 := by omega
    nlinarith [sq_nonneg (ell+1), sq_nonneg rC, sq_nonneg sC, sq_nonneg tC]
  have hellU : ell ≤ 0 := by
    by_contra hn
    have hl : 1 ≤ ell := by omega
    nlinarith [sq_nonneg (ell-1), sq_nonneg rC, sq_nonneg sC, sq_nonneg tC]
  have hell : ell = -1 ∨ ell = 0 := by omega
  rcases hell with rfl | rfl
  · have hres : 2*rC^2+2*sC^2+tC^2 = 1 := by nlinarith
    obtain ⟨hrC, hsC, htC⟩ := residual_one hres
    subst rC; subst sC
    have hts : tA = 2*z ∨ tA = -2*z := by
      rcases integer_square_eq_one htC with ht | ht
      · rw [ht] at hAC; right; nlinarith
      · rw [ht] at hAC; left; nlinarith
    have htSq : tA^2 = 4*z^2 := by
      rcases hts with ht | ht <;> rw [ht] <;> ring
    have hz : z = 0 := integer_zero_of_square_lt_one
      (by nlinarith [sq_nonneg rA, sq_nonneg sA])
    subst z
    have ht : tA = 0 := integer_zero_of_square_lt_one (by nlinarith)
    subst tA
    rcases hk with rfl | rfl <;> norm_num at hA <;> omega
  · have hres : 2*rC^2+2*sC^2+tC^2 = 2 := by nlinarith
    obtain ⟨htC, hpC⟩ := residual_two hres
    subst tC
    have hzChoices := integer_square_le_two (x := z)
      (by nlinarith [sq_nonneg rA, sq_nonneg sA, sq_nonneg tA])
    have hz : z = 0 := by
      rcases hzChoices with hz | hz | hz
      · rw [hz] at hAC; norm_num at hAC; omega
      · exact hz
      · rw [hz] at hAC; norm_num at hAC; omega
    subst z
    have htChoices := integer_square_le_three (x := tA)
      (by nlinarith [sq_nonneg rA, sq_nonneg sA])
    have htA : tA^2 = 1 := by
      rcases htChoices with ht | ht | ht
      · rw [ht]; norm_num
      · subst tA; rcases hk with rfl | rfl <;> norm_num at hA <;> omega
      · rw [ht]; norm_num
    exact ⟨rfl, rfl, htA, rfl, hpC⟩

private theorem integer_square_le_six {x : ℤ} (h : x^2 ≤ 6) : -2 ≤ x ∧ x ≤ 2 := by
  constructor
  · by_contra hn
    have hx : x ≤ -3 := by omega
    nlinarith [sq_nonneg (x+3)]
  · by_contra hn
    have hx : 3 ≤ x := by omega
    nlinarith [sq_nonneg (x-3)]

/-- The weight-six vertex has the two shapes described in the paper.
`d` is its long-block squared norm, already proved to be zero or four. -/
theorem weightSix_shape {d g r s t : ℤ}
    (hd : d = 0 ∨ d = 4)
    (hB : d+(g-1)^2+2*g^2+2*r^2+2*s^2+t^2 = 6)
    (hInd : ¬ ((3*g-1)%2 = 0 ∧ t%2 = 0)) :
    g = 0 ∧ t^2 = 1 ∧ (d = 0 → r^2 = 1 ∧ s^2 = 1) ∧
      (d = 4 → r = 0 ∧ s = 0) := by
  have hd0 : 0 ≤ d := by omega
  have hgL : -1 ≤ g := by
    by_contra hn
    have hg : g ≤ -2 := by omega
    nlinarith [sq_nonneg (g+2), sq_nonneg r, sq_nonneg s, sq_nonneg t]
  have hgU : g ≤ 1 := by
    by_contra hn
    have hg : 2 ≤ g := by omega
    nlinarith [sq_nonneg (g-2), sq_nonneg r, sq_nonneg s, sq_nonneg t]
  have htBound : -2 ≤ t ∧ t ≤ 2 := integer_square_le_six
    (by nlinarith [sq_nonneg (g-1), sq_nonneg g, sq_nonneg r, sq_nonneg s])
  obtain ⟨htL, htU⟩ := htBound
  have hg : g = 0 := by
    have hgs : g = -1 ∨ g = 0 ∨ g = 1 := by omega
    rcases hgs with hg | hg | hg
    · subst g
      have ht : t = 0 := integer_zero_of_square_lt_one
        (by nlinarith [sq_nonneg r, sq_nonneg s])
      subst t
      norm_num at hInd
    · exact hg
    · subst g
      interval_cases t <;> norm_num at hInd hB
      all_goals rcases hd with rfl | rfl <;> omega
  subst g
  have ht : t^2 = 1 := by
    interval_cases t <;> norm_num at hB ⊢
    all_goals rcases hd with rfl | rfl <;> omega
  refine ⟨rfl, ht, ?_, ?_⟩
  · intro hd'
    subst d
    have hrSmall : r^2 ≤ 2 := by nlinarith [sq_nonneg s]
    have hsSmall : s^2 ≤ 2 := by nlinarith [sq_nonneg r]
    have hr : r^2 ≤ 1 := by
      rcases integer_square_le_two hrSmall with h | h | h <;> rw [h] <;> norm_num
    have hs : s^2 ≤ 1 := by
      rcases integer_square_le_two hsSmall with h | h | h <;> rw [h] <;> norm_num
    constructor <;> nlinarith
  · intro hd'
    subst d
    have hres : 2*r^2+2*s^2+t^2 = 1 := by nlinarith
    obtain ⟨hr, hs, _⟩ := residual_one hres
    exact ⟨hr, hs⟩

private theorem unit_pairing_ne_neg_one {a b t u : ℤ}
    (hb : b^2 = 1) (ht : t^2 = 1) (hu : u^2 = 1) :
    (4*a+1)*b+t*u ≠ -1 := by
  intro h
  rcases integer_square_eq_one hb with hb' | hb' <;>
    rcases integer_square_eq_one ht with ht' | ht' <;>
    rcases integer_square_eq_one hu with hu' | hu' <;>
    rw [hb', ht', hu'] at h <;> norm_num at h <;> omega

private theorem one_unit_pair {r s : ℤ} (h : r^2+s^2 = 1) :
    (r = 0 ∧ s^2 = 1) ∨ (r^2 = 1 ∧ s = 0) := by
  have hrSmall : r^2 ≤ 2 := by nlinarith [sq_nonneg s]
  rcases integer_square_le_two hrSmall with hr | hr | hr
  · right
    have hs : s = 0 := integer_zero_of_square_lt_one (by rw [hr] at h; nlinarith)
    exact ⟨by rw [hr]; norm_num, hs⟩
  · left
    exact ⟨hr, by rw [hr] at h; nlinarith⟩
  · right
    have hs : s = 0 := integer_zero_of_square_lt_one (by rw [hr] at h; nlinarith)
    exact ⟨by rw [hr]; norm_num, hs⟩

set_option maxHeartbeats 1000000 in
/-- There is no configuration of the three heavy vertices satisfying the
displayed normal form, pairings and mod-two independence in Section 3A. -/
theorem no_lattice_configuration {m : ℤ} (hm : m = 4 ∨ 6 ≤ m)
    (v : LatticeConfiguration m) : False := by
  rcases v with ⟨a,b,c,z,g,ell,rA,sA,tA,rB,sB,tB,rC,sC,tC,
    hA,hB,hC,hAB,hAC,hBC,hInd⟩
  obtain ⟨ha, hk⟩ := weightFour_long_block hm hA
  obtain ⟨hc, hb⟩ := smallWeight_long_blocks hm hB hC
  subst c
  simp only [zero_pow (by decide : 2 ≠ 0), mul_zero, zero_add] at hC
  simp only [mul_zero, zero_add] at hAC
  obtain ⟨hell, hz, htA, htC, hpC⟩ := weightFour_weightThree_shapes hk hA hC hAC
  subst ell; subst z; subst tC
  have hLong : m*b^2 = 0 ∨ m*b^2 = 4 := by
    rcases hb with hb | ⟨hm', hb⟩
    · rw [hb]; norm_num
    · rw [hm', hb]; norm_num
  have hEvenLong : (m*b)%2 = 0 := by
    rcases hb with hb | ⟨hm', _⟩
    · rw [hb]; norm_num
    · rw [hm']; omega
  have hInd' : ¬ ((3*g-1)%2 = 0 ∧ tB%2 = 0) := by
    intro h
    exact hInd ⟨hEvenLong,h⟩
  obtain ⟨hg, htB, hBzero, hBfour⟩ := weightSix_shape hLong hB hInd'
  subst g
  rcases hb with hb | ⟨hm', hb⟩
  · subst b
    have hzero : m*(0:ℤ)^2 = 0 := by ring
    obtain ⟨hrB, hsB⟩ := hBzero hzero
    rcases one_unit_pair hpC with ⟨hrC, hsC⟩ | ⟨hrC, hsC⟩
    · subst rC
      have hprod : sB*sC = 0 := by nlinarith only [hBC]
      rcases mul_eq_zero.mp hprod with h | h
      · rw [h] at hsB; norm_num at hsB
      · rw [h] at hsC; norm_num at hsC
    · subst sC
      have hprod : rB*rC = 0 := by nlinarith only [hBC]
      rcases mul_eq_zero.mp hprod with h | h
      · rw [h] at hrB; norm_num at hrB
      · rw [h] at hrC; norm_num at hrC
  · subst m
    have hfour : (4:ℤ)*b^2 = 4 := by rw [hb]; norm_num
    obtain ⟨hrB, hsB⟩ := hBfour hfour
    subst rB; subst sB
    exact unit_pairing_ne_neg_one hb htA htB (by simpa using hAB)

/-- Natural-number formulation matching the family parameter in the paper. -/
theorem no_lattice_configuration_nat (m : ℕ) (hm : m = 4 ∨ 6 ≤ m)
    (v : LatticeConfiguration (m : ℤ)) : False := by
  apply no_lattice_configuration (m := (m : ℤ)) _ v
  omega

end Trefoil
