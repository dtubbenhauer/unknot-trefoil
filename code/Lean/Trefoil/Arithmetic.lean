import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Lean.Elab.Tactic.Omega
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Algebra.BigOperators.Group.List.Defs
import Mathlib.Algebra.Order.Field.Basic

/-!
# Exact arithmetic used by the trefoil paper

These are proofs about explicitly defined continued fractions and rational
pivots. No topological identification, signature theorem, or conclusion
about unknotting number is built into the definitions.

Homogeneous numerator--denominator pairs retain the infinity tangle `(1, 0)`;
evaluating a continued fraction using field division alone would lose this
information because Lean defines inverse zero to be zero.
-/

namespace Trefoil

namespace Arithmetic

/-- Homogeneous pair for a positive continued fraction. -/
def plusPair : List ℤ → ℤ × ℤ
  | [] => (1, 0)
  | a :: as =>
      let tail := plusPair as
      (a * tail.1 + tail.2, tail.1)

/-- Homogeneous pair for a negative continued fraction. -/
def minusPair : List ℤ → ℤ × ℤ
  | [] => (1, 0)
  | a :: as =>
      let tail := minusPair as
      (a * tail.1 - tail.2, tail.1)

theorem partner_fraction (m : ℤ) :
    plusPair [m, 2, 1, 4, 3, 2] = (104 * m + 37, 104) := by
  apply Prod.ext <;> norm_num [plusPair]
  ring

theorem three_changes_infinity (m : ℤ) :
    plusPair [m, 2, -1, 4, -1, 2] = (1, 0) := by
  norm_num [plusPair]

theorem first_insertion_fraction (m : ℤ) :
    plusPair [0, 1, 2, m] = (2 * m + 1, 3 * m + 1) := by
  apply Prod.ext <;> norm_num [plusPair]
  ring

theorem last_insertion_fraction (m : ℤ) :
    plusPair [1, 2, m] = (3 * m + 1, 2 * m + 1) := by
  apply Prod.ext <;> norm_num [plusPair]
  ring

theorem first_insertion_seed : plusPair [0, 1, 2, 0] = (1, 1) := by
  norm_num [plusPair]

theorem last_insertion_seed : plusPair [1, 2, 0] = (1, 1) := by
  norm_num [plusPair]

theorem first_insertion_two : plusPair [0, 1, 2, 2] = (5, 7) := by
  norm_num [plusPair]

theorem last_insertion_two : plusPair [1, 2, 2] = (7, 5) := by
  norm_num [plusPair]

theorem even_seifert_pair (m : ℤ) :
    minusPair [m, -2, 2, 2, 2, 2, 4, -2] = (104 * m + 37, 104) := by
  apply Prod.ext <;> norm_num [minusPair]
  ring

/-- The odd expansion has the same fraction, with both homogeneous signs
reversed. The sign reversal is recorded rather than silently discarded. -/
theorem odd_seifert_pair (m : ℤ) :
    minusPair [m + 1, 2, 2, -4, 4, 2] = (-(104 * m + 37), -104) := by
  apply Prod.ext <;> norm_num [minusPair]
  ring

theorem plumbing_tail_pair :
    minusPair [4, 6, 2, 2, 3] = (141, 37) := by
  norm_num [minusPair]

/-- Adding `n` leading vertices of weight two gives the exact plumbing
fraction. The paper uses `n = m - 1`. -/
theorem plumbing_pair (n : ℕ) :
    minusPair (List.replicate n 2 ++ [4, 6, 2, 2, 3]) =
      (104 * (n : ℤ) + 141, 104 * (n : ℤ) + 37) := by
  induction n with
  | zero => norm_num [minusPair]
  | succ n ih =>
      simp only [List.replicate_succ, List.cons_append, minusPair, ih]
      apply Prod.ext <;> norm_num <;> ring

theorem plumbing_pair_at_parameter (m : ℕ) :
    minusPair (List.replicate m 2 ++ [4, 6, 2, 2, 3]) =
      (104 * ((m : ℤ) + 1) + 37, 104 * ((m : ℤ) + 1) + 37 - 104) := by
  rw [plumbing_pair]
  apply Prod.ext <;> norm_num <;> ring

theorem determinant_odd (m : ℕ) : Odd (104 * m + 37) := by
  exact ⟨52 * m + 18, by omega⟩

theorem determinant_coprime (m : ℕ) : Nat.Coprime (104 * m + 37) 104 := by
  rw [Nat.add_comm, Nat.coprime_add_mul_left_left]
  decide

theorem determinant_strictMono : StrictMono (fun m : ℕ => 104 * m + 37) := by
  intro a b hab
  change 104 * a + 37 < 104 * b + 37
  omega

theorem determinant_injective : Function.Injective (fun m : ℕ => 104 * m + 37) :=
  determinant_strictMono.injective

theorem determinant_bezout (m : ℤ) :
    45 * (104 * m + 37) - 104 * (45 * m + 16) = 1 := by
  ring

theorem determinant_at_two : (104 : ℤ) * 2 + 37 = 245 := by norm_num

theorem lens_complement_at_two : (245 : ℕ) - 104 = 141 := by norm_num

/-- The unique solution of the spin-label congruence for `(p,q)=(245,141)`.
The identification of this congruence with topological conjugation is part
of the lens-space labeling convention, not a definition of a knot. -/
theorem spin_label_unique (i : Fin 245) :
    (2 * i.val) % 245 = 140 ↔ i.val = 70 := by
  omega

/-- A negative continued fraction evaluated in the field of rationals.
This function is used only where all elimination pivots are nonzero. -/
def minusValue : List ℚ → ℚ
  | [] => 0
  | a :: as => a - (minusValue as)⁻¹

/-- Right-to-left elimination pivots, listed in the original vertex order. -/
def rightPivots : List ℚ → List ℚ
  | [] => []
  | a :: as => minusValue (a :: as) :: rightPivots as

theorem even_pivots (m : ℚ) :
    rightPivots [m, -2, 2, 2, 2, 2, 4, -2] =
      [(104 * m + 37) / 104, -104 / 37, 37 / 30, 30 / 23,
        23 / 16, 16 / 9, 9 / 2, -2] := by
  norm_num [rightPivots, minusValue]
  ring

theorem odd_pivots (m : ℚ) :
    rightPivots [m + 1, 2, 2, -4, 4, 2] =
      [(104 * m + 37) / 104, 104 / 67, 67 / 30, -30 / 7, 7 / 2, 2] := by
  norm_num [rightPivots, minusValue]
  ring

/-- The signature of a diagonal rational form represented by its pivots. -/
def signedPivotCount (ps : List ℚ) : ℤ :=
  (ps.map fun q => if 0 < q then (1 : ℤ) else if q < 0 then -1 else 0).sum

theorem even_pivot_signature (m : ℚ) (hm : 0 ≤ m) :
    signedPivotCount (rightPivots [m, -2, 2, 2, 2, 2, 4, -2]) = 4 := by
  have hp : 0 < (104 * m + 37) / 104 := by positivity
  rw [even_pivots]
  norm_num [signedPivotCount, hp]

theorem odd_pivot_signature (m : ℚ) (hm : 0 ≤ m) :
    signedPivotCount (rightPivots [m + 1, 2, 2, -4, 4, 2]) = 4 := by
  have hp : 0 < (104 * m + 37) / 104 := by positivity
  rw [odd_pivots]
  norm_num [signedPivotCount, hp]

theorem even_pivots_nonzero (m : ℚ) (hm : 0 ≤ m) :
    ∀ q ∈ rightPivots [m, -2, 2, 2, 2, 2, 4, -2], q ≠ 0 := by
  have hp : (104 * m + 37) / 104 ≠ 0 := ne_of_gt (by positivity)
  rw [even_pivots]
  norm_num [hp]

theorem odd_pivots_nonzero (m : ℚ) (hm : 0 ≤ m) :
    ∀ q ∈ rightPivots [m + 1, 2, 2, -4, 4, 2], q ≠ 0 := by
  have hp : (104 * m + 37) / 104 ≠ 0 := ne_of_gt (by positivity)
  rw [odd_pivots]
  norm_num [hp]

/-- Exact rational value of the positive plumbing, for every number of
leading weight-two vertices. -/
theorem plumbing_value (n : ℕ) :
    minusValue (List.replicate n 2 ++ [4, 6, 2, 2, 3]) =
      (104 * (n : ℚ) + 141) / (104 * (n : ℚ) + 37) := by
  induction n with
  | zero => norm_num [minusValue]
  | succ n ih =>
      simp only [List.replicate_succ, List.cons_append, minusValue, ih]
      have hnum : 104 * (n : ℚ) + 141 ≠ 0 := ne_of_gt (by positivity)
      have hden : 104 * (n : ℚ) + 37 ≠ 0 := ne_of_gt (by positivity)
      norm_num only [Nat.cast_add, Nat.cast_one, Nat.cast_succ]
      field_simp
      ring

/-- Positivity of every elimination pivot of the positive plumbing.
The general theorem relating these pivots to positive definiteness of its
intersection matrix is a separate linear-algebra bridge. -/
theorem plumbing_pivots_positive (n : ℕ) :
    ∀ q ∈ rightPivots (List.replicate n 2 ++ [4, 6, 2, 2, 3]), 0 < q := by
  induction n with
  | zero => norm_num [rightPivots, minusValue]
  | succ n ih =>
      rw [List.replicate_succ, List.cons_append, rightPivots]
      intro q hq
      simp only [List.mem_cons] at hq
      rcases hq with hq | hq
      · subst q
        change 0 < minusValue (List.replicate (n + 1) 2 ++ [4, 6, 2, 2, 3])
        rw [plumbing_value]
        positivity
      · exact ih q hq

end Arithmetic
end Trefoil
