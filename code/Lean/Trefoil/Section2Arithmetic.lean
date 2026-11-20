import Trefoil.Arithmetic
import Mathlib.Data.Int.ModEq
import Mathlib.Algebra.Ring.Int.Parity

/-!
# Exact calculations for the three-change sequences in Section 2

The arithmetic keeps the crossing-circle slopes and the partner's two
marked twist boxes explicit. The definitions here are finite combinatorics
and integer arithmetic. Their interpretations as crossings, Reidemeister
moves, Dehn fillings and rational tangles are supplied separately.
-/

namespace Trefoil.Section2Arithmetic

open Trefoil.Arithmetic

/-- Choice of augmented diagram in the two parity cases. -/
def parity (m : ℕ) : Fin 2 := ⟨m % 2, Nat.mod_lt _ (by decide)⟩

/-- Number of full twists after retaining the zero or one half-twist. -/
def fullTwists (m : ℕ) : ℕ := m / 2

def halfTwists (b : Fin 2) (t : ℕ) : ℕ := b.val + 2 * t

@[simp] theorem halfTwists_decompose (m : ℕ) :
    halfTwists (parity m) (fullTwists m) = m := by
  simpa [halfTwists, parity, fullTwists] using Nat.mod_add_div m 2

/-- Filling slope in the meridian and disk longitude basis. -/
def twistSlope (t : ℤ) : ℤ × ℤ := (1, t)

/-- The unoriented slopes are represented by opposite primitive vectors. -/
def SameSlope (s t : ℤ × ℤ) : Prop := s = t ∨ s = (-t.1, -t.2)

def reflectSlope (s : ℤ × ℤ) : ℤ × ℤ := (s.1, -s.2)

@[simp] theorem reflect_twistSlope (t : ℤ) : reflectSlope (twistSlope t) = twistSlope (-t) := rfl

theorem twistSlope_primitive (t : ℤ) : Nat.Coprime (twistSlope t).1.natAbs (twistSlope t).2.natAbs := by
  simp [twistSlope]

/-- A diagonal meridian-preserving peripheral matrix with second entry
`sign`, up to an overall sign. The entries act on the ordered slope pair. -/
def diagonalAction (overall sign : ℤ) (s : ℤ × ℤ) : ℤ × ℤ :=
  (overall * s.1, overall * sign * s.2)

theorem diagonalAction_twistSlope (t overall sign : ℤ)
    (h : overall = 1 ∨ overall = -1) :
    SameSlope (diagonalAction overall sign (twistSlope t)) (twistSlope (sign * t)) := by
  rcases h with rfl | rfl
  · exact Or.inl (by simp [diagonalAction, twistSlope])
  · exact Or.inr (by simp [diagonalAction, twistSlope, neg_mul])

/-- Homogeneous numerator and denominator of the sum of two finite
rational slopes. We keep the homogeneous presentation for the later
infinity slope calculation. -/
def tangleAdd (p q : ℤ × ℤ) : ℤ × ℤ := (p.1 * q.2 + q.1 * p.2, p.2 * q.2)

/-- Splitting off the first integer twist box in the continued fraction
produces the tail used at the constructed remainder diagram. -/
theorem partner_tail : plusPair [2, 1, 4, 3, 2] = (104, 37) := by decide

/-- Integer twists added beside the remainder tangle give the partner's
homogeneous pair as in the paper. -/
theorem integer_plus_remainder (m : ℤ) :
    tangleAdd (m, 1) (37, 104) = plusPair [m, 2, 1, 4, 3, 2] := by
  rw [partner_fraction]
  simp [tangleAdd, mul_comm]

/-- For the chosen parity, adjoining the full twists gives the same
fraction as the corresponding member of the infinite family. -/
theorem filled_remainder_fraction (b : Fin 2) (t : ℕ) :
    tangleAdd (((b.val : ℤ) + 2 * (t : ℤ)), 1) (37, 104) =
      plusPair [(halfTwists b t : ℤ), 2, 1, 4, 3, 2] := by
  have hcast : ((halfTwists b t : ℕ) : ℤ) = (b.val : ℤ) + 2 * (t : ℤ) := by
    simp [halfTwists]
  rw [hcast, integer_plus_remainder]

/-- One elementary operation of a rational-tangle chart, applied outward
from its innermost twist box. -/
inductive ChartStep where
  | translate : ℤ → ChartStep
  | invert : ChartStep
  deriving DecidableEq

def ChartStep.apply : ChartStep → (ℤ × ℤ) → (ℤ × ℤ)
  | .translate k, p => (p.1 + k * p.2, p.2)
  | .invert, p => (p.2, p.1)

def ChartStep.orientation : ChartStep → ℤ
  | .translate _ => 1
  | .invert => -1

def chartApply (chart : List ChartStep) (p : ℤ × ℤ) : ℤ × ℤ :=
  chart.foldl (fun x step => step.apply x) p

def chartOrientation (chart : List ChartStep) : ℤ :=
  (chart.map ChartStep.orientation).prod

def crossProduct (p q : ℤ × ℤ) : ℤ := p.1 * q.2 - p.2 * q.1

/-- Each reciprocal reverses the determinant sign, while integer twists
preserve it. This statement also covers an arbitrary sequence of chart
operations. -/
theorem chart_crossProduct (chart : List ChartStep) (p q : ℤ × ℤ) :
    crossProduct (chartApply chart p) (chartApply chart q) =
      chartOrientation chart * crossProduct p q := by
  induction chart generalizing p q with
  | nil => simp [chartApply, chartOrientation]
  | cons step chart ih =>
    have hstep : crossProduct (step.apply p) (step.apply q) =
        step.orientation * crossProduct p q := by
      cases step <;> simp only [ChartStep.apply, crossProduct, ChartStep.orientation] <;> ring
    change crossProduct (chartApply chart (step.apply p)) (chartApply chart (step.apply q)) = _
    rw [ih, hstep]
    simp only [chartOrientation, List.map_cons, List.prod_cons]
    ring

/-- The first two marked diagrams use `[0,1,2,m]⁺`. -/
def firstChart : List ChartStep :=
  [.invert, .translate 2, .invert, .translate 1, .invert, .translate 0]

/-- The last marked diagram uses `[1,2,m]⁺`. -/
def lastChart : List ChartStep := [.invert, .translate 2, .invert, .translate 1]

theorem firstChart_fraction (m : ℤ) :
    chartApply firstChart (m, 1) = plusPair [0, 1, 2, m] := by
  rw [first_insertion_fraction]
  apply Prod.ext <;> simp only [chartApply, firstChart, ChartStep.apply,
    List.foldl_cons, List.foldl_nil] <;> ring

theorem lastChart_fraction (m : ℤ) :
    chartApply lastChart (m, 1) = plusPair [1, 2, m] := by
  rw [last_insertion_fraction]
  apply Prod.ext <;> simp only [chartApply, lastChart, ChartStep.apply,
    List.foldl_cons, List.foldl_nil] <;> ring

/-- In the disk longitude convention, the innermost chart's base slope
has negative full-twist coefficient. A reciprocal reverses that sign. -/
def chartSlopeSign (chart : List ChartStep) : ℤ := -chartOrientation chart

@[simp] theorem firstChart_slopeSign : chartSlopeSign firstChart = 1 := by decide

@[simp] theorem lastChart_slopeSign : chartSlopeSign lastChart = -1 := by decide

/-- Each bit is the sign of one crossing in a fixed Conway twist box.
Boxes have their own local sign conventions. -/
abbrev TwistBox := List Bool
abbrev TwistDiagram := List TwistBox

def signedBox (n : ℤ) : TwistBox := List.replicate n.natAbs (0 ≤ n)

def boxWeight (box : TwistBox) : ℤ := (box.map fun c => if c then 1 else -1).sum

def diagramWeights (D : TwistDiagram) : List ℤ := D.map boxWeight

@[simp] theorem signedBox_weight (n : ℤ) : boxWeight (signedBox n) = n := by
  cases n with
  | ofNat n => simp [boxWeight, signedBox]
  | negSucc n =>
      simp [boxWeight, signedBox]
      omega

/-- Switching exactly one sign in exactly one box. -/
inductive TwistDiagramSwitch : TwistDiagram → TwistDiagram → Prop where
  | atCrossing (pre post : TwistDiagram) (a b : TwistBox) (c : Bool) :
      TwistDiagramSwitch (pre ++ [(a ++ c :: b)] ++ post)
        (pre ++ [(a ++ (!c) :: b)] ++ post)

/-- Deleting adjacent opposite signs in one box. -/
inductive TwistDiagramCancel : TwistDiagram → TwistDiagram → Prop where
  | adjacent (pre post : TwistDiagram) (a b : TwistBox) (c : Bool) :
      TwistDiagramCancel (pre ++ [(a ++ c :: (!c) :: b)] ++ post)
        (pre ++ [(a ++ b)] ++ post)

private def pairModEqTwo (p q : ℤ × ℤ) : Prop :=
  Int.ModEq 2 p.1 q.1 ∧ Int.ModEq 2 p.2 q.2

private theorem plusPair_cons_modEq {a b : ℤ} {as bs : List ℤ}
    (hab : Int.ModEq 2 a b) (ht : pairModEqTwo (plusPair as) (plusPair bs)) :
    pairModEqTwo (plusPair (a :: as)) (plusPair (b :: bs)) := by
  rcases ht with ⟨h₁, h₂⟩
  exact ⟨(hab.mul h₁).add h₂, h₁⟩

private theorem plusPair_middle_modEq (pre post : List ℤ) {a b : ℤ}
    (h : Int.ModEq 2 a b) :
    pairModEqTwo (plusPair (pre ++ a :: post)) (plusPair (pre ++ b :: post)) := by
  induction pre with
  | nil => exact plusPair_cons_modEq h ⟨Int.ModEq.refl _, Int.ModEq.refl _⟩
  | cons head pre ih => exact plusPair_cons_modEq (Int.ModEq.refl head) ih

/-- One twist-box switch changes the homogeneous numerator by an even integer. -/
theorem TwistDiagramSwitch.numerator_modEq {D E : TwistDiagram}
    (h : TwistDiagramSwitch D E) :
    Int.ModEq 2 (plusPair (diagramWeights D)).1 (plusPair (diagramWeights E)).1 := by
  cases h with
  | atCrossing pre post a b c =>
    have hc : Int.ModEq 2 (boxWeight (a ++ c :: b)) (boxWeight (a ++ (!c) :: b)) := by
      cases c <;> simp [Int.ModEq, boxWeight, List.sum_append] <;> omega
    simpa only [diagramWeights, List.map_append, List.map_cons, List.map_nil, List.append_assoc, List.singleton_append]
      using (plusPair_middle_modEq (diagramWeights pre) (diagramWeights post) hc).1

/-- Adjacent cancellation preserves the entire list of twist weights. -/
theorem TwistDiagramCancel.weights_eq {D E : TwistDiagram} (h : TwistDiagramCancel D E) :
    diagramWeights D = diagramWeights E := by
  cases h with
  | adjacent pre post a b c =>
    have hc : boxWeight (a ++ c :: (!c) :: b) = boxWeight (a ++ b) := by
      cases c <;> simp [boxWeight, List.sum_append]
    simp [diagramWeights, hc]

theorem TwistDiagramCancel.numerator_modEq {D E : TwistDiagram}
    (h : TwistDiagramCancel D E) :
    Int.ModEq 2 (plusPair (diagramWeights D)).1 (plusPair (diagramWeights E)).1 := by
  rw [h.weights_eq]

theorem TwistDiagramSwitch.numerator_odd_iff {D E : TwistDiagram}
    (h : TwistDiagramSwitch D E) :
    Odd (plusPair (diagramWeights D)).1 ↔ Odd (plusPair (diagramWeights E)).1 := by
  simp only [Int.odd_iff]
  rw [show (plusPair (diagramWeights D)).1 % 2 = (plusPair (diagramWeights E)).1 % 2
    from h.numerator_modEq]

theorem TwistDiagramCancel.numerator_odd_iff {D E : TwistDiagram}
    (h : TwistDiagramCancel D E) :
    Odd (plusPair (diagramWeights D)).1 ↔ Odd (plusPair (diagramWeights E)).1 := by
  rw [h.weights_eq]

def partnerWeights (m : ℤ) : List ℤ := [m, 2, 1, 4, 3, 2]

def partnerBoxes (m : ℤ) : TwistDiagram := (partnerWeights m).map signedBox

def changedPartnerBoxes (m : ℤ) : TwistDiagram := [signedBox m, signedBox 2, [false],
  signedBox 4, [false], signedBox 2]

theorem partnerBoxes_weights (m : ℤ) : diagramWeights (partnerBoxes m) = partnerWeights m := by
  simp [partnerBoxes, diagramWeights, List.map_map, Function.comp_def]

/-- The parity of the partner's numerator holds independently of the
choice of twist parameter. -/
theorem partnerWeights_numerator_odd (m : ℤ) : Odd (plusPair (partnerWeights m)).1 := by
  unfold partnerWeights
  rw [partner_fraction]
  exact ⟨52 * m + 18, by simp; ring⟩

theorem partnerBoxes_numerator_odd (m : ℤ) : Odd (plusPair (diagramWeights (partnerBoxes m))).1 := by
  rw [partnerBoxes_weights]
  exact partnerWeights_numerator_odd m

/-- The three indicated crossing changes and one adjacent cancellation.
No diagram or isotopy equivalence is asserted by this finite list proof. -/
theorem partner_three_local_switches (m : ℤ) :
    ∃ D₁ D₂ D₃,
      TwistDiagramSwitch (partnerBoxes m) D₁ ∧
      TwistDiagramSwitch D₁ D₂ ∧ TwistDiagramSwitch D₂ D₃ ∧
      TwistDiagramCancel D₃ (changedPartnerBoxes m) := by
  let X := signedBox m
  let Y := signedBox 2
  let Z := signedBox 4
  refine ⟨[X,Y,[false],Z,[true,true,true],Y], [X,Y,[false],Z,[false,true,true],Y],
    [X,Y,[false],Z,[false,false,true],Y], ?_, ?_, ?_, ?_⟩
  · exact .atCrossing [X,Y] [Z,[true,true,true],Y] [] [] true
  · exact .atCrossing [X,Y,[false],Z] [Y] [] [true,true] true
  · exact .atCrossing [X,Y,[false],Z] [Y] [false] [true] true
  · exact .adjacent [X,Y,[false],Z] [Y] [false] [] false

/-- After the checked local edits the partner's fraction is the infinity
slope. Its topological interpretation uses the rational tangle theorem. -/
theorem changedPartnerBoxes_infinity (m : ℤ) :
    plusPair (diagramWeights (changedPartnerBoxes m)) = (1, 0) := by
  simpa [diagramWeights, changedPartnerBoxes, show boxWeight [false] = -1 by decide] using
    three_changes_infinity m

end Trefoil.Section2Arithmetic
