import Trefoil.Section2Arithmetic

/-!
# The three crossing changes of Section 2

The upper bound for a partner alone is relative to the usual rational-tangle
dictionary. For the connected sum, the uniform Dehn-filling argument receives
the two finite diagram certificates. Its conclusion is quantified over every
twist parameter. The finite geometry still needed by this stage is exposed
in the types below.
-/

namespace Trefoil.Section2Topology

open Section2Arithmetic

/-- A crossing-change path of precisely the indicated length, on knot
isotopy classes. The intervening isotopies are expressed by substitution. -/
inductive Changes {K : Type*} (cross : K → K → Prop) : ℕ → K → K → Prop
  | done (K₀) : Changes cross 0 K₀ K₀
  | step {n j k l} : cross j k → Changes cross n k l → Changes cross (n + 1) j l

/-- Knot operations and their diagram interpretation in Section 2. -/
structure KnotGeometry where
  Knot : Type
  unknot : Knot
  trefoil : Knot
  mirror : Knot → Knot
  connectedSum : Knot → Knot → Knot
  unknotting : Knot → ℕ
  switch : Knot → Knot → Prop
  conway : List ℤ → Knot
  numerator : (ℤ × ℤ) → Knot

variable {K : KnotGeometry}

/-- General facts about twist boxes and rational tangle closures. A Boolean
word is the two-strand braid of its signed half twists. -/
structure KnotReferences (K : KnotGeometry) where
  path_bound : ∀ {n j}, Changes K.switch n j K.unknot → K.unknotting j ≤ n
  mirror_switch : ∀ {j k}, K.switch j k → K.switch (K.mirror j) (K.mirror k)
  mirror_unknotting : ∀ j, K.unknotting (K.mirror j) = K.unknotting j
  mirror_unknot : K.mirror K.unknot = K.unknot
  box_switch : ∀ {D E}, TwistDiagramSwitch D E → Odd (Arithmetic.plusPair (diagramWeights D)).1 →
    K.switch (K.conway (diagramWeights D)) (K.conway (diagramWeights E))
  closure_fraction : ∀ weights, Odd (Arithmetic.plusPair weights).1 →
    K.conway weights = K.numerator (Arithmetic.plusPair weights)
  infinity_unknot : K.numerator (1, 0) = K.unknot

/-- The partner is mirrored relative to the rational closure used for the
reference link in the two reversing exterior identifications. -/
def partner (K : KnotGeometry) (m : ℕ) : K.Knot :=
  K.mirror (K.conway (partnerWeights (m : ℤ)))

/-- Section 2B, by switching one crossing in the one-crossing box and two
in the three-crossing box, cancelling opposite signs, and closing infinity. -/
theorem partner_upper_bound (R : KnotReferences K) (m : ℕ) :
    K.unknotting (partner K m) ≤ 3 := by
  obtain ⟨D₁, D₂, D₃, h₁, h₂, h₃, hc⟩ := partner_three_local_switches (m : ℤ)
  have hstart : K.conway (diagramWeights (partnerBoxes (m : ℤ))) =
      K.conway (partnerWeights (m : ℤ)) :=
    congrArg K.conway (partnerBoxes_weights (m : ℤ))
  have o₀ := partnerBoxes_numerator_odd (m : ℤ)
  have o₁ := h₁.numerator_odd_iff.mp o₀
  have o₂ := h₂.numerator_odd_iff.mp o₁
  have o₃ := h₃.numerator_odd_iff.mp o₂
  have hend : K.conway (diagramWeights D₃) = K.unknot := by
    rw [hc.weights_eq, R.closure_fraction _ (hc.numerator_odd_iff.mp o₃),
      changedPartnerBoxes_infinity, R.infinity_unknot]
  have a := R.box_switch h₁ o₀
  have d := R.box_switch h₃ o₂
  rw [hstart] at a
  rw [hend] at d
  have M : Changes K.switch 3 (K.conway (partnerWeights (m : ℤ))) K.unknot :=
    .step a (.step (R.box_switch h₂ o₁) (.step d (.done _)))
  rw [partner, R.mirror_unknotting]
  exact R.path_bound M

/-- A marked exterior map either preserves orientation or reverses it. In
each case the meridian of the main knot is preserved up to sign. Its action
on the axis slope is the identity or the longitude reflection, respectively. -/
inductive ExteriorAction
  | preserve
  | reverse
  deriving DecidableEq

def ExteriorAction.onSlope : ExteriorAction → (ℤ × ℤ) → (ℤ × ℤ)
  | .preserve => id
  | .reverse => reflectSlope

def ExteriorAction.onKnot (K : KnotGeometry) : ExteriorAction → K.Knot → K.Knot
  | .preserve => id
  | .reverse => K.mirror

/-- Intended objects are links with a framed, unknotted crossing circle.
The filling parameter is the integer slope pair in its disk framing.
The predicates record data about unfilled links. -/
structure AugmentedGeometry (K : KnotGeometry) where
  Link : Type
  fill : Link → ℤ × ℤ → K.Knot
  crossingAway : Link → Link → Prop
  splitOff : Link → K.Knot → Link → Prop
  terminalUnlink : Link → Prop
  markedExterior : ExteriorAction → Link → Link → Prop
  axisChart : Fin 2 → (ℤ × ℤ) → Link

variable {A : AugmentedGeometry K}

/-- Standard consequences of filling a marked axis. The chart convention in
`fill_chart` is the disk framing of a side-by-side integer tangle and tail.
The negative slope inserts positive full twists in this chart. -/
structure FillingReferences (A : AugmentedGeometry K) where
  crossing_fills : ∀ {d e} (t : ℤ), A.crossingAway d e →
    K.switch (A.fill d (twistSlope t)) (A.fill e (twistSlope t))
  split_fills : ∀ {d e k} (t : ℤ), A.splitOff d k e →
    A.fill d (twistSlope t) = K.connectedSum k (A.fill e (twistSlope t))
  unlink_fills : ∀ {d} (t : ℤ), A.terminalUnlink d → A.fill d (twistSlope t) = K.unknot
  marked_fills : ∀ {d e action} (t : ℤ), A.markedExterior action d e →
    A.fill d (twistSlope t) =
      action.onKnot K (A.fill e (action.onSlope (twistSlope t)))
  fill_chart : ∀ (b : Fin 2) (t : ℕ) (tail : ℤ × ℤ),
    Nat.Coprime tail.1.natAbs tail.2.natAbs → Odd (tangleAdd ((halfTwists b t : ℤ), 1) tail).1 →
    A.fill (A.axisChart b tail) (twistSlope (- (t : ℤ))) =
      K.numerator (tangleAdd (((halfTwists b t : ℕ) : ℤ), 1) tail)

/-- The finite information for an unfilled parity template. For the published
family these obligations are about precisely the two finite replays. This
structure records outstanding geometric realization where the combinatorial
checks do not yet have a sound interpretation theorem. -/
structure ParityTemplate (A : AugmentedGeometry K) (b : Fin 2) where
  start : A.Link
  afterFirst : A.Link
  beforeSecond : A.Link
  afterSecond : A.Link
  beforeThird : A.Link
  finish : A.Link
  residual : A.Link
  first_switch : A.crossingAway start afterFirst
  second_switch : A.crossingAway beforeSecond afterSecond
  third_switch : A.crossingAway beforeThird finish
  split_start : A.splitOff start K.trefoil residual
  final_unlink : A.terminalUnlink finish
  residual_reference : A.markedExterior .reverse residual (A.axisChart b (37, 104))
  intermediate_first : A.markedExterior .preserve afterFirst beforeSecond
  intermediate_second : A.markedExterior .reverse afterSecond beforeThird

/-- The explicit all-full-twists crossing-change movie in either parity.
The two reversing identifications change exactly the longitude sign.
The last crossing change is mirrored together with its two endpoints. -/
theorem filled_movie (RK : KnotReferences K) (RF : FillingReferences A)
    {b : Fin 2} (P : ParityTemplate A b) (t : ℕ) :
    Changes K.switch 3 (K.connectedSum K.trefoil (partner K (halfTwists b t))) K.unknot := by
  have htail : A.fill (A.axisChart b (37, 104)) (twistSlope (- (t : ℤ))) =
      K.conway (partnerWeights ((halfTwists b t : ℕ) : ℤ)) := by
    have odd := partnerWeights_numerator_odd (halfTwists b t : ℤ)
    have hfrac := integer_plus_remainder (halfTwists b t : ℤ)
    have hodd : Odd (tangleAdd ((halfTwists b t : ℤ), 1) (37, 104)).1 := by
      exact hfrac ▸ odd
    have hc : Nat.Coprime (37 : ℤ).natAbs (104 : ℤ).natAbs := by decide
    rw [RF.fill_chart _ _ _ hc hodd, hfrac, RK.closure_fraction _ odd]
    rfl
  have hv := RF.marked_fills (t : ℤ) P.residual_reference
  have hbc := RF.marked_fills (t : ℤ) P.intermediate_first
  have hde := RF.marked_fills (t : ℤ) P.intermediate_second
  simp only [ExteriorAction.onKnot, ExteriorAction.onSlope, id, reflect_twistSlope] at hv hbc hde
  rw [htail] at hv
  have hstart := RF.split_fills (t : ℤ) P.split_start
  rw [hv] at hstart
  have hab := RF.crossing_fills (t : ℤ) P.first_switch
  have hcd := RF.crossing_fills (t : ℤ) P.second_switch
  have hef := RK.mirror_switch (RF.crossing_fills (- (t : ℤ)) P.third_switch)
  rw [hstart, hbc] at hab
  rw [hde] at hcd
  rw [RF.unlink_fills (- (t : ℤ)) P.final_unlink, RK.mirror_unknot] at hef
  exact .step hab (.step hcd (.step hef (.done _)))

/-- The family deduction only consumes two unfilled finite templates and
uniform filling rules. No filled identifications or upper bounds are inputs. -/
theorem connected_sum_upper_bound (RK : KnotReferences K) (RF : FillingReferences A)
    (templates : ∀ b : Fin 2, ParityTemplate A b) (m : ℕ) :
    K.unknotting (K.connectedSum K.trefoil (partner K m)) ≤ 3 := by
  have M := filled_movie RK RF (templates (parity m)) (fullTwists m)
  rw [halfTwists_decompose m] at M
  exact RK.path_bound M

end Trefoil.Section2Topology
