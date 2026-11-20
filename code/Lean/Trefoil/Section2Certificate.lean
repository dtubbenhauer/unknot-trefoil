import Trefoil.Section2Topology
import Trefoil.Section2SwitchData
import Trefoil.Section2TriangulationData
import Trefoil.Section2ReferenceTangle
import Trefoil.Section2DiagramDomainData

/-!
# Connecting the finite Section 2 certificates

The ten marked exterior computations and the planar diagrams used by the
paper are materialized as Lean data. Generic interpretation of diagrams
and triangulations is explicit. The missing link-to-exterior identification
is a typed obligation on the recorded triangulations, at the point where
a checked planar diagram is compared to a checked triangulation.
-/

namespace Trefoil.Section2Certificate

open Section2Topology Section2DiagramMoves Section2DiagramData Section2Switches
  Section2SwitchData Section2Triangulations Section2TriangulationData Section2ReferenceTangle

inductive Role
  | a | b | c | d | e | f | residual | reference
  deriving DecidableEq

/-- An explicitly marked dart on the crossing-circle component. -/
structure MarkedDiagram where
  diagram : Diagram
  axis : Dart

set_option maxRecDepth 20000
set_option maxHeartbeats 0

def evenDiagram : Role → MarkedDiagram
  | .a => ⟨evenStart, evenAAxis⟩
  | .b => ⟨evenB, evenBAxis⟩
  | .c => ⟨evenC, evenCAxis⟩
  | .d => ⟨evenD, evenDAxis⟩
  | .e => ⟨evenE, evenEAxis⟩
  | .f => ⟨evenEnd, evenFAxis⟩
  | .residual => ⟨evenPartner, evenPartnerAxis⟩
  | .reference => ⟨evenReference, evenReferenceAxis⟩

def oddDiagram : Role → MarkedDiagram
  | .a => ⟨oddStart, oddAAxis⟩
  | .b => ⟨oddB, oddBAxis⟩
  | .c => ⟨oddC, oddCAxis⟩
  | .d => ⟨oddD, oddDAxis⟩
  | .e => ⟨oddE, oddEAxis⟩
  | .f => ⟨oddEnd, oddFAxis⟩
  | .residual => ⟨oddPartner, oddPartnerAxis⟩
  | .reference => ⟨oddReference, oddReferenceAxis⟩

def diagram (b : Fin 2) : Role → MarkedDiagram :=
  if b.val = 0 then evenDiagram else oddDiagram

def evenRaw : Role → MarkedDiagram
  | .a => evenDiagram .a
  | .b => ⟨evenBRaw, evenBRawAxis⟩
  | .c => ⟨evenCRaw, evenCRawAxis⟩
  | .d => ⟨evenDRaw, evenDRawAxis⟩
  | .e => ⟨evenERaw, evenERawAxis⟩
  | .f => evenDiagram .f
  | .residual => ⟨evenPartnerRaw, evenPartnerRawAxis⟩
  | .reference => ⟨evenReferenceRaw, evenReferenceRawAxis⟩

def oddRaw : Role → MarkedDiagram
  | .a => oddDiagram .a
  | .b => ⟨oddBRaw, oddBRawAxis⟩
  | .c => ⟨oddCRaw, oddCRawAxis⟩
  | .d => ⟨oddDRaw, oddDRawAxis⟩
  | .e => ⟨oddERaw, oddERawAxis⟩
  | .f => oddDiagram .f
  | .residual => ⟨oddPartnerRaw, oddPartnerRawAxis⟩
  | .reference => ⟨oddReferenceRaw, oddReferenceRawAxis⟩

def rawDiagram (b : Fin 2) : Role → MarkedDiagram :=
  if b.val = 0 then evenRaw else oddRaw

def sourceRole : Match → Role
  | .partnerReference => .residual
  | .firstIntermediate => .b
  | .secondIntermediate => .d

def targetRole : Match → Role
  | .partnerReference => .reference
  | .firstIntermediate => .c
  | .secondIntermediate => .e

def action (reverse : Bool) : ExteriorAction := if reverse then .reverse else .preserve

variable {K : KnotGeometry} {A : AugmentedGeometry K}

/-- The intended interpretations read planar diagrams of knots or of two
components with the crossing-circle component selected by the marked dart.
The exterior relation includes the realization of each peripheral curve
and identification of the cusp of the marked component. -/
structure DiagramGeometry (A : AugmentedGeometry K) where
  knot : Diagram → K.Knot
  augmented : Diagram → Dart → A.Link
  hasMarkedExterior : A.Link → Triangulation → CuspMarking → ℕ → Prop
  hasKnotExterior : K.Knot → Triangulation → CuspMarking → Prop

abbrev DiagramGeometry.marked (I : DiagramGeometry A) (d : MarkedDiagram) : A.Link :=
  I.augmented d.diagram d.axis

/-- Uniform geometric interpretation of local diagram moves, marked cuts
and triangulation isomorphisms. Each implication is independent of the
particular two-bridge family. -/
structure DiagramReferences (I : DiagramGeometry A) where
  ordinary_move : ∀ D E move, D.knotDiagram = true → E.knotDiagram = true →
    checkMove D E move = true → I.knot D = I.knot E
  marked_move : ∀ D E move a b, D.markedDiagram a = true → E.markedDiagram b = true →
    checkMove D E move = true → Move.transportAnchor a move = some b →
    I.augmented D a = I.augmented E b
  split : ∀ D a b c L R, D.markedDiagram c = true → L.knotDiagram = true →
    R.markedDiagram c = true → D.checkSplit a b (some c) L R = true →
    A.splitOff (I.augmented D c) (I.knot L) (I.augmented R c)
  terminal : ∀ D axis trace, D.markedDiagram axis = true → CertifiedMoves D trace →
    Trace.withComponents D 2 trace = true → Trace.endpoint D trace = ⟨[], 2⟩ →
    A.terminalUnlink (I.augmented D axis)
  switch : ∀ D E i a b p, D.markedDiagram a = true → E.markedDiagram b = true →
    checkSwitch D E i (some a) (some b) p = true →
    A.crossingAway (I.augmented D a) (I.augmented E b)
  ordinary_split : ∀ D a b L R, D.knotDiagram = true → L.knotDiagram = true →
    R.knotDiagram = true → D.checkSplit a b none L R = true →
    I.knot D = K.connectedSum (I.knot L) (I.knot R)
  ordinary_terminal : ∀ D trace, CertifiedMoves D trace → Trace.withComponents D 1 trace = true →
    Trace.endpoint D trace = ⟨[], 1⟩ → I.knot D = K.unknot
  ordinary_switch : ∀ D E i p, D.knotDiagram = true → E.knotDiagram = true →
    checkSwitch D E i none none p = true → K.switch (I.knot D) (I.knot E)
  ordinary_iso : ∀ (c : Certificate) l r,
    I.hasKnotExterior l c.source c.sourceMarking →
    I.hasKnotExterior r c.target c.targetMarking →
    MarkedIsomorphism c.source c.target c.tetMap c.reverse
      c.sourceMarking c.targetMarking c.peripheral →
    hasMarkedSlope c → l = (action c.reverse).onKnot K r
  ordinary_chart : ∀ (twists : ℤ) (tail : List ℤ),
    Odd (Section2Arithmetic.tangleAdd (twists, 1) (Arithmetic.plusPair tail)).1 →
    I.knot (ordinaryReference twists tail) =
      K.numerator (Section2Arithmetic.tangleAdd (twists, 1) (Arithmetic.plusPair tail))
  axis_chart : ∀ (b : Fin 2) (tail : List ℤ),
    Nat.Coprime (Arithmetic.plusPair tail).1.natAbs (Arithmetic.plusPair tail).2.natAbs →
    Odd (Section2Arithmetic.tangleAdd ((b.val : ℤ), 1) (Arithmetic.plusPair tail)).1 →
    I.augmented (axisChartDiagram b.val tail) builtReferenceAxis =
      A.axisChart b (Arithmetic.plusPair tail)
  augmented_iso : ∀ (c : Certificate) l r,
    I.hasMarkedExterior l c.source c.sourceMarking c.sourceAxis →
    I.hasMarkedExterior r c.target c.targetMarking c.targetAxis →
    MarkedIsomorphism c.source c.target c.tetMap c.reverse
      c.sourceMarking c.targetMarking c.peripheral →
    hasMarkedSlope c → A.markedExterior (action c.reverse) l r

theorem diagram_to_raw {I : DiagramGeometry A} (R : DiagramReferences I)
    (b : Fin 2) (r : Role) : I.marked (diagram b r) = I.marked (rawDiagram b r) := by
  by_cases hb : b.val = 0
  · cases r
    · simp only [diagram, rawDiagram, if_pos hb, evenRaw]
    · simpa only [diagram, rawDiagram, if_pos hb, evenDiagram, evenRaw] using
        evenBRawChecked.markedPlanarSound I.augmented R.marked_move evenBRawAnchorChecked evenBRawTraceDomain
    · simpa only [diagram, rawDiagram, if_pos hb, evenDiagram, evenRaw] using
        evenCRawChecked.markedPlanarSound I.augmented R.marked_move evenCRawAnchorChecked evenCRawTraceDomain
    · simpa only [diagram, rawDiagram, if_pos hb, evenDiagram, evenRaw] using
        evenDRawChecked.markedPlanarSound I.augmented R.marked_move evenDRawAnchorChecked evenDRawTraceDomain
    · simpa only [diagram, rawDiagram, if_pos hb, evenDiagram, evenRaw] using
        evenERawChecked.markedPlanarSound I.augmented R.marked_move evenERawAnchorChecked evenERawTraceDomain
    · simp only [diagram, rawDiagram, if_pos hb, evenRaw]
    · simpa only [diagram, rawDiagram, if_pos hb, evenDiagram, evenRaw] using
        evenPartnerRawChecked.markedPlanarSound I.augmented R.marked_move evenPartnerRawAnchorChecked evenPartnerRawTraceDomain
    · simpa only [diagram, rawDiagram, if_pos hb, evenDiagram, evenRaw] using
        evenReferenceRawChecked.markedPlanarSound I.augmented R.marked_move evenReferenceRawAnchorChecked evenReferenceRawTraceDomain
  · cases r
    · simp only [diagram, rawDiagram, if_neg hb, oddRaw]
    · simpa only [diagram, rawDiagram, if_neg hb, oddDiagram, oddRaw] using
        oddBRawChecked.markedPlanarSound I.augmented R.marked_move oddBRawAnchorChecked oddBRawTraceDomain
    · simpa only [diagram, rawDiagram, if_neg hb, oddDiagram, oddRaw] using
        oddCRawChecked.markedPlanarSound I.augmented R.marked_move oddCRawAnchorChecked oddCRawTraceDomain
    · simpa only [diagram, rawDiagram, if_neg hb, oddDiagram, oddRaw] using
        oddDRawChecked.markedPlanarSound I.augmented R.marked_move oddDRawAnchorChecked oddDRawTraceDomain
    · simpa only [diagram, rawDiagram, if_neg hb, oddDiagram, oddRaw] using
        oddERawChecked.markedPlanarSound I.augmented R.marked_move oddERawAnchorChecked oddERawTraceDomain
    · simp only [diagram, rawDiagram, if_neg hb, oddRaw]
    · simpa only [diagram, rawDiagram, if_neg hb, oddDiagram, oddRaw] using
        oddPartnerRawChecked.markedPlanarSound I.augmented R.marked_move oddPartnerRawAnchorChecked oddPartnerRawTraceDomain
    · simpa only [diagram, rawDiagram, if_neg hb, oddDiagram, oddRaw] using
        oddReferenceRawChecked.markedPlanarSound I.augmented R.marked_move oddReferenceRawAnchorChecked oddReferenceRawTraceDomain

/-- The precise compatibility obligations across the diagram/exterior
interface. The finite triangulation statements checked in this archive
refer to explicit face arrays and peripheral chains. This structure is
where those arrays are attached to the exterior of each planar diagram. -/
structure ExteriorBridges (I : DiagramGeometry A) : Prop where
  source : ∀ b m, let c := data b m
    I.hasMarkedExterior (I.marked (rawDiagram b (sourceRole m))) c.source c.sourceMarking c.sourceAxis
  target : ∀ b m, let c := data b m
    I.hasMarkedExterior (I.marked (rawDiagram b (targetRole m))) c.target c.targetMarking c.targetAxis

/-- The marked maps follow from the kernel-checked triangulations once the
framed exteriors are realized. The maps are concrete and do not depend on
the number of full twists. -/
theorem exterior_identification {I : DiagramGeometry A} (R : DiagramReferences I)
    (E : ExteriorBridges I) (b : Fin 2) (m : Match) :
    A.markedExterior (action m.reverses)
      (I.marked (diagram b (sourceRole m))) (I.marked (diagram b (targetRole m))) := by
  have h := R.augmented_iso (data b m) _ _ (E.source b m) (E.target b m)
    (markedIso b m) (data_slopes b m)
  simpa only [← diagram_to_raw R b (sourceRole m), ← diagram_to_raw R b (targetRole m),
    data_reverses b m] using h

/-- The recorded reference diagram is the explicit tangle construction.
The two comparisons are genuine planar relabelings preserving the axis. -/
theorem reference_chart {I : DiagramGeometry A} (R : DiagramReferences I) (b : Fin 2) :
    I.marked (diagram b .reference) = A.axisChart b (37, 104) := by
  have ho : Odd (Section2Arithmetic.tangleAdd ((b.val : ℤ), 1)
      (Arithmetic.plusPair remainderWeights)).1 := by
    rw [remainder_fraction, Section2Arithmetic.integer_plus_remainder]
    exact Section2Arithmetic.partnerWeights_numerator_odd (b.val : ℤ)
  have hc : Nat.Coprime (Arithmetic.plusPair remainderWeights).1.natAbs
      (Arithmetic.plusPair remainderWeights).2.natAbs := by decide
  have h := R.axis_chart b remainderWeights hc ho
  rw [remainder_fraction] at h
  change I.augmented (builtReference b) builtReferenceAxis = _ at h
  have hr : I.augmented (builtReference b) builtReferenceAxis = I.marked (diagram b .reference) := by
    have := b.isLt
    have hb : b = 0 ∨ b = 1 := by
      by_cases he : b.val = 0
      · exact Or.inl (Fin.ext he)
      · exact Or.inr (Fin.ext (by change b.val = 1; omega))
    rcases hb with rfl | rfl
    · exact R.marked_move _ _ (.relabel (referenceRelabel 0)) _ _
        evenBuiltReferenceDomain evenReferenceDomain evenReference_constructor (congrArg some evenReference_axis)
    · exact R.marked_move _ _ (.relabel (referenceRelabel 1)) _ _
        oddBuiltReferenceDomain oddReferenceDomain oddReference_constructor (congrArg some oddReference_axis)
  exact hr.symm.trans h

/-- The two split spheres, with the marked axis transported along the
checked initial simplification and lying in the residual piece. -/
theorem split_start {I : DiagramGeometry A} (R : DiagramReferences I) (htrefoil : I.knot trefoilModel = K.trefoil)
    (b : Fin 2) :
    A.splitOff (I.marked (diagram b .a)) K.trefoil (I.marked (diagram b .residual)) := by
  by_cases h : b.val = 0
  · have htrace := evenStartChecked.markedPlanarSound I.augmented R.marked_move evenAnchorChecked evenStartDomain
    have hcut := R.split _ _ _ _ _ _ evenReducedStartDomain evenTrefoilDomain evenPartnerDomain evenSplitChecked
    have ht := evenTrefoilChecked.knotSound I.knot R.ordinary_move evenTrefoilTraceDomain
    change I.knot evenTrefoil = I.knot trefoilModel at ht
    rw [ht, htrefoil, ← htrace] at hcut
    simpa only [diagram, if_pos h, evenDiagram] using hcut
  · have htrace := oddStartChecked.markedPlanarSound I.augmented R.marked_move oddAnchorChecked oddStartDomain
    have hcut := R.split _ _ _ _ _ _ oddReducedStartDomain oddTrefoilDomain oddPartnerDomain oddSplitChecked
    have ht := oddTrefoilChecked.knotSound I.knot R.ordinary_move oddTrefoilTraceDomain
    change I.knot oddTrefoil = I.knot trefoilModel at ht
    rw [ht, htrefoil, ← htrace] at hcut
    simpa only [diagram, if_neg h, oddDiagram] using hcut

/-- Uniform assembly of the witnessed finite parity templates. -/
def realized_template {I : DiagramGeometry A} (R : DiagramReferences I) (E : ExteriorBridges I)
    (htrefoil : I.knot trefoilModel = K.trefoil) (b : Fin 2) : ParityTemplate A b where
  start := I.marked (diagram b .a)
  afterFirst := I.marked (diagram b .b)
  beforeSecond := I.marked (diagram b .c)
  afterSecond := I.marked (diagram b .d)
  beforeThird := I.marked (diagram b .e)
  finish := I.marked (diagram b .f)
  residual := I.marked (diagram b .residual)
  first_switch := by
    by_cases h : b.val = 0
    · simpa only [diagram, if_pos h, evenDiagram] using R.switch _ _ _ _ _ _ evenADomain evenBDomain evenAB_checked
    · simpa only [diagram, if_neg h, oddDiagram] using R.switch _ _ _ _ _ _ oddADomain oddBDomain oddAB_checked
  second_switch := by
    by_cases h : b.val = 0
    · simpa only [diagram, if_pos h, evenDiagram] using R.switch _ _ _ _ _ _ evenCDomain evenDDomain evenCD_checked
    · simpa only [diagram, if_neg h, oddDiagram] using R.switch _ _ _ _ _ _ oddCDomain oddDDomain oddCD_checked
  third_switch := by
    by_cases h : b.val = 0
    · simpa only [diagram, if_pos h, evenDiagram] using R.switch _ _ _ _ _ _ evenEDomain evenFDomain evenEF_checked
    · simpa only [diagram, if_neg h, oddDiagram] using R.switch _ _ _ _ _ _ oddEDomain oddFDomain oddEF_checked
  split_start := split_start R htrefoil b
  final_unlink := by
    by_cases h : b.val = 0
    · simpa only [diagram, if_pos h, evenDiagram] using
        R.terminal evenEnd evenFAxis evenEndTrace evenFDomain evenEndChecked evenEndDomain evenEndUnlink
    · simpa only [diagram, if_neg h, oddDiagram] using
        R.terminal oddEnd oddFAxis oddEndTrace oddFDomain oddEndChecked oddEndDomain oddEndUnlink
  residual_reference := by
    have he := exterior_identification R E b .partnerReference
    change A.markedExterior .reverse (I.marked (diagram b .residual))
      (I.marked (diagram b .reference)) at he
    simpa only [reference_chart R b] using he
  intermediate_first := exterior_identification R E b .firstIntermediate
  intermediate_second := exterior_identification R E b .secondIntermediate

/-- The Section 2 upper bound from the concrete, checked witnesses and the
explicit geometric interpretation obligations. -/
theorem family_upper_bound
    {I : DiagramGeometry A} (RK : KnotReferences K) (RF : FillingReferences A)
    (R : DiagramReferences I) (E : ExteriorBridges I)
    (htrefoil : I.knot trefoilModel = K.trefoil) (m : ℕ) :
    K.unknotting (K.connectedSum K.trefoil (partner K m)) ≤ 3 :=
  connected_sum_upper_bound RK RF (realized_template R E htrefoil) m

/-- The four additional exterior matches for the filled first example. -/
inductive SeedMatch
  | residualReference | residualTable | first | second
  deriving DecidableEq

def SeedMatch.certificate : SeedMatch → Certificate
  | .residualReference => partnerReference2
  | .residualTable => partnerTable2
  | .first => firstIntermediate2
  | .second => secondIntermediate2

def SeedMatch.source : SeedMatch → Diagram
  | .residualReference | .residualTable => seedPartner
  | .first => seedB
  | .second => seedD

def SeedMatch.target : SeedMatch → Diagram
  | .residualReference => seedReference
  | .residualTable => seedTable
  | .first => seedC
  | .second => seedE

def SeedMatch.sourceRaw : SeedMatch → Diagram
  | .residualReference | .residualTable => seedPartnerRaw
  | .first => seedBRaw
  | .second => seedDRaw

def SeedMatch.targetRaw : SeedMatch → Diagram
  | .residualReference => seedReferenceRaw
  | .residualTable => seedTableRaw
  | .first => seedCRaw
  | .second => seedERaw

theorem SeedMatch.checked (m : SeedMatch) : Checked m.certificate := by
  cases m
  · exact partnerReference2_checked
  · exact partnerTable2_checked
  · exact firstIntermediate2_checked
  · exact secondIntermediate2_checked

theorem SeedMatch.slopes (m : SeedMatch) : hasMarkedSlope m.certificate := by
  cases m
  · exact partnerReference2_slopes
  · exact partnerTable2_slopes
  · exact firstIntermediate2_slopes
  · exact secondIntermediate2_slopes

/-- The corresponding diagram-to-marked-exterior obligations for the
independently replayed filled first example. -/
structure SeedExteriorBridges (I : DiagramGeometry A) : Prop where
  source : ∀ m : SeedMatch, I.hasKnotExterior (I.knot m.sourceRaw)
    m.certificate.source m.certificate.sourceMarking
  target : ∀ m : SeedMatch, I.hasKnotExterior (I.knot m.targetRaw)
    m.certificate.target m.certificate.targetMarking

theorem seed_identification {I : DiagramGeometry A} (R : DiagramReferences I)
    (E : SeedExteriorBridges I) (m : SeedMatch) :
    I.knot m.source = (action m.certificate.reverse).onKnot K (I.knot m.target) := by
  have hs : I.knot m.source = I.knot m.sourceRaw := by
    cases m
    · exact seedPartnerRawChecked.knotSound I.knot R.ordinary_move seedPartnerRawTraceDomain
    · exact seedPartnerRawChecked.knotSound I.knot R.ordinary_move seedPartnerRawTraceDomain
    · exact seedBRawChecked.knotSound I.knot R.ordinary_move seedBRawTraceDomain
    · exact seedDRawChecked.knotSound I.knot R.ordinary_move seedDRawTraceDomain
  have ht : I.knot m.target = I.knot m.targetRaw := by
    cases m
    · exact seedReferenceRawChecked.knotSound I.knot R.ordinary_move seedReferenceRawTraceDomain
    · exact seedTableRawChecked.knotSound I.knot R.ordinary_move seedTableRawTraceDomain
    · exact seedCRawChecked.knotSound I.knot R.ordinary_move seedCRawTraceDomain
    · exact seedERawChecked.knotSound I.knot R.ordinary_move seedERawTraceDomain
  rw [hs, ht]
  exact R.ordinary_iso m.certificate _ _ (E.source m) (E.target m) m.checked.markedIso m.slopes

/-- The named first example has the orientation-reversed table diagram
as its partner. The checked diagram and exterior witnesses give the
three individual crossing changes, independently of the parity proof. -/
theorem seed_movie {I : DiagramGeometry A} (RK : KnotReferences K)
    (R : DiagramReferences I) (E : SeedExteriorBridges I)
    (ht : I.knot trefoilModel = K.trefoil) :
    Changes K.switch 3 (K.connectedSum K.trefoil (K.mirror (I.knot seedTable))) K.unknot := by
  have htrace := seedStartChecked.knotSound I.knot R.ordinary_move seedStartDomain
  have hsplit := R.ordinary_split _ _ _ _ _ seedReducedStartDomain seedTrefoilDomain seedPartnerDomain seedSplitChecked
  have hTrefoil := seedTrefoilChecked.knotSound I.knot R.ordinary_move seedTrefoilTraceDomain
  change I.knot seedTrefoil = I.knot trefoilModel at hTrefoil
  rw [hTrefoil, ht] at hsplit
  have hp := seed_identification R E .residualTable
  change I.knot seedPartner = K.mirror (I.knot seedTable) at hp
  have hab := R.ordinary_switch _ _ _ _ seedADomain seedBDomain seedAB_checked
  rw [htrace, hsplit, hp] at hab
  have hbc := seed_identification R E .first
  change I.knot seedB = I.knot seedC at hbc
  rw [hbc] at hab
  have hcd := R.ordinary_switch _ _ _ _ seedCDomain seedDDomain seedCD_checked
  have hde := seed_identification R E .second
  change I.knot seedD = K.mirror (I.knot seedE) at hde
  rw [hde] at hcd
  have hef := RK.mirror_switch (R.ordinary_switch _ _ _ _ seedEDomain seedFDomain seedEF_checked)
  rw [R.ordinary_terminal _ _ seedEndChecked seedEndDomain seedEndUnlink, RK.mirror_unknot] at hef
  exact .step hab (.step hcd (.step hef (.done _)))

/-- Both exterior comparisons of the residual filled example reverse
orientation, so the code's reference closure and the table diagram give
the same mirror partner. -/
theorem seed_reference_agrees {I : DiagramGeometry A} (R : DiagramReferences I)
    (E : SeedExteriorBridges I) :
    K.mirror (I.knot seedReference) = K.mirror (I.knot seedTable) := by
  have hW := seed_identification R E .residualReference
  have hT := seed_identification R E .residualTable
  exact hW.symm.trans hT

/-- The first partner defined by the homogeneous fraction agrees with the
mirrored table diagram chosen by the seed proof. -/
theorem seed_partner_is_table {I : DiagramGeometry A} (RK : KnotReferences K)
    (R : DiagramReferences I) (E : SeedExteriorBridges I) :
    partner K 2 = K.mirror (I.knot seedTable) := by
  have hc : Odd (Arithmetic.plusPair (Section2Arithmetic.partnerWeights 2)).1 :=
    Section2Arithmetic.partnerWeights_numerator_odd 2
  have hp := Section2Arithmetic.integer_plus_remainder 2
  have hn : Odd (Section2Arithmetic.tangleAdd (2, 1) (Arithmetic.plusPair remainderWeights)).1 := by
    rw [remainder_fraction, hp]
    exact hc
  have hr := R.ordinary_chart 2 remainderWeights hn
  rw [remainder_fraction, hp] at hr
  change _ = K.numerator (Arithmetic.plusPair (Section2Arithmetic.partnerWeights 2)) at hr
  rw [← RK.closure_fraction _ hc] at hr
  have hs : I.knot (ordinaryReference 2 remainderWeights) = I.knot seedReference :=
    R.ordinary_move _ _ (.relabel seedReferenceRelabel)
      seedReference_constructor_domain seedReferenceDomain seedReference_constructor
  have he := hr.symm.trans hs
  exact (congrArg K.mirror he).trans (seed_reference_agrees R E)

end Trefoil.Section2Certificate
