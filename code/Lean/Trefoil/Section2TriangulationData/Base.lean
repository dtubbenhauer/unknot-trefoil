import Trefoil.Section2Triangulations

/-!
# The finite exterior witnesses for Section 2

The six rows are the three marked exterior maps for each of the two
parities. The additional rows give the filled first example. Generated
from the fixed JSON snapshot by `render_section2_triangulations.py`.

The tetrahedron and peripheral equations are checked by Lean, using
explicit signed coefficients of dual cusp two-cells. The source diagrams,
decorated triangulation signatures and the Python exporter record the
provenance of the arrays. The theorem realizing the marked exteriors of
those diagrams is a separate topological input.
-/

namespace Trefoil.Section2TriangulationData

open Trefoil.Section2Triangulations

set_option maxRecDepth 100000
set_option maxHeartbeats 0

inductive Match
  | partnerReference
  | firstIntermediate
  | secondIntermediate
  deriving DecidableEq

def Match.reverses : Match → Bool
  | .partnerReference | .secondIntermediate => true
  | .firstIntermediate => false

structure Certificate where
  source : Triangulation
  target : Triangulation
  tetMap : Array TetImage
  sourceMarking : CuspMarking
  targetMarking : CuspMarking
  peripheral : PeripheralWitness
  sourceAxis : Nat
  targetAxis : Nat
  reverse : Bool

structure Checked (c : Certificate) : Prop where
  sourceValid : checkTriangulation c.source = true
  targetValid : checkTriangulation c.target = true
  faces : checkIso c.source c.target c.tetMap c.reverse = true
  sourceCurves : checkCuspMarking c.source c.sourceMarking = true
  targetCurves : checkCuspMarking c.target c.targetMarking = true
  peripheralMaps : checkPeripheral c.source c.target c.tetMap
    c.sourceMarking c.targetMarking c.peripheral = true

def hasMarkedSlope (c : Certificate) : Prop :=
  c.sourceAxis < c.sourceMarking.cuspCount ∧
  c.targetAxis < c.targetMarking.cuspCount ∧
  (peripheralImage c.peripheral c.sourceAxis).cusp = c.targetAxis ∧
  ∀ i : Fin c.sourceMarking.cuspCount,
    let m := peripheralImage c.peripheral i
    (m.mm = 1 ∨ m.mm = -1) ∧ m.ml = 0 ∧ m.lm = 0 ∧
      m.ll = if c.reverse then -m.mm else m.mm

instance (c : Certificate) : Decidable (hasMarkedSlope c) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- The axis matrix preserves the prescribed slope up to the sign of its
meridian coefficient, which does not change an unoriented primitive slope. -/
theorem markedSlope_image {c : Certificate} (h : hasMarkedSlope c) (t : Int) :
    let m := peripheralImage c.peripheral c.sourceAxis
    (m.mm * 1 + m.ml * t, m.lm * 1 + m.ll * t) =
      (m.mm, m.mm * (if c.reverse then -t else t)) := by
  have hm := h.2.2.2 ⟨c.sourceAxis, h.1⟩
  dsimp only at hm ⊢
  rcases hm with ⟨_, hml, hlm, hll⟩
  cases hd : c.reverse <;> simp [hml, hlm, hll, hd, Int.neg_mul, Int.mul_neg]

noncomputable def Checked.markedIso {c : Certificate} (h : Checked c) :
    MarkedIsomorphism c.source c.target c.tetMap c.reverse
      c.sourceMarking c.targetMarking c.peripheral :=
  checkMarkedIso_sound h.sourceValid h.targetValid h.faces
    h.sourceCurves h.targetCurves h.peripheralMaps

end Trefoil.Section2TriangulationData
