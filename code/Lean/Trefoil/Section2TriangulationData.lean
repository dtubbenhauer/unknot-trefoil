import Trefoil.Section2TriangulationData.Base
import Trefoil.Section2TriangulationData.NamedPartnerReference
import Trefoil.Section2TriangulationData.NamedPartnerTable
/-! The checked exterior data from the two parity cases and filled first example. -/

namespace Trefoil.Section2TriangulationData

open Trefoil.Section2Triangulations

/-- The three diagrams to compare, for either parity of the twist parameter. -/
def data (b : Fin 2) (k : Match) : Certificate :=
  if (b : Nat) = 0 then
    match k with
    | .partnerReference => partnerReference0
    | .firstIntermediate => firstIntermediate0
    | .secondIntermediate => secondIntermediate0
  else
    match k with
    | .partnerReference => partnerReference1
    | .firstIntermediate => firstIntermediate1
    | .secondIntermediate => secondIntermediate1

theorem data_reverses (b : Fin 2) (k : Match) :
    (data b k).reverse = k.reverses := by
  unfold data
  split <;> cases k <;> rfl

theorem data_checked (b : Fin 2) (k : Match) : Checked (data b k) := by
  unfold data
  split <;> cases k
  · exact partnerReference0_checked
  · exact firstIntermediate0_checked
  · exact secondIntermediate0_checked
  · exact partnerReference1_checked
  · exact firstIntermediate1_checked
  · exact secondIntermediate1_checked

theorem data_slopes (b : Fin 2) (k : Match) : hasMarkedSlope (data b k) := by
  unfold data
  split <;> cases k
  · exact partnerReference0_slopes
  · exact firstIntermediate0_slopes
  · exact secondIntermediate0_slopes
  · exact partnerReference1_slopes
  · exact firstIntermediate1_slopes
  · exact secondIntermediate1_slopes

noncomputable def markedIso (b : Fin 2) (m : Match) :
    let c := data b m
    MarkedIsomorphism c.source c.target c.tetMap c.reverse
      c.sourceMarking c.targetMarking c.peripheral :=
  (data_checked b m).markedIso

end Trefoil.Section2TriangulationData
