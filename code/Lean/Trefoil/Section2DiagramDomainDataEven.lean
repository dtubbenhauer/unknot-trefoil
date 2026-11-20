import Trefoil.Section2DiagramDataEven
import Trefoil.Section2DiagramDomains

/-! Checked diagram domains for the even Section 2 case. -/

namespace Trefoil.Section2DiagramData

open Section2DiagramMoves

set_option maxHeartbeats 0
set_option maxRecDepth 20000

theorem evenADomain :
    evenA.markedDiagram evenAAxis = true := by decide +kernel

theorem evenBDomain :
    evenB.markedDiagram evenBAxis = true := by decide +kernel

theorem evenCDomain :
    evenC.markedDiagram evenCAxis = true := by decide +kernel

theorem evenDDomain :
    evenD.markedDiagram evenDAxis = true := by decide +kernel

theorem evenEDomain :
    evenE.markedDiagram evenEAxis = true := by decide +kernel

theorem evenFDomain :
    evenF.markedDiagram evenFAxis = true := by decide +kernel

theorem evenPartnerDomain :
    evenPartner.markedDiagram evenPartnerAxis = true := by decide +kernel

theorem evenReferenceDomain :
    evenReference.markedDiagram evenReferenceAxis = true := by decide +kernel

theorem evenStartDomain :
    Trace.marked evenStart evenAAxis evenStartTrace = true := by decide +kernel

theorem evenEndDomain :
    Trace.withComponents evenEnd 2 evenEndTrace = true := by decide +kernel

theorem evenEndPlanarDomain :
    Trace.planar evenEnd evenEndTrace = true := by decide +kernel

theorem evenTrefoilDomain :
    evenTrefoil.knotDiagram = true := by decide +kernel

theorem evenTrefoilTraceDomain :
    Trace.knot evenTrefoil [(evenTrefoilRelabel, trefoilModel)] = true := by decide +kernel

theorem evenReducedStartDomain :
    (Trace.endpoint evenStart evenStartTrace).markedDiagram evenPartnerAxis = true := by decide +kernel

theorem evenPartnerRawDomain :
    evenPartnerRaw.markedDiagram evenPartnerRawAxis = true := by decide +kernel

theorem evenPartnerRawTraceDomain :
    Trace.marked evenPartner evenPartnerAxis [(evenPartnerRawRelabel, evenPartnerRaw)] = true := by decide +kernel

theorem evenReferenceRawDomain :
    evenReferenceRaw.markedDiagram evenReferenceRawAxis = true := by decide +kernel

theorem evenReferenceRawTraceDomain :
    Trace.marked evenReference evenReferenceAxis [(evenReferenceRawRelabel, evenReferenceRaw)] = true := by decide +kernel

theorem evenBRawDomain :
    evenBRaw.markedDiagram evenBRawAxis = true := by decide +kernel

theorem evenBRawTraceDomain :
    Trace.marked evenB evenBAxis [(evenBRawRelabel, evenBRaw)] = true := by decide +kernel

theorem evenCRawDomain :
    evenCRaw.markedDiagram evenCRawAxis = true := by decide +kernel

theorem evenCRawTraceDomain :
    Trace.marked evenC evenCAxis [(evenCRawRelabel, evenCRaw)] = true := by decide +kernel

theorem evenDRawDomain :
    evenDRaw.markedDiagram evenDRawAxis = true := by decide +kernel

theorem evenDRawTraceDomain :
    Trace.marked evenD evenDAxis [(evenDRawRelabel, evenDRaw)] = true := by decide +kernel

theorem evenERawDomain :
    evenERaw.markedDiagram evenERawAxis = true := by decide +kernel

theorem evenERawTraceDomain :
    Trace.marked evenE evenEAxis [(evenERawRelabel, evenERaw)] = true := by decide +kernel

theorem trefoilModelDomain :
    trefoilModel.knotDiagram = true := by decide +kernel

end Trefoil.Section2DiagramData
