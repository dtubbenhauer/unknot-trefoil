import Trefoil.Section2DiagramDataOdd
import Trefoil.Section2DiagramDomainDataEven

/-! Checked diagram domains for the odd Section 2 case. -/

namespace Trefoil.Section2DiagramData

open Section2DiagramMoves

set_option maxHeartbeats 0
set_option maxRecDepth 20000

theorem oddADomain :
    oddA.markedDiagram oddAAxis = true := by decide +kernel

theorem oddBDomain :
    oddB.markedDiagram oddBAxis = true := by decide +kernel

theorem oddCDomain :
    oddC.markedDiagram oddCAxis = true := by decide +kernel

theorem oddDDomain :
    oddD.markedDiagram oddDAxis = true := by decide +kernel

theorem oddEDomain :
    oddE.markedDiagram oddEAxis = true := by decide +kernel

theorem oddFDomain :
    oddF.markedDiagram oddFAxis = true := by decide +kernel

theorem oddPartnerDomain :
    oddPartner.markedDiagram oddPartnerAxis = true := by decide +kernel

theorem oddReferenceDomain :
    oddReference.markedDiagram oddReferenceAxis = true := by decide +kernel

theorem oddStartDomain :
    Trace.marked oddStart oddAAxis oddStartTrace = true := by decide +kernel

theorem oddEndDomain :
    Trace.withComponents oddEnd 2 oddEndTrace = true := by decide +kernel

theorem oddEndPlanarDomain :
    Trace.planar oddEnd oddEndTrace = true := by decide +kernel

theorem oddTrefoilDomain :
    oddTrefoil.knotDiagram = true := by decide +kernel

theorem oddTrefoilTraceDomain :
    Trace.knot oddTrefoil [(oddTrefoilRelabel, trefoilModel)] = true := by decide +kernel

theorem oddReducedStartDomain :
    (Trace.endpoint oddStart oddStartTrace).markedDiagram oddPartnerAxis = true := by decide +kernel

theorem oddPartnerRawDomain :
    oddPartnerRaw.markedDiagram oddPartnerRawAxis = true := by decide +kernel

theorem oddPartnerRawTraceDomain :
    Trace.marked oddPartner oddPartnerAxis [(oddPartnerRawRelabel, oddPartnerRaw)] = true := by decide +kernel

theorem oddReferenceRawDomain :
    oddReferenceRaw.markedDiagram oddReferenceRawAxis = true := by decide +kernel

theorem oddReferenceRawTraceDomain :
    Trace.marked oddReference oddReferenceAxis [(oddReferenceRawRelabel, oddReferenceRaw)] = true := by decide +kernel

theorem oddBRawDomain :
    oddBRaw.markedDiagram oddBRawAxis = true := by decide +kernel

theorem oddBRawTraceDomain :
    Trace.marked oddB oddBAxis [(oddBRawRelabel, oddBRaw)] = true := by decide +kernel

theorem oddCRawDomain :
    oddCRaw.markedDiagram oddCRawAxis = true := by decide +kernel

theorem oddCRawTraceDomain :
    Trace.marked oddC oddCAxis [(oddCRawRelabel, oddCRaw)] = true := by decide +kernel

theorem oddDRawDomain :
    oddDRaw.markedDiagram oddDRawAxis = true := by decide +kernel

theorem oddDRawTraceDomain :
    Trace.marked oddD oddDAxis [(oddDRawRelabel, oddDRaw)] = true := by decide +kernel

theorem oddERawDomain :
    oddERaw.markedDiagram oddERawAxis = true := by decide +kernel

theorem oddERawTraceDomain :
    Trace.marked oddE oddEAxis [(oddERawRelabel, oddERaw)] = true := by decide +kernel

end Trefoil.Section2DiagramData
