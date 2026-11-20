import Trefoil.Section2DiagramDataSeed
import Trefoil.Section2DiagramDomainDataOdd

/-! Checked diagram domains for the seed Section 2 case. -/

namespace Trefoil.Section2DiagramData

open Section2DiagramMoves

set_option maxHeartbeats 0
set_option maxRecDepth 20000

theorem seedADomain :
    seedA.knotDiagram = true := by decide +kernel

theorem seedBDomain :
    seedB.knotDiagram = true := by decide +kernel

theorem seedCDomain :
    seedC.knotDiagram = true := by decide +kernel

theorem seedDDomain :
    seedD.knotDiagram = true := by decide +kernel

theorem seedEDomain :
    seedE.knotDiagram = true := by decide +kernel

theorem seedFDomain :
    seedF.knotDiagram = true := by decide +kernel

theorem seedPartnerDomain :
    seedPartner.knotDiagram = true := by decide +kernel

theorem seedReferenceDomain :
    seedReference.knotDiagram = true := by decide +kernel

theorem seedTableDomain :
    seedTable.knotDiagram = true := by decide +kernel

theorem seedStartDomain :
    Trace.knot seedStart seedStartTrace = true := by decide +kernel

theorem seedEndDomain :
    Trace.knot seedEnd seedEndTrace = true := by decide +kernel

theorem seedTrefoilDomain :
    seedTrefoil.knotDiagram = true := by decide +kernel

theorem seedTrefoilTraceDomain :
    Trace.knot seedTrefoil [(seedTrefoilRelabel, trefoilModel)] = true := by decide +kernel

theorem seedReducedStartDomain :
    (Trace.endpoint seedStart seedStartTrace).knotDiagram = true := by decide +kernel

theorem seedPartnerRawDomain :
    seedPartnerRaw.knotDiagram = true := by decide +kernel

theorem seedPartnerRawTraceDomain :
    Trace.knot seedPartner [(seedPartnerRawRelabel, seedPartnerRaw)] = true := by decide +kernel

theorem seedReferenceRawDomain :
    seedReferenceRaw.knotDiagram = true := by decide +kernel

theorem seedReferenceRawTraceDomain :
    Trace.knot seedReference [(seedReferenceRawRelabel, seedReferenceRaw)] = true := by decide +kernel

theorem seedBRawDomain :
    seedBRaw.knotDiagram = true := by decide +kernel

theorem seedBRawTraceDomain :
    Trace.knot seedB [(seedBRawRelabel, seedBRaw)] = true := by decide +kernel

theorem seedCRawDomain :
    seedCRaw.knotDiagram = true := by decide +kernel

theorem seedCRawTraceDomain :
    Trace.knot seedC [(seedCRawRelabel, seedCRaw)] = true := by decide +kernel

theorem seedDRawDomain :
    seedDRaw.knotDiagram = true := by decide +kernel

theorem seedDRawTraceDomain :
    Trace.knot seedD [(seedDRawRelabel, seedDRaw)] = true := by decide +kernel

theorem seedERawDomain :
    seedERaw.knotDiagram = true := by decide +kernel

theorem seedERawTraceDomain :
    Trace.knot seedE [(seedERawRelabel, seedERaw)] = true := by decide +kernel

theorem seedTableRawDomain :
    seedTableRaw.knotDiagram = true := by decide +kernel

theorem seedTableRawTraceDomain :
    Trace.knot seedTable [(seedTableRawRelabel, seedTableRaw)] = true := by decide +kernel

end Trefoil.Section2DiagramData
