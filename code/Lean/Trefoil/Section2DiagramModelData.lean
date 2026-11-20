import Trefoil.Section2DiagramMoves

/-! The standard three-crossing trefoil diagram. -/

namespace Trefoil.Section2DiagramData

open Section2DiagramMoves

set_option maxHeartbeats 0
set_option maxRecDepth 20000

/-- The closure of the three-crossing two-strand braid with
Spherogram generator −1, in the manuscript's trefoil chirality. -/
def trefoilModel : Diagram := ⟨[some [11, 10, 5, 4], some [3, 2, 9, 8], some [7, 6, 1, 0]], 0⟩

end Trefoil.Section2DiagramData
