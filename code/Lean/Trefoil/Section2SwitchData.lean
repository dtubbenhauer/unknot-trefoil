import Trefoil.Section2Switches
import Trefoil.Section2DiagramData

/-! Finite crossing-switch witnesses for the three replays. -/

namespace Trefoil.Section2SwitchData
open Section2DiagramMoves Section2DiagramData Section2Switches

def evenAB : List (Dart × Dart) := [(36, 39), (37, 36), (38, 37), (39, 38)]
theorem evenAB_checked : checkSwitch evenStart evenB 9
    (some evenAAxis) (some evenBAxis) evenAB = true := by decide

def evenCD : List (Dart × Dart) := [(32, 33), (33, 34), (34, 35), (35, 32)]
theorem evenCD_checked : checkSwitch evenC evenD 8
    (some evenCAxis) (some evenDAxis) evenCD = true := by decide

def evenEF : List (Dart × Dart) := [(16, 19), (17, 16), (18, 17), (19, 18)]
theorem evenEF_checked : checkSwitch evenE evenEnd 4
    (some evenEAxis) (some evenFAxis) evenEF = true := by decide

def oddAB : List (Dart × Dart) := [(36, 39), (37, 36), (38, 37), (39, 38)]
theorem oddAB_checked : checkSwitch oddStart oddB 9
    (some oddAAxis) (some oddBAxis) oddAB = true := by decide

def oddCD : List (Dart × Dart) := [(32, 33), (33, 34), (34, 35), (35, 32)]
theorem oddCD_checked : checkSwitch oddC oddD 8
    (some oddCAxis) (some oddDAxis) oddCD = true := by decide

def oddEF : List (Dart × Dart) := [(16, 19), (17, 16), (18, 17), (19, 18)]
theorem oddEF_checked : checkSwitch oddE oddEnd 4
    (some oddEAxis) (some oddFAxis) oddEF = true := by decide

def seedAB : List (Dart × Dart) := [(36, 39), (37, 36), (38, 37), (39, 38)]
theorem seedAB_checked : checkSwitch seedStart seedB 9
    (none) (none) seedAB = true := by decide

def seedCD : List (Dart × Dart) := [(32, 33), (33, 34), (34, 35), (35, 32)]
theorem seedCD_checked : checkSwitch seedC seedD 8
    (none) (none) seedCD = true := by decide

def seedEF : List (Dart × Dart) := [(16, 19), (17, 16), (18, 17), (19, 18)]
theorem seedEF_checked : checkSwitch seedE seedEnd 4
    (none) (none) seedEF = true := by decide

end Trefoil.Section2SwitchData
