import Trefoil.Section2DiagramModelData

/-! Even endpoint and exterior-source diagram certificates. -/

namespace Trefoil.Section2DiagramData

open Section2DiagramMoves

set_option maxHeartbeats 0
set_option maxRecDepth 20000

def evenB : Diagram :=
  ⟨[some [13, 53, 9, 6], some [11, 42, 3, 8], some [7, 2, 43, 4], some [54, 0, 39, 17], some [55, 15, 35, 22], some [25, 48, 19, 26], some [57, 20, 23, 69], some [33, 56, 61, 34], some [38, 28, 31, 18], some [41, 49, 32, 14], some [46, 36, 5, 10], some [51, 50, 40, 52], some [21, 37, 45, 44], some [47, 1, 12, 16], some [29, 24, 76, 62], some [67, 30, 59, 64], some [63, 82, 73, 60], some [77, 27, 72, 78], some [70, 66, 81, 80], some [58, 68, 71, 83], some [75, 74, 65, 79]], 0⟩

def evenBAxis : Dart := 81

def evenC : Diagram :=
  ⟨[some [13, 53, 9, 6], some [11, 34, 3, 8], some [7, 2, 40, 4], some [17, 0, 31, 18], some [57, 12, 15, 69], some [25, 56, 61, 26], some [54, 20, 23, 30], some [33, 49, 27, 14], some [46, 28, 5, 37], some [47, 35, 43, 42], some [10, 52, 39, 38], some [51, 50, 32, 36], some [55, 29, 45, 44], some [41, 1, 24, 48], some [21, 16, 76, 62], some [67, 22, 59, 64], some [63, 82, 73, 60], some [77, 19, 72, 78], some [70, 66, 81, 80], some [58, 68, 71, 83], some [75, 74, 65, 79]], 0⟩

def evenCAxis : Dart := 81

def evenD : Diagram :=
  ⟨[some [13, 53, 9, 6], some [11, 35, 3, 8], some [7, 2, 40, 4], some [17, 0, 31, 18], some [57, 12, 15, 69], some [25, 56, 61, 26], some [54, 20, 23, 30], some [34, 49, 27, 14], some [37, 46, 28, 5], some [47, 32, 43, 42], some [10, 52, 39, 38], some [51, 50, 33, 36], some [55, 29, 45, 44], some [41, 1, 24, 48], some [21, 16, 76, 62], some [67, 22, 59, 64], some [63, 82, 73, 60], some [77, 19, 72, 78], some [70, 66, 81, 80], some [58, 68, 71, 83], some [75, 74, 65, 79]], 0⟩

def evenDAxis : Dart := 81

def evenE : Diagram :=
  ⟨[some [5, 12, 17, 22], some [9, 0, 41, 10], some [13, 4, 7, 14], some [1, 8, 11, 18], some [23, 2, 15, 40], some [58, 46, 3, 16], some [39, 30, 45, 48], some [35, 42, 25, 32], some [31, 38, 37, 28], some [43, 34, 33, 24], some [19, 6, 29, 36], some [49, 26, 21, 67], some [27, 44, 55, 54], some [71, 60, 51, 50], some [65, 64, 20, 63], some [53, 70, 69, 59], some [57, 56, 68, 47], some [66, 62, 61, 52]], 0⟩

def evenEAxis : Dart := 61

def evenReference : Diagram :=
  ⟨[some [11, 10, 16, 7], some [27, 12, 15, 3], some [14, 17, 1, 0], some [5, 28, 8, 6], some [2, 9, 23, 22], some [47, 24, 19, 18], some [21, 58, 29, 4], some [13, 26, 33, 32], some [31, 30, 37, 36], some [35, 34, 41, 40], some [39, 38, 63, 44], some [43, 50, 49, 20], some [55, 46, 45, 52], some [51, 62, 59, 48], some [61, 60, 25, 54], some [57, 56, 53, 42]], 0⟩

def evenReferenceAxis : Dart := 7

def evenStart : Diagram :=
  ⟨[some [13, 53, 9, 6], some [11, 42, 3, 8], some [7, 2, 43, 4], some [54, 0, 36, 17], some [55, 15, 35, 22], some [25, 48, 19, 26], some [57, 20, 23, 69], some [33, 56, 61, 34], some [39, 28, 31, 18], some [14, 41, 49, 32], some [46, 37, 5, 10], some [51, 50, 40, 52], some [21, 38, 45, 44], some [47, 1, 12, 16], some [29, 24, 76, 62], some [67, 30, 59, 64], some [63, 82, 73, 60], some [77, 27, 72, 78], some [70, 66, 81, 80], some [58, 68, 71, 83], some [75, 74, 65, 79]], 0⟩

def evenStartTrace : Trace := [
  (.arc false [52, 12, 36] [84], ⟨[some [17, 16, 9, 6], some [11, 42, 3, 8], some [7, 2, 43, 4], none, some [1, 0, 35, 22], some [25, 48, 19, 26], some [57, 20, 23, 69], some [33, 56, 61, 34], some [41, 28, 31, 18], none, some [87, 32, 5, 10], some [51, 50, 85, 84], some [21, 86, 45, 44], none, some [29, 24, 76, 62], some [67, 30, 59, 64], some [63, 82, 73, 60], some [77, 27, 72, 78], some [70, 66, 81, 80], some [58, 68, 71, 83], some [75, 74, 65, 79], some [47, 46, 49, 40]], 0⟩)]

theorem evenStartChecked : CertifiedMoves evenStart evenStartTrace := by decide +kernel

def evenAAxis : Dart := 81
def evenPartnerAxis : Dart := 81

theorem evenAnchorChecked :
    Trace.anchor evenStart evenAAxis evenStartTrace = some evenPartnerAxis := by decide +kernel

def evenTrefoil : Diagram :=
  ⟨[none, none, none, none, none, none, none, none, none, none, none, some [51, 50, 85, 84], some [87, 86, 45, 44], none, none, none, none, none, none, none, none, some [47, 46, 49, 48]], 0⟩

def evenTrefoilRelabel : Move :=
  .relabel [(44, 0), (45, 1), (46, 2), (47, 3), (48, 8), (49, 9), (50, 10), (51, 11), (84, 4), (85, 5), (86, 6), (87, 7)]

theorem evenTrefoilChecked :
    CertifiedMoves evenTrefoil [(evenTrefoilRelabel, trefoilModel)] := by decide +kernel

def evenPartner : Diagram :=
  ⟨[some [17, 16, 9, 6], some [11, 42, 3, 8], some [7, 2, 43, 4], none, some [1, 0, 35, 22], some [25, 40, 19, 26], some [57, 20, 23, 69], some [33, 56, 61, 34], some [41, 28, 31, 18], none, some [21, 32, 5, 10], none, none, none, some [29, 24, 76, 62], some [67, 30, 59, 64], some [63, 82, 73, 60], some [77, 27, 72, 78], some [70, 66, 81, 80], some [58, 68, 71, 83], some [75, 74, 65, 79]], 0⟩

def evenCutA : Dart := 21
def evenCutB : Dart := 87

theorem evenSplitChecked :
    (Trace.endpoint evenStart evenStartTrace).checkSplit evenCutA evenCutB (some evenPartnerAxis)
      evenTrefoil evenPartner = true := by decide +kernel

def evenEnd : Diagram :=
  ⟨[some [5, 12, 16, 22], some [9, 0, 41, 10], some [13, 4, 7, 14], some [1, 8, 11, 17], some [2, 15, 40, 23], some [58, 46, 3, 19], some [39, 30, 45, 48], some [35, 42, 25, 32], some [31, 38, 37, 28], some [43, 34, 33, 24], some [18, 6, 29, 36], some [49, 26, 21, 67], some [27, 44, 55, 54], some [71, 60, 51, 50], some [65, 64, 20, 63], some [53, 70, 69, 59], some [57, 56, 68, 47], some [66, 62, 61, 52]], 0⟩

def evenEndTrace : Trace := [
  (.riii 1 16 15, ⟨[some [18, 11, 40, 14], some [9, 16, 41, 10], some [17, 4, 7, 1], some [22, 19, 3, 23], some [5, 8, 0, 13], some [58, 46, 12, 15], some [39, 30, 45, 48], some [35, 42, 25, 32], some [31, 38, 37, 28], some [43, 34, 33, 24], some [2, 6, 29, 36], some [49, 26, 21, 67], some [27, 44, 55, 54], some [71, 60, 51, 50], some [65, 64, 20, 63], some [53, 70, 69, 59], some [57, 56, 68, 47], some [66, 62, 61, 52]], 0⟩),
  (.rii 22 12, ⟨[some [18, 11, 40, 58], some [9, 16, 41, 10], some [17, 4, 7, 1], none, some [5, 8, 0, 46], none, some [39, 30, 45, 48], some [35, 42, 25, 32], some [31, 38, 37, 28], some [43, 34, 33, 24], some [2, 6, 29, 36], some [49, 26, 19, 67], some [27, 44, 55, 54], some [71, 60, 51, 50], some [65, 64, 3, 63], some [53, 70, 69, 59], some [57, 56, 68, 47], some [66, 62, 61, 52]], 0⟩),
  (.riii 17 0 11, ⟨[some [5, 4, 16, 9], some [1, 0, 41, 17], some [46, 3, 19, 58], none, some [2, 7, 40, 10], none, some [39, 30, 45, 48], some [35, 42, 25, 32], some [31, 38, 37, 28], some [43, 34, 33, 24], some [18, 6, 29, 36], some [49, 26, 8, 67], some [27, 44, 55, 54], some [71, 60, 51, 50], some [65, 64, 11, 63], some [53, 70, 69, 59], some [57, 56, 68, 47], some [66, 62, 61, 52]], 0⟩),
  (.riii 40 6 17, ⟨[some [17, 41, 40, 9], some [43, 19, 36, 10], some [46, 3, 7, 58], none, some [42, 0, 29, 5], none, some [39, 30, 45, 48], some [35, 18, 25, 32], some [31, 38, 37, 28], some [6, 34, 33, 24], some [2, 1, 16, 4], some [49, 26, 8, 67], some [27, 44, 55, 54], some [71, 60, 51, 50], some [65, 64, 11, 63], some [53, 70, 69, 59], some [57, 56, 68, 47], some [66, 62, 61, 52]], 0⟩),
  (.rii 1 41, ⟨[none, some [9, 19, 36, 10], some [46, 4, 7, 58], none, some [17, 16, 29, 5], none, some [39, 30, 45, 48], some [35, 18, 25, 32], some [31, 38, 37, 28], some [6, 34, 33, 24], none, some [49, 26, 8, 67], some [27, 44, 55, 54], some [71, 60, 51, 50], some [65, 64, 11, 63], some [53, 70, 69, 59], some [57, 56, 68, 47], some [66, 62, 61, 52]], 0⟩),
  (.ri 16, ⟨[none, some [9, 29, 36, 10], some [46, 4, 7, 58], none, none, none, some [39, 30, 45, 48], some [35, 5, 25, 32], some [31, 38, 37, 28], some [6, 34, 33, 24], none, some [49, 26, 8, 67], some [27, 44, 55, 54], some [71, 60, 51, 50], some [65, 64, 11, 63], some [53, 70, 69, 59], some [57, 56, 68, 47], some [66, 62, 61, 52]], 0⟩),
  (.relabel [(4, 6), (5, 7), (6, 4), (7, 5), (8, 10), (9, 11), (10, 8), (11, 9), (24, 26), (25, 27), (26, 24), (27, 25), (28, 30), (29, 31), (30, 28), (31, 29), (32, 34), (33, 35), (34, 32), (35, 33), (36, 38), (37, 39), (38, 36), (39, 37), (44, 46), (45, 47), (46, 44), (47, 45), (48, 50), (49, 51), (50, 48), (51, 49), (52, 54), (53, 55), (54, 52), (55, 53), (56, 58), (57, 59), (58, 56), (59, 57), (60, 62), (61, 63), (62, 60), (63, 61), (64, 66), (65, 67), (66, 64), (67, 65), (68, 70), (69, 71), (70, 68), (71, 69)], ⟨[none, some [38, 8, 11, 31], some [5, 56, 44, 6], none, none, none, some [47, 50, 37, 28], some [27, 34, 33, 7], some [39, 30, 29, 36], some [35, 26, 4, 32], none, some [10, 65, 51, 24], some [53, 52, 25, 46], some [49, 48, 69, 62], some [9, 61, 67, 66], some [71, 57, 55, 68], some [70, 45, 59, 58], some [63, 54, 64, 60]], 0⟩),
  (.arc true [29, 7] [75], ⟨[none, none, some [73, 56, 44, 38], none, none, none, some [47, 50, 72, 33], none, some [39, 27, 75, 36], some [35, 74, 11, 32], none, some [10, 65, 51, 24], some [53, 52, 25, 46], some [49, 48, 69, 62], some [9, 61, 67, 66], some [71, 57, 55, 68], some [70, 45, 59, 58], some [63, 54, 64, 60], some [26, 8, 37, 34]], 0⟩),
  (.riii 75 26 33, ⟨[none, none, some [34, 56, 44, 38], none, none, none, some [74, 35, 37, 36], none, some [73, 50, 8, 25], some [27, 26, 11, 75], none, some [10, 65, 51, 72], some [53, 52, 33, 46], some [49, 48, 69, 62], some [9, 61, 67, 66], some [71, 57, 55, 68], some [70, 45, 59, 58], some [63, 54, 64, 60], some [47, 32, 24, 39]], 0⟩),
  (.riii 27 74 39, ⟨[none, none, some [34, 56, 44, 27], none, none, none, some [47, 38, 72, 11], none, some [39, 50, 8, 36], some [35, 73, 25, 32], none, some [10, 65, 51, 24], some [53, 52, 33, 46], some [49, 48, 69, 62], some [9, 61, 67, 66], some [71, 57, 55, 68], some [70, 45, 59, 58], some [63, 54, 64, 60], some [26, 37, 75, 74]], 0⟩),
  (.ri 74, ⟨[none, none, some [34, 56, 44, 27], none, none, none, some [47, 38, 37, 11], none, some [39, 50, 8, 36], some [35, 26, 25, 32], none, some [10, 65, 51, 24], some [53, 52, 33, 46], some [49, 48, 69, 62], some [9, 61, 67, 66], some [71, 57, 55, 68], some [70, 45, 59, 58], some [63, 54, 64, 60]], 0⟩),
  (.riii 47 10 27, ⟨[none, none, some [46, 25, 51, 38], none, none, none, some [65, 9, 45, 56], none, some [39, 50, 44, 36], some [35, 47, 11, 32], none, some [34, 26, 8, 37], some [53, 52, 33, 10], some [49, 48, 69, 62], some [27, 61, 67, 66], some [71, 57, 55, 68], some [70, 24, 59, 58], some [63, 54, 64, 60]], 0⟩),
  (.riii 11 46 37, ⟨[none, none, some [34, 36, 44, 35], none, none, none, some [65, 38, 37, 56], none, some [47, 50, 8, 11], some [9, 26, 25, 45], none, some [10, 39, 51, 32], some [53, 52, 33, 46], some [49, 48, 69, 62], some [27, 61, 67, 66], some [71, 57, 55, 68], some [70, 24, 59, 58], some [63, 54, 64, 60]], 0⟩),
  (.rii 11 35, ⟨[none, none, none, none, none, none, some [65, 38, 37, 56], none, none, some [50, 26, 25, 45], none, some [47, 39, 51, 44], some [53, 52, 36, 46], some [49, 48, 69, 62], some [27, 61, 67, 66], some [71, 57, 55, 68], some [70, 24, 59, 58], some [63, 54, 64, 60]], 0⟩),
  (.ri 47, ⟨[none, none, none, none, none, none, some [65, 38, 37, 56], none, none, some [50, 26, 25, 51], none, none, some [53, 52, 36, 39], some [49, 48, 69, 62], some [27, 61, 67, 66], some [71, 57, 55, 68], some [70, 24, 59, 58], some [63, 54, 64, 60]], 0⟩),
  (.rii 39 51, ⟨[none, none, none, none, none, none, some [65, 53, 52, 56], none, none, none, none, none, none, some [26, 25, 69, 62], some [27, 61, 67, 66], some [71, 57, 55, 68], some [70, 24, 59, 58], some [63, 54, 64, 60]], 0⟩),
  (.rii 25 53, ⟨[none, none, none, none, none, none, none, none, none, none, none, none, none, none, some [62, 61, 67, 66], some [71, 57, 56, 68], some [70, 69, 59, 58], some [63, 65, 64, 60]], 0⟩),
  (.rii 56 62, ⟨[none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, some [70, 69, 68, 71], some [66, 65, 64, 67]], 0⟩),
  (.rii 64 70, ⟨[], 2⟩)]

theorem evenEndChecked : CertifiedMoves evenEnd evenEndTrace := by decide +kernel

def evenFAxis : Dart := 61

theorem evenEndUnlink : Trace.endpoint evenEnd evenEndTrace = ⟨[], 2⟩ := rfl

abbrev evenA : Diagram := evenStart
abbrev evenF : Diagram := evenEnd

def evenPartnerPlanarCode : List (List ℕ) :=
  [[9, 13, 10, 12], [11, 22, 12, 23], [19, 9, 20, 8], [27, 15, 0, 14], [15, 7, 16, 6], [7, 19, 8, 18], [21, 25, 22, 24], [30, 18, 31, 17], [23, 10, 24, 11], [13, 27, 14, 26], [1, 4, 2, 5], [25, 21, 26, 20], [3, 28, 4, 29], [16, 30, 17, 29], [31, 2, 28, 3], [5, 0, 6, 1]]

def evenPartnerRaw : Diagram :=
  ⟨[some [9, 36, 33, 6], some [35, 26, 3, 32], some [21, 0, 47, 22], some [37, 16, 61, 38], some [13, 20, 52, 62], some [17, 8, 11, 29], some [45, 44, 5, 34], some [53, 23, 56, 54], some [7, 2, 27, 4], some [1, 12, 15, 46], some [63, 50, 57, 60], some [25, 24, 39, 10], some [59, 58, 41, 55], some [18, 28, 31, 51], some [30, 42, 49, 48], some [43, 14, 19, 40]], 0⟩

theorem evenPartnerPlanarCodeChecked : Diagram.ofPD evenPartnerPlanarCode = evenPartnerRaw := by decide +kernel

def evenPartnerRawRelabel : Move :=
  .relabel [(0, 24), (1, 25), (2, 26), (3, 27), (4, 32), (5, 33), (6, 34), (7, 35), (8, 4), (9, 5), (10, 6), (11, 7), (16, 44), (17, 45), (18, 46), (19, 47), (20, 8), (21, 9), (22, 10), (23, 11), (24, 20), (25, 21), (26, 22), (27, 23), (28, 12), (29, 13), (30, 14), (31, 15), (32, 36), (33, 37), (34, 38), (35, 39), (40, 0), (41, 1), (42, 2), (43, 3), (56, 16), (57, 17), (58, 18), (59, 19), (64, 40), (65, 41), (66, 42), (67, 43), (68, 28), (69, 29), (70, 30), (71, 31), (72, 56), (73, 57), (74, 58), (75, 59), (76, 52), (77, 53), (78, 54), (79, 55), (80, 48), (81, 49), (82, 50), (83, 51)]

theorem evenPartnerRawChecked :
    CertifiedMoves evenPartner [(evenPartnerRawRelabel, evenPartnerRaw)] := by decide +kernel

def evenPartnerRawAxis : Dart := 49

theorem evenPartnerRawAnchorChecked :
    Trace.anchor evenPartner evenPartnerAxis [(evenPartnerRawRelabel, evenPartnerRaw)] = some evenPartnerRawAxis := by decide +kernel

def evenReferencePlanarCode : List (List ℕ) :=
  [[20, 31, 21, 28], [3, 29, 4, 28], [30, 19, 31, 20], [29, 5, 30, 4], [21, 19, 22, 18], [17, 23, 18, 22], [23, 2, 24, 3], [5, 24, 6, 25], [25, 6, 26, 7], [7, 26, 8, 27], [27, 8, 0, 9], [9, 16, 10, 17], [15, 10, 16, 11], [11, 14, 12, 15], [1, 13, 2, 12], [13, 1, 14, 0]]

def evenReferenceRaw : Diagram :=
  ⟨[some [11, 10, 16, 7], some [27, 12, 15, 3], some [14, 17, 1, 0], some [5, 28, 8, 6], some [2, 9, 23, 22], some [47, 24, 19, 18], some [21, 58, 29, 4], some [13, 26, 33, 32], some [31, 30, 37, 36], some [35, 34, 41, 40], some [39, 38, 63, 44], some [43, 50, 49, 20], some [55, 46, 45, 52], some [51, 62, 59, 48], some [61, 60, 25, 54], some [57, 56, 53, 42]], 0⟩

theorem evenReferencePlanarCodeChecked : Diagram.ofPD evenReferencePlanarCode = evenReferenceRaw := by decide +kernel

def evenReferenceRawRelabel : Move :=
  .relabel []

theorem evenReferenceRawChecked :
    CertifiedMoves evenReference [(evenReferenceRawRelabel, evenReferenceRaw)] := by decide +kernel

def evenReferenceRawAxis : Dart := 7

theorem evenReferenceRawAnchorChecked :
    Trace.anchor evenReference evenReferenceAxis [(evenReferenceRawRelabel, evenReferenceRaw)] = some evenReferenceRawAxis := by decide +kernel

def evenBPlanarCode : List (List ℕ) :=
  [[30, 34, 31, 33], [32, 17, 33, 18], [18, 31, 19, 32], [12, 30, 13, 29], [35, 29, 36, 28], [27, 9, 28, 8], [7, 27, 8, 26], [37, 23, 38, 22], [21, 37, 22, 36], [20, 14, 21, 13], [16, 20, 17, 19], [15, 10, 16, 11], [9, 14, 10, 15], [11, 34, 12, 35], [23, 7, 24, 6], [5, 38, 6, 39], [39, 4, 40, 5], [2, 26, 3, 25], [3, 40, 0, 41], [24, 2, 25, 1], [41, 0, 4, 1]]

def evenBRaw : Diagram :=
  ⟨[some [13, 53, 9, 6], some [11, 42, 3, 8], some [7, 2, 43, 4], some [54, 0, 39, 17], some [55, 15, 35, 22], some [25, 48, 19, 26], some [57, 20, 23, 69], some [33, 56, 61, 34], some [38, 28, 31, 18], some [41, 49, 32, 14], some [46, 36, 5, 10], some [51, 50, 40, 52], some [21, 37, 45, 44], some [47, 1, 12, 16], some [29, 24, 76, 62], some [67, 30, 59, 64], some [63, 82, 73, 60], some [77, 27, 72, 78], some [70, 66, 81, 80], some [58, 68, 71, 83], some [75, 74, 65, 79]], 0⟩

theorem evenBPlanarCodeChecked : Diagram.ofPD evenBPlanarCode = evenBRaw := by decide +kernel

def evenBRawRelabel : Move :=
  .relabel []

theorem evenBRawChecked :
    CertifiedMoves evenB [(evenBRawRelabel, evenBRaw)] := by decide +kernel

def evenBRawAxis : Dart := 81

theorem evenBRawAnchorChecked :
    Trace.anchor evenB evenBAxis [(evenBRawRelabel, evenBRaw)] = some evenBRawAxis := by decide +kernel

def evenCPlanarCode : List (List ℕ) :=
  [[9, 13, 10, 12], [11, 30, 12, 31], [31, 10, 32, 11], [25, 9, 26, 8], [7, 25, 8, 24], [37, 21, 38, 20], [19, 37, 20, 36], [35, 27, 36, 26], [29, 35, 30, 34], [16, 34, 17, 33], [32, 18, 33, 17], [28, 15, 29, 16], [14, 27, 15, 28], [18, 13, 19, 14], [21, 7, 22, 6], [5, 38, 6, 39], [39, 4, 40, 5], [2, 24, 3, 23], [3, 40, 0, 41], [22, 2, 23, 1], [41, 0, 4, 1]]

def evenCRaw : Diagram :=
  ⟨[some [13, 53, 9, 6], some [11, 34, 3, 8], some [7, 2, 40, 4], some [17, 0, 31, 18], some [57, 12, 15, 69], some [25, 56, 61, 26], some [54, 20, 23, 30], some [33, 49, 27, 14], some [46, 28, 5, 37], some [47, 35, 43, 42], some [10, 52, 39, 38], some [51, 50, 32, 36], some [55, 29, 45, 44], some [41, 1, 24, 48], some [21, 16, 76, 62], some [67, 22, 59, 64], some [63, 82, 73, 60], some [77, 19, 72, 78], some [70, 66, 81, 80], some [58, 68, 71, 83], some [75, 74, 65, 79]], 0⟩

theorem evenCPlanarCodeChecked : Diagram.ofPD evenCPlanarCode = evenCRaw := by decide +kernel

def evenCRawRelabel : Move :=
  .relabel []

theorem evenCRawChecked :
    CertifiedMoves evenC [(evenCRawRelabel, evenCRaw)] := by decide +kernel

def evenCRawAxis : Dart := 81

theorem evenCRawAnchorChecked :
    Trace.anchor evenC evenCAxis [(evenCRawRelabel, evenCRaw)] = some evenCRawAxis := by decide +kernel

def evenDPlanarCode : List (List ℕ) :=
  [[9, 13, 10, 12], [11, 30, 12, 31], [31, 10, 32, 11], [25, 9, 26, 8], [7, 25, 8, 24], [37, 21, 38, 20], [19, 37, 20, 36], [35, 27, 36, 26], [34, 29, 35, 30], [16, 34, 17, 33], [32, 18, 33, 17], [28, 15, 29, 16], [14, 27, 15, 28], [18, 13, 19, 14], [21, 7, 22, 6], [5, 38, 6, 39], [39, 4, 40, 5], [2, 24, 3, 23], [3, 40, 0, 41], [22, 2, 23, 1], [41, 0, 4, 1]]

def evenDRaw : Diagram :=
  ⟨[some [13, 53, 9, 6], some [11, 35, 3, 8], some [7, 2, 40, 4], some [17, 0, 31, 18], some [57, 12, 15, 69], some [25, 56, 61, 26], some [54, 20, 23, 30], some [34, 49, 27, 14], some [37, 46, 28, 5], some [47, 32, 43, 42], some [10, 52, 39, 38], some [51, 50, 33, 36], some [55, 29, 45, 44], some [41, 1, 24, 48], some [21, 16, 76, 62], some [67, 22, 59, 64], some [63, 82, 73, 60], some [77, 19, 72, 78], some [70, 66, 81, 80], some [58, 68, 71, 83], some [75, 74, 65, 79]], 0⟩

theorem evenDPlanarCodeChecked : Diagram.ofPD evenDPlanarCode = evenDRaw := by decide +kernel

def evenDRawRelabel : Move :=
  .relabel []

theorem evenDRawChecked :
    CertifiedMoves evenD [(evenDRawRelabel, evenDRaw)] := by decide +kernel

def evenDRawAxis : Dart := 81

theorem evenDRawAnchorChecked :
    Trace.anchor evenD evenDAxis [(evenDRawRelabel, evenDRaw)] = some evenDRawAxis := by decide +kernel

def evenEPlanarCode : List (List ℕ) :=
  [[9, 21, 10, 20], [23, 9, 24, 8], [7, 23, 8, 22], [21, 7, 22, 6], [5, 10, 6, 11], [19, 4, 20, 5], [15, 28, 16, 29], [27, 12, 28, 13], [13, 26, 14, 27], [25, 14, 26, 15], [11, 24, 12, 25], [3, 16, 4, 17], [29, 3, 30, 2], [1, 31, 2, 30], [18, 34, 19, 33], [31, 32, 0, 33], [34, 18, 35, 17], [35, 0, 32, 1]]

def evenERaw : Diagram :=
  ⟨[some [5, 12, 17, 22], some [9, 0, 41, 10], some [13, 4, 7, 14], some [1, 8, 11, 18], some [23, 2, 15, 40], some [58, 46, 3, 16], some [39, 30, 45, 48], some [35, 42, 25, 32], some [31, 38, 37, 28], some [43, 34, 33, 24], some [19, 6, 29, 36], some [49, 26, 21, 67], some [27, 44, 55, 54], some [71, 60, 51, 50], some [65, 64, 20, 63], some [53, 70, 69, 59], some [57, 56, 68, 47], some [66, 62, 61, 52]], 0⟩

theorem evenEPlanarCodeChecked : Diagram.ofPD evenEPlanarCode = evenERaw := by decide +kernel

def evenERawRelabel : Move :=
  .relabel []

theorem evenERawChecked :
    CertifiedMoves evenE [(evenERawRelabel, evenERaw)] := by decide +kernel

def evenERawAxis : Dart := 61

theorem evenERawAnchorChecked :
    Trace.anchor evenE evenEAxis [(evenERawRelabel, evenERaw)] = some evenERawAxis := by decide +kernel

end Trefoil.Section2DiagramData
