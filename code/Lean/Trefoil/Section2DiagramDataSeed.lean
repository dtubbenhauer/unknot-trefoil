import Trefoil.Section2DiagramDataOdd

/-! Seed endpoint and exterior-source diagram certificates. -/

namespace Trefoil.Section2DiagramData

open Section2DiagramMoves

set_option maxHeartbeats 0
set_option maxRecDepth 20000

def seedB : Diagram :=
  ⟨[some [11, 4, 15, 55], some [1, 10, 9, 40], some [41, 6, 5, 0], some [37, 19, 52, 2], some [33, 20, 53, 13], some [17, 24, 27, 50], some [21, 68, 59, 22], some [63, 32, 35, 58], some [29, 16, 36, 30], some [34, 12, 43, 51], some [7, 8, 44, 38], some [42, 54, 49, 48], some [47, 46, 23, 39], some [14, 18, 45, 3], some [73, 60, 31, 26], some [57, 66, 65, 28], some [69, 62, 61, 72], some [25, 64, 75, 74], some [67, 56, 71, 70]], 0⟩

def seedC : Diagram :=
  ⟨[some [11, 4, 15, 55], some [1, 10, 9, 32], some [42, 6, 5, 0], some [29, 16, 19, 2], some [13, 68, 59, 14], some [63, 24, 27, 58], some [21, 28, 52, 22], some [25, 12, 35, 51], some [7, 39, 44, 30], some [41, 40, 45, 33], some [37, 36, 8, 54], some [34, 38, 49, 48], some [47, 46, 53, 31], some [26, 50, 43, 3], some [73, 60, 23, 18], some [57, 66, 65, 20], some [69, 62, 61, 72], some [17, 64, 75, 74], some [67, 56, 71, 70]], 0⟩

def seedD : Diagram :=
  ⟨[some [11, 4, 15, 55], some [1, 10, 9, 33], some [42, 6, 5, 0], some [29, 16, 19, 2], some [13, 68, 59, 14], some [63, 24, 27, 58], some [21, 28, 52, 22], some [25, 12, 32, 51], some [30, 7, 39, 44], some [41, 40, 45, 34], some [37, 36, 8, 54], some [35, 38, 49, 48], some [47, 46, 53, 31], some [26, 50, 43, 3], some [73, 60, 23, 18], some [57, 66, 65, 20], some [69, 62, 61, 72], some [17, 64, 75, 74], some [67, 56, 71, 70]], 0⟩

def seedE : Diagram :=
  ⟨[some [5, 12, 17, 22], some [9, 0, 41, 10], some [13, 4, 7, 14], some [1, 8, 11, 18], some [23, 2, 15, 40], some [59, 46, 3, 16], some [39, 30, 45, 48], some [35, 42, 25, 32], some [31, 38, 37, 28], some [43, 34, 33, 24], some [19, 6, 29, 36], some [49, 26, 21, 60], some [27, 44, 55, 54], some [63, 56, 51, 50], some [53, 62, 61, 20], some [47, 58, 57, 52]], 0⟩

def seedReference : Diagram :=
  ⟨[some [19, 6, 5, 8], some [9, 2, 1, 20], some [3, 4, 15, 14], some [39, 16, 11, 10], some [13, 50, 21, 0], some [7, 18, 25, 24], some [23, 22, 29, 28], some [27, 26, 33, 32], some [31, 30, 55, 36], some [35, 42, 41, 12], some [47, 38, 37, 44], some [43, 54, 51, 40], some [53, 52, 17, 46], some [49, 48, 45, 34]], 0⟩

def seedStart : Diagram :=
  ⟨[some [11, 4, 15, 55], some [1, 10, 9, 40], some [41, 6, 5, 0], some [38, 19, 52, 2], some [33, 20, 53, 13], some [17, 24, 27, 50], some [21, 68, 59, 22], some [63, 32, 35, 58], some [29, 16, 37, 30], some [51, 34, 12, 43], some [7, 8, 44, 39], some [42, 54, 49, 48], some [47, 46, 23, 36], some [14, 18, 45, 3], some [73, 60, 31, 26], some [57, 66, 65, 28], some [69, 62, 61, 72], some [25, 64, 75, 74], some [67, 56, 71, 70]], 0⟩

def seedStartTrace : Trace := [
  (.arc false [36, 12, 52] [76], ⟨[some [11, 4, 19, 18], some [1, 10, 9, 40], some [41, 6, 5, 0], none, some [33, 20, 3, 2], some [17, 24, 27, 79], some [21, 68, 59, 22], some [63, 32, 35, 58], some [29, 16, 43, 30], none, some [7, 8, 44, 34], some [42, 78, 49, 48], some [47, 46, 77, 76], none, some [73, 60, 31, 26], some [57, 66, 65, 28], some [69, 62, 61, 72], some [25, 64, 75, 74], some [67, 56, 71, 70], some [51, 50, 45, 23]], 0⟩)]

theorem seedStartChecked : CertifiedMoves seedStart seedStartTrace := by decide +kernel

def seedTrefoil : Diagram :=
  ⟨[none, none, none, none, none, none, none, none, none, none, none, some [79, 78, 49, 48], some [47, 46, 77, 76], none, none, none, none, none, none, some [51, 50, 45, 44]], 0⟩

def seedTrefoilRelabel : Move :=
  .relabel [(44, 0), (45, 1), (46, 2), (47, 3), (48, 4), (49, 5), (50, 6), (51, 7), (76, 8), (77, 9), (78, 10), (79, 11)]

theorem seedTrefoilChecked :
    CertifiedMoves seedTrefoil [(seedTrefoilRelabel, trefoilModel)] := by decide +kernel

def seedPartner : Diagram :=
  ⟨[some [11, 4, 19, 18], some [1, 10, 9, 40], some [41, 6, 5, 0], none, some [33, 20, 3, 2], some [17, 24, 27, 42], some [21, 68, 59, 22], some [63, 32, 35, 58], some [29, 16, 43, 30], none, some [7, 8, 23, 34], none, none, none, some [73, 60, 31, 26], some [57, 66, 65, 28], some [69, 62, 61, 72], some [25, 64, 75, 74], some [67, 56, 71, 70]], 0⟩

def seedCutA : Dart := 42
def seedCutB : Dart := 79

theorem seedSplitChecked :
    (Trace.endpoint seedStart seedStartTrace).checkSplit seedCutA seedCutB none
      seedTrefoil seedPartner = true := by decide +kernel

def seedEnd : Diagram :=
  ⟨[some [5, 12, 16, 22], some [9, 0, 41, 10], some [13, 4, 7, 14], some [1, 8, 11, 17], some [2, 15, 40, 23], some [59, 46, 3, 19], some [39, 30, 45, 48], some [35, 42, 25, 32], some [31, 38, 37, 28], some [43, 34, 33, 24], some [18, 6, 29, 36], some [49, 26, 21, 60], some [27, 44, 55, 54], some [63, 56, 51, 50], some [53, 62, 61, 20], some [47, 58, 57, 52]], 0⟩

def seedEndTrace : Trace := [
  (.riii 1 16 15, ⟨[some [18, 11, 40, 14], some [9, 16, 41, 10], some [17, 4, 7, 1], some [22, 19, 3, 23], some [5, 8, 0, 13], some [59, 46, 12, 15], some [39, 30, 45, 48], some [35, 42, 25, 32], some [31, 38, 37, 28], some [43, 34, 33, 24], some [2, 6, 29, 36], some [49, 26, 21, 60], some [27, 44, 55, 54], some [63, 56, 51, 50], some [53, 62, 61, 20], some [47, 58, 57, 52]], 0⟩),
  (.rii 15 23, ⟨[some [18, 11, 40, 59], some [9, 16, 41, 10], some [17, 4, 7, 1], none, some [5, 8, 0, 46], none, some [39, 30, 45, 48], some [35, 42, 25, 32], some [31, 38, 37, 28], some [43, 34, 33, 24], some [2, 6, 29, 36], some [49, 26, 19, 60], some [27, 44, 55, 54], some [63, 56, 51, 50], some [53, 62, 61, 3], some [47, 58, 57, 52]], 0⟩),
  (.riii 17 0 11, ⟨[some [5, 4, 16, 9], some [1, 0, 41, 17], some [46, 3, 19, 59], none, some [2, 7, 40, 10], none, some [39, 30, 45, 48], some [35, 42, 25, 32], some [31, 38, 37, 28], some [43, 34, 33, 24], some [18, 6, 29, 36], some [49, 26, 8, 60], some [27, 44, 55, 54], some [63, 56, 51, 50], some [53, 62, 61, 11], some [47, 58, 57, 52]], 0⟩),
  (.riii 40 6 17, ⟨[some [17, 41, 40, 9], some [43, 19, 36, 10], some [46, 3, 7, 59], none, some [42, 0, 29, 5], none, some [39, 30, 45, 48], some [35, 18, 25, 32], some [31, 38, 37, 28], some [6, 34, 33, 24], some [2, 1, 16, 4], some [49, 26, 8, 60], some [27, 44, 55, 54], some [63, 56, 51, 50], some [53, 62, 61, 11], some [47, 58, 57, 52]], 0⟩),
  (.rii 1 41, ⟨[none, some [9, 19, 36, 10], some [46, 4, 7, 59], none, some [17, 16, 29, 5], none, some [39, 30, 45, 48], some [35, 18, 25, 32], some [31, 38, 37, 28], some [6, 34, 33, 24], none, some [49, 26, 8, 60], some [27, 44, 55, 54], some [63, 56, 51, 50], some [53, 62, 61, 11], some [47, 58, 57, 52]], 0⟩),
  (.ri 16, ⟨[none, some [9, 29, 36, 10], some [46, 4, 7, 59], none, none, none, some [39, 30, 45, 48], some [35, 5, 25, 32], some [31, 38, 37, 28], some [6, 34, 33, 24], none, some [49, 26, 8, 60], some [27, 44, 55, 54], some [63, 56, 51, 50], some [53, 62, 61, 11], some [47, 58, 57, 52]], 0⟩),
  (.relabel [(4, 6), (5, 7), (6, 4), (7, 5), (8, 10), (9, 11), (10, 8), (11, 9), (24, 26), (25, 27), (26, 24), (27, 25), (28, 30), (29, 31), (30, 28), (31, 29), (32, 34), (33, 35), (34, 32), (35, 33), (36, 38), (37, 39), (38, 36), (39, 37), (44, 46), (45, 47), (46, 44), (47, 45), (48, 50), (49, 51), (50, 48), (51, 49), (52, 54), (53, 55), (54, 52), (55, 53), (56, 58), (57, 59), (58, 56), (59, 57), (60, 62), (61, 63), (62, 60), (63, 61)], ⟨[none, some [38, 8, 11, 31], some [5, 57, 44, 6], none, none, none, some [47, 50, 37, 28], some [27, 34, 33, 7], some [39, 30, 29, 36], some [35, 26, 4, 32], none, some [10, 62, 51, 24], some [53, 52, 25, 46], some [49, 48, 61, 58], some [63, 9, 55, 60], some [59, 54, 45, 56]], 0⟩),
  (.arc true [29, 7] [67], ⟨[none, none, some [65, 57, 44, 38], none, none, none, some [47, 50, 64, 33], none, some [39, 27, 67, 36], some [35, 66, 11, 32], none, some [10, 62, 51, 24], some [53, 52, 25, 46], some [49, 48, 61, 58], some [63, 9, 55, 60], some [59, 54, 45, 56], some [26, 8, 37, 34]], 0⟩),
  (.riii 67 26 33, ⟨[none, none, some [34, 57, 44, 38], none, none, none, some [66, 35, 37, 36], none, some [65, 50, 8, 25], some [27, 26, 11, 67], none, some [10, 62, 51, 64], some [53, 52, 33, 46], some [49, 48, 61, 58], some [63, 9, 55, 60], some [59, 54, 45, 56], some [47, 32, 24, 39]], 0⟩),
  (.riii 27 66 39, ⟨[none, none, some [34, 57, 44, 27], none, none, none, some [47, 38, 64, 11], none, some [39, 50, 8, 36], some [35, 65, 25, 32], none, some [10, 62, 51, 24], some [53, 52, 33, 46], some [49, 48, 61, 58], some [63, 9, 55, 60], some [59, 54, 45, 56], some [26, 37, 67, 66]], 0⟩),
  (.ri 66, ⟨[none, none, some [34, 57, 44, 27], none, none, none, some [47, 38, 37, 11], none, some [39, 50, 8, 36], some [35, 26, 25, 32], none, some [10, 62, 51, 24], some [53, 52, 33, 46], some [49, 48, 61, 58], some [63, 9, 55, 60], some [59, 54, 45, 56]], 0⟩),
  (.riii 47 10 27, ⟨[none, none, some [46, 25, 51, 38], none, none, none, some [62, 9, 45, 57], none, some [39, 50, 44, 36], some [35, 47, 11, 32], none, some [34, 26, 8, 37], some [53, 52, 33, 10], some [49, 48, 61, 58], some [63, 27, 55, 60], some [59, 54, 24, 56]], 0⟩),
  (.riii 34 36 47, ⟨[none, none, some [34, 25, 51, 35], none, none, none, some [62, 9, 37, 57], none, some [46, 38, 8, 11], some [50, 26, 33, 45], none, some [47, 39, 32, 44], some [53, 52, 36, 10], some [49, 48, 61, 58], some [63, 27, 55, 60], some [59, 54, 24, 56]], 0⟩),
  (.ri 47, ⟨[none, none, some [34, 25, 51, 35], none, none, none, some [62, 9, 37, 57], none, some [39, 38, 8, 11], some [50, 26, 33, 32], none, none, some [53, 52, 36, 10], some [49, 48, 61, 58], some [63, 27, 55, 60], some [59, 54, 24, 56]], 0⟩),
  (.rii 34 8, ⟨[none, none, none, none, none, none, some [62, 38, 37, 57], none, none, some [50, 26, 25, 51], none, none, some [53, 52, 36, 39], some [49, 48, 61, 58], some [63, 27, 55, 60], some [59, 54, 24, 56]], 0⟩),
  (.rii 50 36, ⟨[none, none, none, none, none, none, some [62, 53, 52, 57], none, none, none, none, none, none, some [26, 25, 61, 58], some [63, 27, 55, 60], some [59, 54, 24, 56]], 0⟩),
  (.rii 25 53, ⟨[none, none, none, none, none, none, none, none, none, none, none, none, none, none, some [63, 58, 57, 60], some [59, 62, 61, 56]], 0⟩),
  (.ri 61, ⟨[none, none, none, none, none, none, none, none, none, none, none, none, none, none, some [59, 58, 57, 56]], 0⟩),
  (.ri 57, ⟨[], 1⟩)]

theorem seedEndChecked : CertifiedMoves seedEnd seedEndTrace := by decide +kernel

theorem seedEndUnlink : Trace.endpoint seedEnd seedEndTrace = ⟨[], 1⟩ := rfl

abbrev seedA : Diagram := seedStart
abbrev seedF : Diagram := seedEnd

/-- The diagram returned by the pinned table entry K14a7385. -/
def seedTable : Diagram := ⟨[some [11, 4, 13, 42], some [1, 10, 9, 36], some [37, 6, 5, 0], some [43, 2, 17, 16], some [15, 14, 21, 20], some [19, 18, 45, 24], some [23, 52, 31, 30], some [55, 32, 27, 26], some [29, 46, 39, 40], some [7, 8, 41, 34], some [35, 38, 3, 12], some [51, 22, 33, 48], some [47, 54, 53, 44], some [25, 50, 49, 28]], 0⟩

def seedPartnerPlanarCode : List (List ℕ) :=
  [[19, 9, 20, 8], [21, 26, 22, 27], [27, 13, 0, 12], [15, 4, 16, 5], [1, 7, 2, 6], [7, 19, 8, 18], [11, 21, 12, 20], [17, 15, 18, 14], [25, 22, 26, 23], [5, 3, 6, 2], [3, 16, 4, 17], [23, 11, 24, 10], [9, 25, 10, 24], [13, 1, 14, 0]]

def seedPartnerRaw : Diagram :=
  ⟨[some [21, 48, 27, 22], some [25, 34, 33, 8], some [7, 52, 55, 26], some [29, 42, 41, 36], some [53, 20, 39, 38], some [17, 0, 3, 30], some [45, 4, 11, 2], some [43, 12, 23, 54], some [49, 6, 5, 44], some [15, 40, 19, 18], some [37, 14, 13, 28], some [35, 24, 51, 50], some [1, 32, 47, 46], some [9, 16, 31, 10]], 0⟩

theorem seedPartnerPlanarCodeChecked : Diagram.ofPD seedPartnerPlanarCode = seedPartnerRaw := by decide +kernel

def seedPartnerRawRelabel : Move :=
  .relabel [(0, 36), (1, 37), (2, 38), (3, 39), (4, 40), (5, 41), (6, 42), (7, 43), (8, 12), (9, 13), (10, 14), (11, 15), (24, 0), (25, 1), (26, 2), (27, 3), (28, 8), (29, 9), (30, 10), (31, 11), (32, 52), (33, 53), (34, 54), (35, 55), (40, 28), (41, 29), (42, 30), (43, 31), (56, 24), (57, 25), (58, 26), (59, 27), (60, 4), (61, 5), (62, 6), (63, 7), (64, 32), (65, 33), (66, 34), (67, 35), (68, 48), (69, 49), (70, 50), (71, 51), (72, 44), (73, 45), (74, 46), (75, 47)]

theorem seedPartnerRawChecked :
    CertifiedMoves seedPartner [(seedPartnerRawRelabel, seedPartnerRaw)] := by decide +kernel

def seedReferencePlanarCode : List (List ℕ) :=
  [[3, 20, 4, 21], [19, 4, 20, 5], [21, 19, 22, 18], [17, 23, 18, 22], [23, 2, 24, 3], [5, 24, 6, 25], [25, 6, 26, 7], [7, 26, 8, 27], [27, 8, 0, 9], [9, 16, 10, 17], [15, 10, 16, 11], [11, 14, 12, 15], [1, 13, 2, 12], [13, 1, 14, 0]]

def seedReferenceRaw : Diagram :=
  ⟨[some [19, 6, 5, 8], some [9, 2, 1, 20], some [3, 4, 15, 14], some [39, 16, 11, 10], some [13, 50, 21, 0], some [7, 18, 25, 24], some [23, 22, 29, 28], some [27, 26, 33, 32], some [31, 30, 55, 36], some [35, 42, 41, 12], some [47, 38, 37, 44], some [43, 54, 51, 40], some [53, 52, 17, 46], some [49, 48, 45, 34]], 0⟩

theorem seedReferencePlanarCodeChecked : Diagram.ofPD seedReferencePlanarCode = seedReferenceRaw := by decide +kernel

def seedReferenceRawRelabel : Move :=
  .relabel []

theorem seedReferenceRawChecked :
    CertifiedMoves seedReference [(seedReferenceRawRelabel, seedReferenceRaw)] := by decide +kernel

def seedTablePlanarCode : List (List ℕ) :=
  [[2, 0, 3, 27], [0, 11, 1, 12], [10, 1, 11, 2], [14, 3, 15, 4], [4, 15, 5, 16], [16, 5, 17, 6], [6, 22, 7, 21], [20, 8, 21, 7], [8, 25, 9, 26], [12, 10, 13, 9], [26, 13, 27, 14], [24, 17, 25, 18], [18, 23, 19, 24], [22, 19, 23, 20]]

def seedTableRaw : Diagram :=
  ⟨[some [11, 4, 13, 42], some [1, 10, 9, 36], some [37, 6, 5, 0], some [43, 2, 17, 16], some [15, 14, 21, 20], some [19, 18, 45, 24], some [23, 52, 31, 30], some [55, 32, 27, 26], some [29, 46, 39, 40], some [7, 8, 41, 34], some [35, 38, 3, 12], some [51, 22, 33, 48], some [47, 54, 53, 44], some [25, 50, 49, 28]], 0⟩

theorem seedTablePlanarCodeChecked : Diagram.ofPD seedTablePlanarCode = seedTableRaw := by decide +kernel

def seedTableRawRelabel : Move :=
  .relabel []

theorem seedTableRawChecked :
    CertifiedMoves seedTable [(seedTableRawRelabel, seedTableRaw)] := by decide +kernel

def seedBPlanarCode : List (List ℕ) :=
  [[32, 30, 33, 29], [30, 7, 31, 8], [6, 31, 7, 32], [12, 34, 13, 33], [27, 35, 28, 34], [35, 17, 36, 16], [17, 37, 18, 36], [25, 3, 26, 2], [3, 27, 4, 26], [4, 12, 5, 11], [8, 6, 9, 5], [9, 14, 10, 15], [15, 10, 16, 11], [13, 28, 14, 29], [1, 19, 2, 18], [19, 24, 20, 25], [23, 20, 24, 21], [37, 23, 0, 22], [21, 1, 22, 0]]

def seedBRaw : Diagram :=
  ⟨[some [11, 4, 15, 55], some [1, 10, 9, 40], some [41, 6, 5, 0], some [37, 19, 52, 2], some [33, 20, 53, 13], some [17, 24, 27, 50], some [21, 68, 59, 22], some [63, 32, 35, 58], some [29, 16, 36, 30], some [34, 12, 43, 51], some [7, 8, 44, 38], some [42, 54, 49, 48], some [47, 46, 23, 39], some [14, 18, 45, 3], some [73, 60, 31, 26], some [57, 66, 65, 28], some [69, 62, 61, 72], some [25, 64, 75, 74], some [67, 56, 71, 70]], 0⟩

theorem seedBPlanarCodeChecked : Diagram.ofPD seedBPlanarCode = seedBRaw := by decide +kernel

def seedBRawRelabel : Move :=
  .relabel []

theorem seedBRawChecked :
    CertifiedMoves seedB [(seedBRawRelabel, seedBRaw)] := by decide +kernel

def seedCPlanarCode : List (List ℕ) :=
  [[13, 11, 14, 10], [11, 30, 12, 31], [29, 12, 30, 13], [35, 15, 36, 14], [15, 37, 16, 36], [23, 3, 24, 2], [3, 25, 4, 24], [25, 35, 26, 34], [31, 27, 32, 26], [6, 28, 7, 27], [28, 6, 29, 5], [32, 7, 33, 8], [8, 33, 9, 34], [4, 9, 5, 10], [1, 17, 2, 16], [17, 22, 18, 23], [21, 18, 22, 19], [37, 21, 0, 20], [19, 1, 20, 0]]

def seedCRaw : Diagram :=
  ⟨[some [11, 4, 15, 55], some [1, 10, 9, 32], some [42, 6, 5, 0], some [29, 16, 19, 2], some [13, 68, 59, 14], some [63, 24, 27, 58], some [21, 28, 52, 22], some [25, 12, 35, 51], some [7, 39, 44, 30], some [41, 40, 45, 33], some [37, 36, 8, 54], some [34, 38, 49, 48], some [47, 46, 53, 31], some [26, 50, 43, 3], some [73, 60, 23, 18], some [57, 66, 65, 20], some [69, 62, 61, 72], some [17, 64, 75, 74], some [67, 56, 71, 70]], 0⟩

theorem seedCPlanarCodeChecked : Diagram.ofPD seedCPlanarCode = seedCRaw := by decide +kernel

def seedCRawRelabel : Move :=
  .relabel []

theorem seedCRawChecked :
    CertifiedMoves seedC [(seedCRawRelabel, seedCRaw)] := by decide +kernel

def seedDPlanarCode : List (List ℕ) :=
  [[13, 11, 14, 10], [11, 30, 12, 31], [29, 12, 30, 13], [35, 15, 36, 14], [15, 37, 16, 36], [23, 3, 24, 2], [3, 25, 4, 24], [25, 35, 26, 34], [26, 31, 27, 32], [6, 28, 7, 27], [28, 6, 29, 5], [32, 7, 33, 8], [8, 33, 9, 34], [4, 9, 5, 10], [1, 17, 2, 16], [17, 22, 18, 23], [21, 18, 22, 19], [37, 21, 0, 20], [19, 1, 20, 0]]

def seedDRaw : Diagram :=
  ⟨[some [11, 4, 15, 55], some [1, 10, 9, 33], some [42, 6, 5, 0], some [29, 16, 19, 2], some [13, 68, 59, 14], some [63, 24, 27, 58], some [21, 28, 52, 22], some [25, 12, 32, 51], some [30, 7, 39, 44], some [41, 40, 45, 34], some [37, 36, 8, 54], some [35, 38, 49, 48], some [47, 46, 53, 31], some [26, 50, 43, 3], some [73, 60, 23, 18], some [57, 66, 65, 20], some [69, 62, 61, 72], some [17, 64, 75, 74], some [67, 56, 71, 70]], 0⟩

theorem seedDPlanarCodeChecked : Diagram.ofPD seedDPlanarCode = seedDRaw := by decide +kernel

def seedDRawRelabel : Move :=
  .relabel []

theorem seedDRawChecked :
    CertifiedMoves seedD [(seedDRawRelabel, seedDRaw)] := by decide +kernel

def seedEPlanarCode : List (List ℕ) :=
  [[9, 21, 10, 20], [23, 9, 24, 8], [7, 23, 8, 22], [21, 7, 22, 6], [5, 10, 6, 11], [19, 4, 20, 5], [15, 28, 16, 29], [27, 12, 28, 13], [13, 26, 14, 27], [25, 14, 26, 15], [11, 24, 12, 25], [3, 16, 4, 17], [29, 3, 30, 2], [1, 31, 2, 30], [31, 18, 0, 19], [17, 0, 18, 1]]

def seedERaw : Diagram :=
  ⟨[some [5, 12, 17, 22], some [9, 0, 41, 10], some [13, 4, 7, 14], some [1, 8, 11, 18], some [23, 2, 15, 40], some [59, 46, 3, 16], some [39, 30, 45, 48], some [35, 42, 25, 32], some [31, 38, 37, 28], some [43, 34, 33, 24], some [19, 6, 29, 36], some [49, 26, 21, 60], some [27, 44, 55, 54], some [63, 56, 51, 50], some [53, 62, 61, 20], some [47, 58, 57, 52]], 0⟩

theorem seedEPlanarCodeChecked : Diagram.ofPD seedEPlanarCode = seedERaw := by decide +kernel

def seedERawRelabel : Move :=
  .relabel []

theorem seedERawChecked :
    CertifiedMoves seedE [(seedERawRelabel, seedERaw)] := by decide +kernel

end Trefoil.Section2DiagramData
