import Trefoil.Section2DiagramDataEven

/-! Odd endpoint and exterior-source diagram certificates. -/

namespace Trefoil.Section2DiagramData

open Section2DiagramMoves

set_option maxHeartbeats 0
set_option maxRecDepth 20000

def oddB : Diagram :=
  ⟨[some [15, 55, 11, 6], some [9, 40, 3, 10], some [41, 4, 7, 2], some [37, 17, 52, 0], some [53, 13, 33, 22], some [27, 50, 19, 24], some [23, 69, 59, 20], some [35, 58, 63, 32], some [31, 18, 36, 28], some [34, 12, 43, 51], some [5, 8, 44, 38], some [42, 54, 49, 48], some [47, 46, 21, 39], some [14, 16, 45, 1], some [85, 60, 29, 26], some [57, 64, 67, 30], some [61, 84, 73, 62], some [77, 25, 72, 78], some [70, 66, 81, 80], some [86, 68, 71, 83], some [75, 74, 87, 79], some [65, 56, 76, 82]], 0⟩

def oddBAxis : Dart := 68

def oddC : Diagram :=
  ⟨[some [9, 4, 13, 55], some [1, 8, 11, 34], some [5, 0, 40, 6], some [19, 2, 31, 16], some [15, 69, 59, 12], some [27, 58, 63, 24], some [23, 30, 52, 20], some [33, 51, 25, 14], some [46, 28, 7, 39], some [43, 42, 47, 35], some [10, 54, 37, 36], some [49, 48, 32, 38], some [45, 44, 53, 29], some [26, 50, 41, 3], some [85, 60, 21, 18], some [57, 64, 67, 22], some [61, 84, 73, 62], some [77, 17, 72, 78], some [70, 66, 81, 80], some [86, 68, 71, 83], some [75, 74, 87, 79], some [65, 56, 76, 82]], 0⟩

def oddCAxis : Dart := 68

def oddD : Diagram :=
  ⟨[some [9, 4, 13, 55], some [1, 8, 11, 35], some [5, 0, 40, 6], some [19, 2, 31, 16], some [15, 69, 59, 12], some [27, 58, 63, 24], some [23, 30, 52, 20], some [34, 51, 25, 14], some [39, 46, 28, 7], some [43, 42, 47, 32], some [10, 54, 37, 36], some [49, 48, 33, 38], some [45, 44, 53, 29], some [26, 50, 41, 3], some [85, 60, 21, 18], some [57, 64, 67, 22], some [61, 84, 73, 62], some [77, 17, 72, 78], some [70, 66, 81, 80], some [86, 68, 71, 83], some [75, 74, 87, 79], some [65, 56, 76, 82]], 0⟩

def oddDAxis : Dart := 68

def oddE : Diagram :=
  ⟨[some [7, 14, 17, 20], some [41, 10, 9, 0], some [15, 6, 5, 12], some [11, 18, 1, 8], some [21, 2, 13, 40], some [3, 16, 56, 46], some [37, 28, 45, 50], some [25, 32, 35, 42], some [29, 36, 39, 30], some [33, 24, 43, 34], some [19, 4, 31, 38], some [51, 26, 23, 72], some [55, 54, 27, 44], some [75, 62, 49, 48], some [22, 61, 65, 64], some [69, 57, 53, 70], some [59, 58, 68, 73], some [66, 60, 63, 74], some [47, 67, 71, 52]], 0⟩

def oddEAxis : Dart := 63

def oddReference : Diagram :=
  ⟨[some [11, 10, 20, 7], some [31, 12, 15, 3], some [14, 19, 1, 0], some [5, 16, 8, 6], some [13, 34, 21, 9], some [2, 18, 25, 24], some [23, 22, 49, 28], some [27, 62, 35, 4], some [37, 36, 17, 30], some [33, 32, 43, 42], some [45, 44, 39, 38], some [41, 40, 65, 50], some [55, 26, 47, 52], some [51, 58, 57, 48], some [63, 54, 53, 64], some [67, 66, 29, 56], some [59, 46, 61, 60]], 0⟩

def oddReferenceAxis : Dart := 7

def oddStart : Diagram :=
  ⟨[some [15, 55, 11, 6], some [9, 40, 3, 10], some [41, 4, 7, 2], some [38, 17, 52, 0], some [53, 13, 33, 22], some [27, 50, 19, 24], some [23, 69, 59, 20], some [35, 58, 63, 32], some [31, 18, 37, 28], some [51, 34, 12, 43], some [5, 8, 44, 39], some [42, 54, 49, 48], some [47, 46, 21, 36], some [14, 16, 45, 1], some [85, 60, 29, 26], some [57, 64, 67, 30], some [61, 84, 73, 62], some [77, 25, 72, 78], some [70, 66, 81, 80], some [86, 68, 71, 83], some [75, 74, 87, 79], some [65, 56, 76, 82]], 0⟩

def oddStartTrace : Trace := [
  (.riii 52 16 13, ⟨[some [17, 16, 11, 6], some [9, 40, 3, 10], some [41, 4, 7, 2], some [54, 22, 45, 19], some [1, 0, 55, 15], some [27, 50, 13, 24], some [23, 69, 59, 20], some [35, 58, 63, 32], some [31, 53, 37, 28], some [51, 34, 52, 43], some [5, 8, 44, 39], some [42, 14, 49, 48], some [47, 46, 21, 36], some [38, 33, 12, 18], some [85, 60, 29, 26], some [57, 64, 67, 30], some [61, 84, 73, 62], some [77, 25, 72, 78], some [70, 66, 81, 80], some [86, 68, 71, 83], some [75, 74, 87, 79], some [65, 56, 76, 82]], 0⟩),
  (.riii 37 52 33, ⟨[some [17, 16, 11, 6], some [9, 40, 3, 10], some [41, 4, 7, 2], some [38, 22, 45, 19], some [1, 0, 33, 15], some [27, 50, 13, 24], some [23, 69, 59, 20], some [53, 58, 63, 37], some [39, 18, 43, 55], some [54, 31, 12, 32], some [5, 8, 44, 34], some [42, 14, 49, 48], some [47, 46, 21, 52], some [51, 28, 36, 35], some [85, 60, 29, 26], some [57, 64, 67, 30], some [61, 84, 73, 62], some [77, 25, 72, 78], some [70, 66, 81, 80], some [86, 68, 71, 83], some [75, 74, 87, 79], some [65, 56, 76, 82]], 0⟩),
  (.riii 53 36 31, ⟨[some [17, 16, 11, 6], some [9, 40, 3, 10], some [41, 4, 7, 2], some [54, 22, 45, 19], some [1, 0, 33, 15], some [27, 50, 13, 24], some [23, 69, 59, 20], some [35, 39, 55, 32], some [31, 18, 43, 28], some [51, 58, 52, 29], some [5, 8, 44, 34], some [42, 14, 49, 48], some [47, 46, 21, 36], some [38, 63, 12, 30], some [85, 60, 37, 26], some [57, 64, 67, 53], some [61, 84, 73, 62], some [77, 25, 72, 78], some [70, 66, 81, 80], some [86, 68, 71, 83], some [75, 74, 87, 79], some [65, 56, 76, 82]], 0⟩),
  (.riii 86 82 79, ⟨[some [17, 16, 11, 6], some [9, 40, 3, 10], some [41, 4, 7, 2], some [54, 22, 45, 19], some [1, 0, 33, 15], some [27, 50, 13, 24], some [23, 69, 59, 20], some [35, 39, 55, 32], some [31, 18, 43, 28], some [51, 58, 52, 29], some [5, 8, 44, 34], some [42, 14, 49, 48], some [47, 46, 21, 36], some [38, 63, 12, 30], some [82, 60, 37, 26], some [57, 64, 67, 53], some [61, 76, 73, 62], some [83, 25, 72, 86], some [70, 66, 79, 87], some [65, 81, 84, 74], some [85, 77, 56, 68], some [78, 80, 71, 75]], 0⟩),
  (.relabel [(0, 2), (1, 3), (2, 0), (3, 1), (4, 6), (5, 7), (6, 4), (7, 5), (8, 10), (9, 11), (10, 8), (11, 9), (12, 14), (13, 15), (14, 12), (15, 13), (16, 18), (17, 19), (18, 16), (19, 17), (20, 22), (21, 23), (22, 20), (23, 21), (24, 26), (25, 27), (26, 24), (27, 25), (28, 30), (29, 31), (30, 28), (31, 29), (32, 34), (33, 35), (34, 32), (35, 33), (36, 38), (37, 39), (38, 36), (39, 37), (40, 42), (41, 43), (42, 40), (43, 41), (44, 46), (45, 47), (46, 44), (47, 45), (48, 50), (49, 51), (50, 48), (51, 49), (52, 54), (53, 55), (54, 52), (55, 53), (56, 58), (57, 59), (58, 56), (59, 57), (60, 62), (61, 63), (62, 60), (63, 61), (64, 66), (65, 67), (66, 64), (67, 65), (68, 70), (69, 71), (70, 68), (71, 69), (72, 74), (73, 75), (74, 72), (75, 73), (76, 78), (77, 79), (78, 76), (79, 77), (80, 82), (81, 83), (82, 80), (83, 81), (84, 86), (85, 87), (86, 84), (87, 85)], ⟨[some [9, 4, 19, 18], some [1, 8, 11, 42], some [5, 0, 43, 6], some [47, 17, 52, 20], some [35, 13, 3, 2], some [15, 26, 25, 48], some [57, 22, 21, 71], some [53, 34, 33, 37], some [41, 30, 29, 16], some [54, 31, 49, 56], some [46, 32, 7, 10], some [51, 50, 40, 12], some [23, 38, 45, 44], some [14, 28, 36, 61], some [39, 24, 80, 62], some [65, 55, 59, 66], some [75, 60, 63, 78], some [74, 84, 81, 27], some [77, 85, 68, 64], some [86, 72, 67, 83], some [58, 70, 87, 79], some [69, 73, 76, 82]], 0⟩),
  (.riii 68 84 73, ⟨[some [9, 4, 19, 18], some [1, 8, 11, 42], some [5, 0, 43, 6], some [47, 17, 52, 20], some [35, 13, 3, 2], some [15, 26, 25, 48], some [57, 22, 21, 84], some [53, 34, 33, 37], some [41, 30, 29, 16], some [54, 31, 49, 56], some [46, 32, 7, 10], some [51, 50, 40, 12], some [23, 38, 45, 44], some [14, 28, 36, 61], some [39, 24, 80, 62], some [65, 55, 59, 66], some [85, 60, 63, 78], some [77, 76, 72, 86], some [70, 82, 81, 87], some [69, 68, 67, 83], some [58, 74, 73, 79], some [27, 64, 71, 75]], 0⟩),
  (.riii 53 36 31, ⟨[some [9, 4, 19, 18], some [1, 8, 11, 42], some [5, 0, 43, 6], some [47, 17, 36, 20], some [35, 13, 3, 2], some [15, 26, 25, 48], some [57, 22, 21, 84], some [61, 39, 55, 56], some [41, 53, 37, 16], some [14, 34, 52, 29], some [46, 32, 7, 10], some [51, 50, 40, 12], some [23, 54, 45, 44], some [38, 33, 49, 30], some [31, 24, 80, 62], some [65, 28, 59, 66], some [85, 60, 63, 78], some [77, 76, 72, 86], some [70, 82, 81, 87], some [69, 68, 67, 83], some [58, 74, 73, 79], some [27, 64, 71, 75]], 0⟩),
  (.riii 70 86 75, ⟨[some [9, 4, 19, 18], some [1, 8, 11, 42], some [5, 0, 43, 6], some [47, 17, 36, 20], some [35, 13, 3, 2], some [15, 26, 25, 48], some [57, 22, 21, 71], some [61, 39, 55, 56], some [41, 53, 37, 16], some [14, 34, 52, 29], some [46, 32, 7, 10], some [51, 50, 40, 12], some [23, 54, 45, 44], some [38, 33, 49, 30], some [31, 24, 80, 62], some [65, 28, 59, 66], some [75, 60, 63, 78], some [74, 84, 81, 27], some [77, 85, 68, 64], some [86, 72, 67, 83], some [58, 70, 87, 79], some [69, 73, 76, 82]], 0⟩),
  (.riii 37 52 33, ⟨[some [9, 4, 19, 18], some [1, 8, 11, 42], some [5, 0, 43, 6], some [47, 17, 52, 20], some [53, 13, 3, 2], some [15, 26, 25, 48], some [57, 22, 21, 71], some [61, 34, 33, 56], some [39, 30, 29, 55], some [54, 41, 49, 32], some [46, 37, 7, 10], some [51, 50, 40, 12], some [23, 38, 45, 44], some [14, 16, 36, 35], some [31, 24, 80, 62], some [65, 28, 59, 66], some [75, 60, 63, 78], some [74, 84, 81, 27], some [77, 85, 68, 64], some [86, 72, 67, 83], some [58, 70, 87, 79], some [69, 73, 76, 82]], 0⟩),
  (.riii 68 84 73, ⟨[some [9, 4, 19, 18], some [1, 8, 11, 42], some [5, 0, 43, 6], some [47, 17, 52, 20], some [53, 13, 3, 2], some [15, 26, 25, 48], some [57, 22, 21, 84], some [61, 34, 33, 56], some [39, 30, 29, 55], some [54, 41, 49, 32], some [46, 37, 7, 10], some [51, 50, 40, 12], some [23, 38, 45, 44], some [14, 16, 36, 35], some [31, 24, 80, 62], some [65, 28, 59, 66], some [85, 60, 63, 78], some [77, 76, 72, 86], some [70, 82, 81, 87], some [69, 68, 67, 83], some [58, 74, 73, 79], some [27, 64, 71, 75]], 0⟩),
  (.riii 52 16 13, ⟨[some [9, 4, 13, 53], some [1, 8, 11, 42], some [5, 0, 43, 6], some [54, 2, 36, 19], some [35, 20, 55, 15], some [17, 26, 25, 48], some [57, 22, 21, 84], some [61, 34, 33, 56], some [39, 30, 29, 16], some [14, 41, 49, 32], some [46, 37, 7, 10], some [51, 50, 40, 52], some [23, 38, 45, 44], some [47, 3, 12, 18], some [31, 24, 80, 62], some [65, 28, 59, 66], some [85, 60, 63, 78], some [77, 76, 72, 86], some [70, 82, 81, 87], some [69, 68, 67, 83], some [58, 74, 73, 79], some [27, 64, 71, 75]], 0⟩),
  (.riii 70 86 75, ⟨[some [9, 4, 13, 53], some [1, 8, 11, 42], some [5, 0, 43, 6], some [54, 2, 36, 19], some [35, 20, 55, 15], some [17, 26, 25, 48], some [57, 22, 21, 71], some [61, 34, 33, 56], some [39, 30, 29, 16], some [14, 41, 49, 32], some [46, 37, 7, 10], some [51, 50, 40, 52], some [23, 38, 45, 44], some [47, 3, 12, 18], some [31, 24, 80, 62], some [65, 28, 59, 66], some [75, 60, 63, 78], some [74, 84, 81, 27], some [77, 85, 68, 64], some [86, 72, 67, 83], some [58, 70, 87, 79], some [69, 73, 76, 82]], 0⟩),
  (.riii 12 2 53, ⟨[some [15, 55, 19, 18], some [53, 8, 11, 42], some [5, 13, 43, 6], some [47, 9, 52, 0], some [35, 20, 3, 2], some [17, 26, 25, 48], some [57, 22, 21, 71], some [61, 34, 33, 56], some [39, 30, 29, 16], some [54, 41, 49, 32], some [46, 37, 7, 10], some [51, 50, 40, 12], some [23, 38, 45, 44], some [14, 4, 36, 1], some [31, 24, 80, 62], some [65, 28, 59, 66], some [75, 60, 63, 78], some [74, 84, 81, 27], some [77, 85, 68, 64], some [86, 72, 67, 83], some [58, 70, 87, 79], some [69, 73, 76, 82]], 0⟩),
  (.riii 76 72 85, ⟨[some [15, 55, 19, 18], some [53, 8, 11, 42], some [5, 13, 43, 6], some [47, 9, 52, 0], some [35, 20, 3, 2], some [17, 26, 25, 48], some [57, 22, 21, 71], some [61, 34, 33, 56], some [39, 30, 29, 16], some [54, 41, 49, 32], some [46, 37, 7, 10], some [51, 50, 40, 12], some [23, 38, 45, 44], some [14, 4, 36, 1], some [31, 24, 80, 62], some [65, 28, 59, 66], some [85, 60, 63, 86], some [77, 76, 81, 27], some [83, 82, 79, 87], some [69, 68, 84, 74], some [58, 70, 73, 72], some [78, 64, 67, 75]], 0⟩),
  (.riii 14 0 55, ⟨[some [9, 4, 13, 53], some [1, 8, 11, 42], some [5, 0, 43, 6], some [54, 2, 36, 19], some [35, 20, 55, 15], some [17, 26, 25, 48], some [57, 22, 21, 71], some [61, 34, 33, 56], some [39, 30, 29, 16], some [14, 41, 49, 32], some [46, 37, 7, 10], some [51, 50, 40, 52], some [23, 38, 45, 44], some [47, 3, 12, 18], some [31, 24, 80, 62], some [65, 28, 59, 66], some [85, 60, 63, 86], some [77, 76, 81, 27], some [83, 82, 79, 87], some [69, 68, 84, 74], some [58, 70, 73, 72], some [78, 64, 67, 75]], 0⟩),
  (.relabel [(0, 2), (1, 3), (2, 0), (3, 1), (4, 6), (5, 7), (6, 4), (7, 5), (8, 10), (9, 11), (10, 8), (11, 9), (12, 14), (13, 15), (14, 12), (15, 13), (16, 18), (17, 19), (18, 16), (19, 17), (20, 22), (21, 23), (22, 20), (23, 21), (24, 26), (25, 27), (26, 24), (27, 25), (28, 30), (29, 31), (30, 28), (31, 29), (32, 34), (33, 35), (34, 32), (35, 33), (36, 38), (37, 39), (38, 36), (39, 37), (40, 42), (41, 43), (42, 40), (43, 41), (44, 46), (45, 47), (46, 44), (47, 45), (48, 50), (49, 51), (50, 48), (51, 49), (52, 54), (53, 55), (54, 52), (55, 53), (56, 58), (57, 59), (58, 56), (59, 57), (60, 62), (61, 63), (62, 60), (63, 61), (64, 66), (65, 67), (66, 64), (67, 65), (68, 70), (69, 71), (70, 68), (71, 69), (72, 74), (73, 75), (74, 72), (75, 73), (76, 78), (77, 79), (78, 76), (79, 77), (80, 82), (81, 83), (82, 80), (83, 81), (84, 86), (85, 87), (86, 84), (87, 85)], ⟨[some [15, 55, 11, 6], some [9, 40, 3, 10], some [41, 4, 7, 2], some [38, 17, 52, 0], some [53, 13, 33, 22], some [27, 50, 19, 24], some [23, 69, 59, 20], some [35, 58, 63, 32], some [31, 18, 37, 28], some [51, 34, 12, 43], some [5, 8, 44, 39], some [42, 54, 49, 48], some [47, 46, 21, 36], some [14, 16, 45, 1], some [82, 60, 29, 26], some [57, 64, 67, 30], some [61, 84, 87, 62], some [83, 25, 79, 78], some [77, 85, 81, 80], some [86, 72, 71, 70], some [75, 74, 56, 68], some [65, 73, 76, 66]], 0⟩),
  (.arc false [36, 12, 52] [88], ⟨[some [17, 16, 11, 6], some [9, 40, 3, 10], some [41, 4, 7, 2], none, some [1, 0, 33, 22], some [27, 91, 19, 24], some [23, 69, 59, 20], some [35, 58, 63, 32], some [31, 18, 43, 28], none, some [5, 8, 44, 34], some [42, 90, 49, 48], some [47, 46, 89, 88], none, some [82, 60, 29, 26], some [57, 64, 67, 30], some [61, 84, 87, 62], some [83, 25, 79, 78], some [77, 85, 81, 80], some [86, 72, 71, 70], some [75, 74, 56, 68], some [65, 73, 76, 66], some [51, 50, 45, 21]], 0⟩),
  (.riii 76 72 85, ⟨[some [17, 16, 11, 6], some [9, 40, 3, 10], some [41, 4, 7, 2], none, some [1, 0, 33, 22], some [27, 91, 19, 24], some [23, 69, 59, 20], some [35, 58, 63, 32], some [31, 18, 43, 28], none, some [5, 8, 44, 34], some [42, 90, 49, 48], some [47, 46, 89, 88], none, some [82, 60, 29, 26], some [57, 64, 67, 30], some [61, 76, 73, 62], some [83, 25, 72, 86], some [70, 66, 79, 87], some [65, 81, 84, 74], some [85, 77, 56, 68], some [78, 80, 71, 75], some [51, 50, 45, 21]], 0⟩),
  (.riii 70 86 75, ⟨[some [17, 16, 11, 6], some [9, 40, 3, 10], some [41, 4, 7, 2], none, some [1, 0, 33, 22], some [27, 91, 19, 24], some [23, 86, 59, 20], some [35, 58, 63, 32], some [31, 18, 43, 28], none, some [5, 8, 44, 34], some [42, 90, 49, 48], some [47, 46, 89, 88], none, some [82, 60, 29, 26], some [57, 64, 67, 30], some [61, 76, 87, 62], some [74, 84, 79, 78], some [83, 85, 68, 80], some [65, 81, 71, 70], some [75, 77, 56, 72], some [69, 73, 25, 66], some [51, 50, 45, 21]], 0⟩)]

theorem oddStartChecked : CertifiedMoves oddStart oddStartTrace := by decide +kernel

def oddAAxis : Dart := 68
def oddPartnerAxis : Dart := 72

theorem oddAnchorChecked :
    Trace.anchor oddStart oddAAxis oddStartTrace = some oddPartnerAxis := by decide +kernel

def oddTrefoil : Diagram :=
  ⟨[none, none, none, none, none, none, none, none, none, none, none, some [91, 90, 49, 48], some [47, 46, 89, 88], none, none, none, none, none, none, none, none, none, some [51, 50, 45, 44]], 0⟩

def oddTrefoilRelabel : Move :=
  .relabel [(44, 0), (45, 1), (46, 2), (47, 3), (48, 4), (49, 5), (50, 6), (51, 7), (88, 8), (89, 9), (90, 10), (91, 11)]

theorem oddTrefoilChecked :
    CertifiedMoves oddTrefoil [(oddTrefoilRelabel, trefoilModel)] := by decide +kernel

def oddPartner : Diagram :=
  ⟨[some [17, 16, 11, 6], some [9, 40, 3, 10], some [41, 4, 7, 2], none, some [1, 0, 33, 22], some [27, 42, 19, 24], some [23, 86, 59, 20], some [35, 58, 63, 32], some [31, 18, 43, 28], none, some [5, 8, 21, 34], none, none, none, some [82, 60, 29, 26], some [57, 64, 67, 30], some [61, 76, 87, 62], some [74, 84, 79, 78], some [83, 85, 68, 80], some [65, 81, 71, 70], some [75, 77, 56, 72], some [69, 73, 25, 66]], 0⟩

def oddCutA : Dart := 42
def oddCutB : Dart := 91

theorem oddSplitChecked :
    (Trace.endpoint oddStart oddStartTrace).checkSplit oddCutA oddCutB (some oddPartnerAxis)
      oddTrefoil oddPartner = true := by decide +kernel

def oddEnd : Diagram :=
  ⟨[some [7, 14, 16, 20], some [41, 10, 9, 0], some [15, 6, 5, 12], some [11, 17, 1, 8], some [2, 13, 40, 21], some [3, 19, 56, 46], some [37, 28, 45, 50], some [25, 32, 35, 42], some [29, 36, 39, 30], some [33, 24, 43, 34], some [18, 4, 31, 38], some [51, 26, 23, 72], some [55, 54, 27, 44], some [75, 62, 49, 48], some [22, 61, 65, 64], some [69, 57, 53, 70], some [59, 58, 68, 73], some [66, 60, 63, 74], some [47, 67, 71, 52]], 0⟩

def oddEndTrace : Trace := [
  (.riii 2 20 19, ⟨[some [18, 22, 40, 56], some [41, 10, 9, 16], some [15, 6, 5, 12], some [11, 21, 20, 8], some [7, 23, 0, 46], some [14, 13, 1, 17], some [37, 28, 45, 50], some [25, 32, 35, 42], some [29, 36, 39, 30], some [33, 24, 43, 34], some [2, 4, 31, 38], some [51, 26, 19, 72], some [55, 54, 27, 44], some [75, 62, 49, 48], some [3, 61, 65, 64], some [69, 57, 53, 70], some [59, 58, 68, 73], some [66, 60, 63, 74], some [47, 67, 71, 52]], 0⟩),
  (.rii 20 14, ⟨[some [18, 11, 40, 56], some [41, 10, 9, 16], some [17, 6, 5, 1], none, some [7, 8, 0, 46], none, some [37, 28, 45, 50], some [25, 32, 35, 42], some [29, 36, 39, 30], some [33, 24, 43, 34], some [2, 4, 31, 38], some [51, 26, 19, 72], some [55, 54, 27, 44], some [75, 62, 49, 48], some [3, 61, 65, 64], some [69, 57, 53, 70], some [59, 58, 68, 73], some [66, 60, 63, 74], some [47, 67, 71, 52]], 0⟩),
  (.riii 17 0 11, ⟨[some [7, 6, 16, 9], some [41, 17, 1, 0], some [46, 3, 19, 56], none, some [2, 5, 40, 10], none, some [37, 28, 45, 50], some [25, 32, 35, 42], some [29, 36, 39, 30], some [33, 24, 43, 34], some [18, 4, 31, 38], some [51, 26, 8, 72], some [55, 54, 27, 44], some [75, 62, 49, 48], some [11, 61, 65, 64], some [69, 57, 53, 70], some [59, 58, 68, 73], some [66, 60, 63, 74], some [47, 67, 71, 52]], 0⟩),
  (.riii 71 66 73, ⟨[some [7, 6, 16, 9], some [41, 17, 1, 0], some [46, 3, 19, 56], none, some [2, 5, 40, 10], none, some [37, 28, 45, 50], some [25, 32, 35, 42], some [29, 36, 39, 30], some [33, 24, 43, 34], some [18, 4, 31, 38], some [51, 26, 8, 71], some [55, 54, 27, 44], some [67, 62, 49, 48], some [11, 61, 73, 68], some [74, 57, 53, 66], some [70, 75, 63, 52], some [59, 72, 64, 47], some [69, 58, 60, 65]], 0⟩),
  (.riii 73 60 57, ⟨[some [7, 6, 16, 9], some [41, 17, 1, 0], some [46, 3, 19, 73], none, some [2, 5, 40, 10], none, some [37, 28, 45, 50], some [25, 32, 35, 42], some [29, 36, 39, 30], some [33, 24, 43, 34], some [18, 4, 31, 38], some [51, 26, 8, 71], some [55, 54, 27, 44], some [67, 74, 49, 48], some [75, 66, 65, 63], some [69, 68, 72, 59], some [70, 58, 57, 52], some [61, 60, 64, 47], some [62, 11, 53, 56]], 0⟩),
  (.riii 1 16 5, ⟨[some [18, 41, 40, 4], some [3, 10, 9, 19], some [46, 6, 5, 73], none, some [17, 16, 0, 7], none, some [37, 28, 45, 50], some [25, 32, 35, 42], some [29, 36, 39, 30], some [33, 24, 43, 34], some [2, 1, 31, 38], some [51, 26, 8, 71], some [55, 54, 27, 44], some [67, 74, 49, 48], some [75, 66, 65, 63], some [69, 68, 72, 59], some [70, 58, 57, 52], some [61, 60, 64, 47], some [62, 11, 53, 56]], 0⟩),
  (.ri 16, ⟨[some [7, 41, 40, 4], some [3, 10, 9, 0], some [46, 6, 5, 73], none, none, none, some [37, 28, 45, 50], some [25, 32, 35, 42], some [29, 36, 39, 30], some [33, 24, 43, 34], some [2, 1, 31, 38], some [51, 26, 8, 71], some [55, 54, 27, 44], some [67, 74, 49, 48], some [75, 66, 65, 63], some [69, 68, 72, 59], some [70, 58, 57, 52], some [61, 60, 64, 47], some [62, 11, 53, 56]], 0⟩),
  (.rii 1 41, ⟨[none, some [38, 10, 9, 31], some [46, 6, 5, 73], none, none, none, some [37, 28, 45, 50], some [25, 32, 35, 7], some [29, 36, 39, 30], some [33, 24, 4, 34], none, some [51, 26, 8, 71], some [55, 54, 27, 44], some [67, 74, 49, 48], some [75, 66, 65, 63], some [69, 68, 72, 59], some [70, 58, 57, 52], some [61, 60, 64, 47], some [62, 11, 53, 56]], 0⟩),
  (.relabel [(4, 6), (5, 7), (6, 4), (7, 5), (8, 10), (9, 11), (10, 8), (11, 9), (24, 26), (25, 27), (26, 24), (27, 25), (28, 30), (29, 31), (30, 28), (31, 29), (32, 34), (33, 35), (34, 32), (35, 33), (36, 38), (37, 39), (38, 36), (39, 37), (44, 46), (45, 47), (46, 44), (47, 45), (48, 50), (49, 51), (50, 48), (51, 49), (52, 54), (53, 55), (54, 52), (55, 53), (56, 58), (57, 59), (58, 56), (59, 57), (60, 62), (61, 63), (62, 60), (63, 61), (64, 66), (65, 67), (66, 64), (67, 65), (68, 70), (69, 71), (70, 68), (71, 69), (72, 74), (73, 75), (74, 72), (75, 73)], ⟨[none, some [11, 29, 36, 8], some [7, 75, 44, 4], none, none, none, some [47, 48, 39, 30], some [33, 5, 27, 34], some [37, 28, 31, 38], some [6, 32, 35, 26], none, some [10, 69, 49, 24], some [25, 46, 53, 52], some [51, 50, 65, 72], some [67, 61, 73, 64], some [74, 57, 71, 70], some [59, 54, 68, 56], some [66, 45, 63, 62], some [55, 58, 60, 9]], 0⟩),
  (.arc true [31, 5] [79], ⟨[none, none, some [77, 75, 44, 36], none, none, none, some [47, 48, 76, 33], none, some [37, 27, 79, 38], some [11, 32, 35, 78], none, some [10, 69, 49, 24], some [25, 46, 53, 52], some [51, 50, 65, 72], some [67, 61, 73, 64], some [74, 57, 71, 70], some [59, 54, 68, 56], some [66, 45, 63, 62], some [55, 58, 60, 9], some [26, 8, 39, 34]], 0⟩),
  (.riii 79 26 33, ⟨[none, none, some [34, 75, 44, 36], none, none, none, some [78, 35, 39, 38], none, some [77, 48, 8, 25], some [11, 79, 27, 26], none, some [10, 69, 49, 76], some [33, 46, 53, 52], some [51, 50, 65, 72], some [67, 61, 73, 64], some [74, 57, 71, 70], some [59, 54, 68, 56], some [66, 45, 63, 62], some [55, 58, 60, 9], some [47, 32, 24, 37]], 0⟩),
  (.riii 73 60 57, ⟨[none, none, some [34, 58, 44, 36], none, none, none, some [78, 35, 39, 38], none, some [77, 48, 8, 25], some [11, 79, 27, 26], none, some [10, 69, 49, 76], some [33, 46, 53, 52], some [51, 50, 65, 60], some [75, 70, 9, 63], some [55, 64, 72, 59], some [61, 54, 68, 73], some [66, 45, 57, 74], some [62, 67, 71, 56], some [47, 32, 24, 37]], 0⟩),
  (.riii 27 78 37, ⟨[none, none, some [34, 58, 44, 27], none, none, none, some [47, 36, 76, 11], none, some [37, 48, 8, 38], some [25, 32, 35, 77], none, some [10, 69, 49, 24], some [33, 46, 53, 52], some [51, 50, 65, 60], some [75, 70, 9, 63], some [55, 64, 72, 59], some [61, 54, 68, 73], some [66, 45, 57, 74], some [62, 67, 71, 56], some [26, 39, 79, 78]], 0⟩),
  (.ri 78, ⟨[none, none, some [34, 58, 44, 27], none, none, none, some [47, 36, 39, 11], none, some [37, 48, 8, 38], some [25, 32, 35, 26], none, some [10, 69, 49, 24], some [33, 46, 53, 52], some [51, 50, 65, 60], some [75, 70, 9, 63], some [55, 64, 72, 59], some [61, 54, 68, 73], some [66, 45, 57, 74], some [62, 67, 71, 56]], 0⟩),
  (.riii 47 10 27, ⟨[none, none, some [46, 25, 49, 36], none, none, none, some [69, 9, 45, 58], none, some [37, 48, 44, 38], some [11, 32, 35, 47], none, some [34, 26, 8, 39], some [33, 10, 53, 52], some [51, 50, 65, 60], some [75, 70, 27, 63], some [55, 64, 72, 59], some [61, 54, 68, 73], some [66, 24, 57, 74], some [62, 67, 71, 56]], 0⟩),
  (.riii 75 62 59, ⟨[none, none, some [46, 25, 49, 36], none, none, none, some [69, 9, 45, 75], none, some [37, 48, 44, 38], some [11, 32, 35, 47], none, some [34, 26, 8, 39], some [33, 10, 53, 52], some [51, 50, 65, 72], some [67, 61, 73, 64], some [74, 57, 71, 70], some [59, 54, 68, 56], some [66, 24, 63, 62], some [55, 58, 60, 27]], 0⟩),
  (.riii 11 46 39, ⟨[none, none, some [34, 38, 44, 35], none, none, none, some [69, 36, 39, 75], none, some [47, 48, 8, 11], some [25, 45, 9, 26], none, some [10, 37, 49, 32], some [33, 46, 53, 52], some [51, 50, 65, 72], some [67, 61, 73, 64], some [74, 57, 71, 70], some [59, 54, 68, 56], some [66, 24, 63, 62], some [55, 58, 60, 27]], 0⟩),
  (.rii 11 35, ⟨[none, none, none, none, none, none, some [69, 36, 39, 75], none, none, some [25, 45, 48, 26], none, some [47, 37, 49, 44], some [38, 46, 53, 52], some [51, 50, 65, 72], some [67, 61, 73, 64], some [74, 57, 71, 70], some [59, 54, 68, 56], some [66, 24, 63, 62], some [55, 58, 60, 27]], 0⟩),
  (.ri 47, ⟨[none, none, none, none, none, none, some [69, 36, 39, 75], none, none, some [25, 49, 48, 26], none, none, some [38, 37, 53, 52], some [51, 50, 65, 72], some [67, 61, 73, 64], some [74, 57, 71, 70], some [59, 54, 68, 56], some [66, 24, 63, 62], some [55, 58, 60, 27]], 0⟩),
  (.rii 37 49, ⟨[none, none, none, none, none, none, some [69, 53, 52, 75], none, none, none, none, none, none, some [26, 25, 65, 72], some [67, 61, 73, 64], some [74, 57, 71, 70], some [59, 54, 68, 56], some [66, 24, 63, 62], some [55, 58, 60, 27]], 0⟩),
  (.rii 52 26, ⟨[none, none, none, none, none, none, none, none, none, none, none, none, none, none, some [67, 61, 73, 64], some [74, 57, 71, 70], some [59, 69, 68, 56], some [66, 65, 63, 62], some [75, 58, 60, 72]], 0⟩),
  (.ri 75, ⟨[none, none, none, none, none, none, none, none, none, none, none, none, none, none, some [67, 61, 60, 64], some [58, 57, 71, 70], some [59, 69, 68, 56], some [66, 65, 63, 62]], 0⟩),
  (.rii 65 69, ⟨[none, none, none, none, none, none, none, none, none, none, none, none, none, none, some [62, 61, 60, 63], some [58, 57, 56, 59]], 0⟩),
  (.rii 56 62, ⟨[], 2⟩)]

theorem oddEndChecked : CertifiedMoves oddEnd oddEndTrace := by decide +kernel

def oddFAxis : Dart := 63

theorem oddEndUnlink : Trace.endpoint oddEnd oddEndTrace = ⟨[], 2⟩ := rfl

abbrev oddA : Diagram := oddStart
abbrev oddF : Diagram := oddEnd

def oddPartnerPlanarCode : List (List ℕ) :=
  [[26, 22, 27, 21], [1, 32, 2, 33], [24, 10, 25, 9], [2, 18, 3, 17], [4, 14, 5, 13], [6, 27, 7, 28], [18, 32, 19, 31], [8, 24, 9, 23], [22, 26, 23, 25], [28, 5, 29, 6], [12, 19, 13, 20], [10, 8, 11, 7], [14, 30, 15, 29], [30, 16, 31, 15], [16, 0, 17, 3], [20, 11, 21, 12], [33, 0, 4, 1]]

def oddPartnerRaw : Diagram :=
  ⟨[some [33, 32, 21, 62], some [67, 25, 12, 64], some [29, 44, 35, 30], some [6, 24, 59, 58], some [66, 48, 37, 42], some [39, 2, 47, 36], some [13, 5, 41, 54], some [45, 8, 11, 34], some [1, 0, 31, 10], some [23, 18, 51, 20], some [63, 26, 19, 60], some [9, 28, 61, 22], some [17, 52, 55, 38], some [49, 56, 27, 50], some [53, 65, 15, 14], some [43, 46, 3, 40], some [7, 57, 16, 4]], 0⟩

theorem oddPartnerPlanarCodeChecked : Diagram.ofPD oddPartnerPlanarCode = oddPartnerRaw := by decide +kernel

def oddPartnerRawRelabel : Move :=
  .relabel [(0, 32), (1, 33), (2, 34), (3, 35), (4, 8), (5, 9), (6, 10), (7, 11), (8, 28), (9, 29), (10, 30), (11, 31), (16, 0), (17, 1), (18, 2), (19, 3), (20, 60), (21, 61), (22, 62), (23, 63), (24, 40), (25, 41), (26, 42), (27, 43), (28, 36), (29, 37), (30, 38), (31, 39), (32, 20), (33, 21), (34, 22), (35, 23), (40, 44), (41, 45), (42, 46), (43, 47), (56, 16), (57, 17), (58, 18), (59, 19), (60, 48), (61, 49), (62, 50), (63, 51), (64, 52), (65, 53), (66, 54), (67, 55), (68, 12), (69, 13), (70, 14), (71, 15), (72, 4), (73, 5), (74, 6), (75, 7), (76, 56), (77, 57), (78, 58), (79, 59), (80, 64), (81, 65), (82, 66), (83, 67), (84, 24), (85, 25), (86, 26), (87, 27)]

theorem oddPartnerRawChecked :
    CertifiedMoves oddPartner [(oddPartnerRawRelabel, oddPartnerRaw)] := by decide +kernel

def oddPartnerRawAxis : Dart := 4

theorem oddPartnerRawAnchorChecked :
    Trace.anchor oddPartner oddPartnerAxis [(oddPartnerRawRelabel, oddPartnerRaw)] = some oddPartnerRawAxis := by decide +kernel

def oddReferencePlanarCode : List (List ℕ) :=
  [[22, 33, 23, 30], [3, 31, 4, 30], [32, 21, 33, 22], [31, 5, 32, 4], [5, 20, 6, 21], [23, 6, 24, 7], [7, 24, 8, 25], [25, 2, 26, 3], [19, 27, 20, 26], [27, 19, 28, 18], [17, 29, 18, 28], [29, 17, 0, 16], [15, 8, 16, 9], [9, 14, 10, 15], [13, 10, 14, 11], [1, 12, 2, 13], [11, 0, 12, 1]]

def oddReferenceRaw : Diagram :=
  ⟨[some [11, 10, 20, 7], some [31, 12, 15, 3], some [14, 19, 1, 0], some [5, 16, 8, 6], some [13, 34, 21, 9], some [2, 18, 25, 24], some [23, 22, 49, 28], some [27, 62, 35, 4], some [37, 36, 17, 30], some [33, 32, 43, 42], some [45, 44, 39, 38], some [41, 40, 65, 50], some [55, 26, 47, 52], some [51, 58, 57, 48], some [63, 54, 53, 64], some [67, 66, 29, 56], some [59, 46, 61, 60]], 0⟩

theorem oddReferencePlanarCodeChecked : Diagram.ofPD oddReferencePlanarCode = oddReferenceRaw := by decide +kernel

def oddReferenceRawRelabel : Move :=
  .relabel []

theorem oddReferenceRawChecked :
    CertifiedMoves oddReference [(oddReferenceRawRelabel, oddReferenceRaw)] := by decide +kernel

def oddReferenceRawAxis : Dart := 7

theorem oddReferenceRawAnchorChecked :
    Trace.anchor oddReference oddReferenceAxis [(oddReferenceRawRelabel, oddReferenceRaw)] = some oddReferenceRawAxis := by decide +kernel

def oddBPlanarCode : List (List ℕ) :=
  [[28, 32, 29, 31], [30, 8, 31, 7], [6, 30, 7, 29], [12, 27, 13, 28], [33, 27, 34, 26], [25, 16, 26, 17], [17, 24, 18, 25], [35, 2, 36, 3], [3, 34, 4, 35], [4, 12, 5, 11], [8, 6, 9, 5], [9, 14, 10, 15], [15, 10, 16, 11], [13, 33, 14, 32], [1, 19, 2, 18], [19, 37, 20, 36], [37, 21, 38, 20], [40, 24, 41, 23], [41, 38, 42, 39], [22, 40, 23, 43], [39, 42, 0, 43], [21, 1, 22, 0]]

def oddBRaw : Diagram :=
  ⟨[some [15, 55, 11, 6], some [9, 40, 3, 10], some [41, 4, 7, 2], some [37, 17, 52, 0], some [53, 13, 33, 22], some [27, 50, 19, 24], some [23, 69, 59, 20], some [35, 58, 63, 32], some [31, 18, 36, 28], some [34, 12, 43, 51], some [5, 8, 44, 38], some [42, 54, 49, 48], some [47, 46, 21, 39], some [14, 16, 45, 1], some [85, 60, 29, 26], some [57, 64, 67, 30], some [61, 84, 73, 62], some [77, 25, 72, 78], some [70, 66, 81, 80], some [86, 68, 71, 83], some [75, 74, 87, 79], some [65, 56, 76, 82]], 0⟩

theorem oddBPlanarCodeChecked : Diagram.ofPD oddBPlanarCode = oddBRaw := by decide +kernel

def oddBRawRelabel : Move :=
  .relabel []

theorem oddBRawChecked :
    CertifiedMoves oddB [(oddBRawRelabel, oddBRaw)] := by decide +kernel

def oddBRawAxis : Dart := 68

theorem oddBRawAnchorChecked :
    Trace.anchor oddB oddBAxis [(oddBRawRelabel, oddBRaw)] = some oddBRawAxis := by decide +kernel

def oddCPlanarCode : List (List ℕ) :=
  [[13, 11, 14, 10], [11, 29, 12, 28], [29, 13, 30, 12], [23, 14, 24, 15], [15, 22, 16, 23], [35, 2, 36, 3], [3, 34, 4, 35], [33, 25, 34, 24], [27, 33, 28, 32], [6, 31, 7, 32], [30, 5, 31, 6], [26, 8, 27, 7], [8, 26, 9, 25], [4, 9, 5, 10], [1, 17, 2, 16], [17, 37, 18, 36], [37, 19, 38, 18], [40, 22, 41, 21], [41, 38, 42, 39], [20, 40, 21, 43], [39, 42, 0, 43], [19, 1, 20, 0]]

def oddCRaw : Diagram :=
  ⟨[some [9, 4, 13, 55], some [1, 8, 11, 34], some [5, 0, 40, 6], some [19, 2, 31, 16], some [15, 69, 59, 12], some [27, 58, 63, 24], some [23, 30, 52, 20], some [33, 51, 25, 14], some [46, 28, 7, 39], some [43, 42, 47, 35], some [10, 54, 37, 36], some [49, 48, 32, 38], some [45, 44, 53, 29], some [26, 50, 41, 3], some [85, 60, 21, 18], some [57, 64, 67, 22], some [61, 84, 73, 62], some [77, 17, 72, 78], some [70, 66, 81, 80], some [86, 68, 71, 83], some [75, 74, 87, 79], some [65, 56, 76, 82]], 0⟩

theorem oddCPlanarCodeChecked : Diagram.ofPD oddCPlanarCode = oddCRaw := by decide +kernel

def oddCRawRelabel : Move :=
  .relabel []

theorem oddCRawChecked :
    CertifiedMoves oddC [(oddCRawRelabel, oddCRaw)] := by decide +kernel

def oddCRawAxis : Dart := 68

theorem oddCRawAnchorChecked :
    Trace.anchor oddC oddCAxis [(oddCRawRelabel, oddCRaw)] = some oddCRawAxis := by decide +kernel

def oddDPlanarCode : List (List ℕ) :=
  [[13, 11, 14, 10], [11, 29, 12, 28], [29, 13, 30, 12], [23, 14, 24, 15], [15, 22, 16, 23], [35, 2, 36, 3], [3, 34, 4, 35], [33, 25, 34, 24], [32, 27, 33, 28], [6, 31, 7, 32], [30, 5, 31, 6], [26, 8, 27, 7], [8, 26, 9, 25], [4, 9, 5, 10], [1, 17, 2, 16], [17, 37, 18, 36], [37, 19, 38, 18], [40, 22, 41, 21], [41, 38, 42, 39], [20, 40, 21, 43], [39, 42, 0, 43], [19, 1, 20, 0]]

def oddDRaw : Diagram :=
  ⟨[some [9, 4, 13, 55], some [1, 8, 11, 35], some [5, 0, 40, 6], some [19, 2, 31, 16], some [15, 69, 59, 12], some [27, 58, 63, 24], some [23, 30, 52, 20], some [34, 51, 25, 14], some [39, 46, 28, 7], some [43, 42, 47, 32], some [10, 54, 37, 36], some [49, 48, 33, 38], some [45, 44, 53, 29], some [26, 50, 41, 3], some [85, 60, 21, 18], some [57, 64, 67, 22], some [61, 84, 73, 62], some [77, 17, 72, 78], some [70, 66, 81, 80], some [86, 68, 71, 83], some [75, 74, 87, 79], some [65, 56, 76, 82]], 0⟩

theorem oddDPlanarCodeChecked : Diagram.ofPD oddDPlanarCode = oddDRaw := by decide +kernel

def oddDRawRelabel : Move :=
  .relabel []

theorem oddDRawChecked :
    CertifiedMoves oddD [(oddDRawRelabel, oddDRaw)] := by decide +kernel

def oddDRawAxis : Dart := 68

theorem oddDRawAnchorChecked :
    Trace.anchor oddD oddDAxis [(oddDRawRelabel, oddDRaw)] = some oddDRawAxis := by decide +kernel

def oddEPlanarCode : List (List ℕ) :=
  [[9, 30, 10, 31], [27, 8, 28, 9], [7, 28, 8, 29], [29, 6, 30, 7], [5, 10, 6, 11], [31, 5, 32, 4], [15, 23, 16, 22], [23, 13, 24, 12], [13, 25, 14, 24], [25, 15, 26, 14], [11, 27, 12, 26], [3, 16, 4, 17], [21, 2, 22, 3], [1, 20, 2, 21], [32, 35, 33, 36], [19, 35, 20, 34], [36, 33, 37, 0], [37, 19, 34, 18], [17, 0, 18, 1]]

def oddERaw : Diagram :=
  ⟨[some [7, 14, 17, 20], some [41, 10, 9, 0], some [15, 6, 5, 12], some [11, 18, 1, 8], some [21, 2, 13, 40], some [3, 16, 56, 46], some [37, 28, 45, 50], some [25, 32, 35, 42], some [29, 36, 39, 30], some [33, 24, 43, 34], some [19, 4, 31, 38], some [51, 26, 23, 72], some [55, 54, 27, 44], some [75, 62, 49, 48], some [22, 61, 65, 64], some [69, 57, 53, 70], some [59, 58, 68, 73], some [66, 60, 63, 74], some [47, 67, 71, 52]], 0⟩

theorem oddEPlanarCodeChecked : Diagram.ofPD oddEPlanarCode = oddERaw := by decide +kernel

def oddERawRelabel : Move :=
  .relabel []

theorem oddERawChecked :
    CertifiedMoves oddE [(oddERawRelabel, oddERaw)] := by decide +kernel

def oddERawAxis : Dart := 63

theorem oddERawAnchorChecked :
    Trace.anchor oddE oddEAxis [(oddERawRelabel, oddERaw)] = some oddERawAxis := by decide +kernel

end Trefoil.Section2DiagramData
