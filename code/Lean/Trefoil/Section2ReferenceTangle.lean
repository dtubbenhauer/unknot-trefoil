import Trefoil.Section2Arithmetic
import Trefoil.Section2DiagramData
import Trefoil.Section2DiagramDomains

/-!
# The reference tangles in Section 2

A four-port tangle is a matching on boundary terminals and crossing darts.
Terminals are bottom left, bottom right, top left, top right, in that order.
Crossing ports have the diagram convention of `Section2DiagramMoves`.
Operations sew pairs of boundary darts, following the resulting paths until
reaching a surviving dart and counting components with no crossing darts.
-/

namespace Trefoil.Section2ReferenceTangle

open Section2DiagramMoves Section2DiagramData

set_option maxHeartbeats 0
set_option maxRecDepth 20000

/-- Ports 0–3 are boundary terminals. Crossing `i` has darts `4 + 4*i`
through `7 + 4*i`. Each edge is recorded once as an unordered pair. -/
structure Tangle where
  crossings : ℕ
  edges : List (Dart × Dart)
  circles : ℕ := 0
  deriving DecidableEq, Repr

/-- Follow a segment of a sewn diagram to its surviving endpoint. -/
def followSew (edges seams : List (Dart × Dart)) (a : Dart) : ℕ → Option Dart
  | 0 => none
  | fuel + 1 => (paired edges a).bind fun b =>
    match paired seams b with
    | none => some b
    | some c => followSew edges seams c fuel

/-- Count closed components entirely supported on seams. The least dart
among both directions around a circle counts that circle once. -/
def seamCircles (edges seams : List (Dart × Dart)) : ℕ :=
  let seamDarts := seams.flatMap (fun (a, b) => [a, b])
  let next := fun a => (paired edges a).bind (paired seams)
  let fuel := seamDarts.length + 1
  (seamDarts.filter fun a =>
    let trace := orbit next a fuel
    trace.length == fuel && trace.all (fun b => a ≤ b) &&
      (paired seams a).all (fun b => (orbit next b fuel).all (fun c => a ≤ c))).length

/-- An explicit set of sewn edges on the surviving darts. -/
def sewEdges (edges seams : List (Dart × Dart)) (survive : List Dart) : List (Dart × Dart) :=
  survive.filterMap fun a => (followSew edges seams a (2 * seams.length + 1)).bind fun b =>
    if a < b then some (a, b) else none

def Tangle.remapEdges (T : Tangle) (f : Dart → Dart) : List (Dart × Dart) :=
  T.edges.map fun (a, b) => (f a, f b)

/-- Horizontal composition connects the two right terminals of the left
factor with the two left terminals of the right factor. -/
def horizontal (A B : Tangle) : Tangle :=
  let n := A.crossings + B.crossings
  let seam := 4 + 4 * n
  let fA : Dart → Dart := fun
    | 1 => seam
    | 3 => seam + 1
    | d => d
  let fB : Dart → Dart := fun
    | 0 => seam + 2
    | 1 => 1
    | 2 => seam + 3
    | 3 => 3
    | d => d + 4 * A.crossings
  let edges := A.remapEdges fA ++ B.remapEdges fB
  let connect := [(seam, seam + 2), (seam + 1, seam + 3)]
  ⟨n, sewEdges edges connect (List.range seam), A.circles + B.circles + seamCircles edges connect⟩

/-- Reverse the crossings while keeping the four boundary terminals. -/
def mirror (T : Tangle) : Tangle :=
  { T with edges := T.remapEdges (fun d => if d < 4 then d else rotate d 3) }

/-- The standard reciprocal is a quarter turn followed by mirroring.
The new list of terminals reads the old ones in order `[1,3,0,2]`. -/
def invert (T : Tangle) : Tangle :=
  let replug : Dart → Dart := fun
    | 0 => 2
    | 1 => 0
    | 2 => 3
    | 3 => 1
    | d => d
  mirror { T with edges := T.remapEdges replug }

/-- The two caps of the numerator closure. -/
def numeratorClose (T : Tangle) : Diagram :=
  let connect := [(0, 1), (2, 3)]
  let rows := (List.range T.crossings).map fun i => some <|
    (List.range 4).filterMap fun p =>
      (followSew T.edges connect (4 + 4 * i + p) 5).map fun d => d - 4
  ⟨rows, T.circles + seamCircles T.edges connect⟩

def zeroTangle : Tangle := ⟨0, [(0, 1), (2, 3)], 0⟩

def infinityTangle : Tangle := ⟨0, [(0, 2), (1, 3)], 0⟩

def oneTangle : Tangle := ⟨1, [(0, 4), (1, 5), (2, 7), (3, 6)], 0⟩

def positiveTwists : ℕ → Tangle
  | 0 => zeroTangle
  | 1 => oneTangle
  | n + 2 => horizontal (positiveTwists (n + 1)) oneTangle

def integerTwists (n : ℤ) : Tangle :=
  if n < 0 then mirror (positiveTwists n.natAbs) else positiveTwists n.natAbs

def continuedTangle : List ℤ → Tangle
  | [] => infinityTangle
  | a :: tail => horizontal (integerTwists a) (invert (continuedTangle tail))

/-- The two horizontal strands and their encircling component. The four
crossings read left top, left bottom, right top, right bottom. -/
def axisTangle : Tangle :=
  ⟨4, [(5, 11), (12, 18), (7, 14), (9, 16), (6, 15), (10, 19),
    (0, 8), (1, 17), (2, 4), (3, 13)], 0⟩

def remainderWeights : List ℤ := [0, 2, 1, 4, 3, 2]

/-- The right-hand factor in the reference tangle is the stated slope. -/
theorem remainder_fraction : Arithmetic.plusPair remainderWeights = (37, 104) := by decide

/-- Explicit intermediate edge tables make the checked chart construction
reduce one sewing at a time. -/
private def remainderStage1 : Tangle := ⟨2, [(0, 4), (1, 9), (2, 7), (3, 10), (5, 8), (6, 11)], 0⟩

private theorem remainderStage1_eq : continuedTangle [2] = remainderStage1 := by
  decide

private def remainderStage2 : Tangle := ⟨5, [(0, 4), (1, 21), (2, 7), (3, 18), (5, 8), (6, 11), (9, 12), (10, 15), (13, 20), (14, 19), (16, 23), (17, 22)], 0⟩

private theorem remainderStage2_eq : continuedTangle [3, 2] = remainderStage2 := by
  change horizontal (integerTwists 3) (invert (continuedTangle [2])) = _
  rw [remainderStage1_eq]
  decide

private def remainderStage3 : Tangle := ⟨9, [(0, 4), (1, 33), (2, 7), (3, 22), (5, 8), (6, 11), (9, 12), (10, 15), (13, 16), (14, 19), (17, 36), (18, 23), (20, 27), (21, 26), (24, 31), (25, 30), (28, 39), (29, 34), (32, 37), (35, 38)], 0⟩

private theorem remainderStage3_eq : continuedTangle [4, 3, 2] = remainderStage3 := by
  change horizontal (integerTwists 4) (invert (continuedTangle [3, 2])) = _
  rw [remainderStage2_eq]
  decide

private def remainderStage4 : Tangle := ⟨10, [(0, 4), (1, 25), (2, 7), (3, 10), (5, 36), (6, 11), (8, 15), (9, 14), (12, 19), (13, 18), (16, 23), (17, 22), (20, 43), (21, 26), (24, 29), (27, 30), (28, 33), (31, 34), (32, 37), (35, 42), (38, 41), (39, 40)], 0⟩

private theorem remainderStage4_eq : continuedTangle [1, 4, 3, 2] = remainderStage4 := by
  change horizontal (integerTwists 1) (invert (continuedTangle [4, 3, 2])) = _
  rw [remainderStage3_eq]
  decide

private def remainderStage5 : Tangle := ⟨12, [(0, 4), (1, 17), (2, 7), (3, 14), (5, 8), (6, 11), (9, 32), (10, 15), (12, 47), (13, 18), (16, 21), (19, 22), (20, 25), (23, 26), (24, 29), (27, 30), (28, 33), (31, 50), (34, 37), (35, 36), (38, 41), (39, 40), (42, 49), (43, 44), (45, 48), (46, 51)], 0⟩

private theorem remainderStage5_eq : continuedTangle [2, 1, 4, 3, 2] = remainderStage5 := by
  change horizontal (integerTwists 2) (invert (continuedTangle [1, 4, 3, 2])) = _
  rw [remainderStage4_eq]
  decide

private def remainderStage6 : Tangle := ⟨12, [(0, 16), (1, 13), (2, 7), (3, 6), (4, 11), (5, 10), (8, 35), (9, 14), (12, 17), (15, 46), (18, 21), (19, 20), (22, 25), (23, 24), (26, 29), (27, 28), (30, 49), (31, 32), (33, 36), (34, 39), (37, 40), (38, 43), (41, 48), (42, 47), (44, 51), (45, 50)], 0⟩

private theorem remainderStage6_eq : continuedTangle [0, 2, 1, 4, 3, 2] = remainderStage6 := by
  change horizontal (integerTwists 0) (invert (continuedTangle [2, 1, 4, 3, 2])) = _
  rw [remainderStage5_eq]
  decide

/-- The chart with an encircling crossing circle and a rational remainder. -/
def axisChartDiagram (twists : ℤ) (tail : List ℤ) : Diagram :=
  numeratorClose (horizontal (horizontal axisTangle (integerTwists twists))
    (continuedTangle tail))

def builtReference (b : Fin 2) : Diagram := axisChartDiagram b.val remainderWeights

/-- This dart runs along the crossing circle at its lower left crossing. -/
def builtReferenceAxis : Dart := 7

private def computedEven : Diagram := ⟨[some [18, 7, 11, 10], some [25, 12, 15, 1], some [14, 19, 3, 2], some [5, 28, 8, 6], some [23, 22, 0, 9], some [47, 26, 17, 16], some [29, 4, 21, 58], some [13, 24, 33, 32], some [31, 30, 37, 36], some [35, 34, 41, 40], some [39, 38, 61, 44], some [43, 48, 51, 20], some [45, 52, 55, 46], some [49, 60, 59, 50], some [63, 62, 27, 54], some [53, 42, 57, 56]], 0⟩

private theorem builtEven_eq : builtReference 0 = computedEven := by
  unfold builtReference axisChartDiagram remainderWeights
  rw [remainderStage6_eq]
  decide

private def computedOdd : Diagram := ⟨[some [22, 7, 11, 10], some [29, 12, 15, 1], some [14, 19, 3, 2], some [5, 16, 8, 6], some [13, 32, 23, 9], some [27, 26, 0, 18], some [51, 30, 21, 20], some [33, 4, 25, 62], some [17, 28, 37, 36], some [35, 34, 41, 40], some [39, 38, 45, 44], some [43, 42, 65, 48], some [47, 52, 55, 24], some [49, 56, 59, 50], some [53, 64, 63, 54], some [67, 66, 31, 58], some [57, 46, 61, 60]], 0⟩

private theorem builtOdd_eq : builtReference 1 = computedOdd := by
  unfold builtReference axisChartDiagram remainderWeights
  rw [remainderStage6_eq]
  decide

/-- Links oriented by Spherogram rotate some crossing ports by 180 degrees.
These relabelings preserve the counterclockwise order and the overstrand. -/
def referenceRelabel (b : Fin 2) : List (Dart × Dart) :=
  let changed := if b = 0 then [0, 4, 6, 12, 15] else [0, 5, 6, 7, 8, 10, 12, 14]
  changed.flatMap fun i => (List.range 4).map fun p => (4 * i + p, 4 * i + (p + 2) % 4)

theorem evenReference_constructor :
    (builtReference 0).checkRelabel evenReference (referenceRelabel 0) = true := by
  rw [builtEven_eq]
  decide

theorem oddReference_constructor :
    (builtReference 1).checkRelabel oddReference (referenceRelabel 1) = true := by
  rw [builtOdd_eq]
  decide

theorem evenReference_axis : lookup builtReferenceAxis (referenceRelabel 0) = evenReferenceAxis := by
  decide

theorem oddReference_axis : lookup builtReferenceAxis (referenceRelabel 1) = oddReferenceAxis := by
  decide

theorem evenBuiltReferenceDomain : (builtReference 0).markedDiagram builtReferenceAxis = true := by
  rw [builtEven_eq]
  decide

theorem oddBuiltReferenceDomain : (builtReference 1).markedDiagram builtReferenceAxis = true := by
  rw [builtOdd_eq]
  decide

private theorem parity_cases (b : Fin 2) : b = 0 ∨ b = 1 := by
  have hb := b.isLt
  by_cases h : b.val = 0
  · exact Or.inl (Fin.ext h)
  · exact Or.inr (Fin.ext (by change b.val = 1; omega))

/-- The marked dart follows the encircling component through the four
axis crossings without entering the twist boxes or the remainder. -/
theorem builtReference_axis_cycle (b : Fin 2) :
    orbit (builtReference b).strandNext builtReferenceAxis 5 = [7, 12, 8, 3, 7] := by
  rcases parity_cases b with rfl | rfl
  · rw [builtEven_eq]
    decide
  · rw [builtOdd_eq]
    decide

theorem builtReference_valid (b : Fin 2) : (builtReference b).valid = true := by
  rcases parity_cases b with rfl | rfl
  · rw [builtEven_eq]
    decide
  · rw [builtOdd_eq]
    decide

/-- The side-by-side rational chart with no surgery axis. -/
def ordinaryReference (twists : ℤ) (tail : List ℤ) : Diagram :=
  numeratorClose (horizontal (integerTwists twists) (continuedTangle tail))

private def computedSeed : Diagram := ⟨[some [17, 4, 7, 10], some [1, 20, 11, 2], some [15, 14, 3, 6], some [39, 18, 9, 8], some [21, 0, 13, 50], some [5, 16, 25, 24], some [23, 22, 29, 28], some [27, 26, 33, 32], some [31, 30, 53, 36], some [35, 40, 43, 12], some [37, 44, 47, 38], some [41, 52, 51, 42], some [55, 54, 19, 46], some [45, 34, 49, 48]], 0⟩

private theorem ordinarySeed_eq : ordinaryReference 2 remainderWeights = computedSeed := by
  unfold ordinaryReference remainderWeights
  rw [remainderStage6_eq]
  decide

def seedReferenceRelabel : List (Dart × Dart) :=
  ([1, 2, 4, 10, 13] : List ℕ).flatMap fun i =>
    (List.range 4).map fun p => (4 * i + p, 4 * i + (p + 2) % 4)

/-- The ordinary reference used in the independent replay is exactly the
ordinary chart with two half-twists, up to even port rotations. -/
theorem seedReference_constructor :
    (ordinaryReference 2 remainderWeights).checkRelabel seedReference seedReferenceRelabel = true := by
  rw [ordinarySeed_eq]
  decide

theorem seedReference_constructor_domain :
    (ordinaryReference 2 remainderWeights).knotDiagram = true := by
  rw [ordinarySeed_eq]
  decide

end Trefoil.Section2ReferenceTangle
