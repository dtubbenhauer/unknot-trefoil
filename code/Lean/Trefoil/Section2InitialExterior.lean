import Trefoil.Section2Triangulations

/-!
# Marked initial tetrahedra from signed planar diagrams

This module computes the octahedral diagram exterior, subdividing each
crossing octahedron into four tetrahedra. Two vertices represent the
north and south poles. Meridian normal curves are drawn at an over-to-under
transition on each component. The longitude is the right-side parallel
corrected by the self-writhe.

The face labels and preferred longitude use the conventions of
SnapPy 3.3.2, kernel/kernel_code/link_complement.c. The signed PD
ports use Spherogram 2.4.1. The geometric interpretation of this
construction and subsequent removal of the finite vertices are
separate inputs.
-/

namespace Trefoil.Section2InitialExterior

open Section2Triangulations

/-- The four cyclic arc labels at each crossing, its sign, and the
lengths of the oriented components in arc-label order. -/
structure SignedPD where
  arcs : Array (Array Nat)
  positive : Array Bool
  componentSizes : Array Nat
  deriving Repr

abbrev HalfEdge := ℕ × ℕ

def ports := [0, 1, 2, 3]

def SignedPD.arc (D : SignedPD) (c p : Nat) : Nat :=
  (D.arcs.getD c #[]).getD p 0

def SignedPD.pos (D : SignedPD) (c : Nat) : Bool :=
  D.positive.getD c false

def SignedPD.darts (D : SignedPD) : List HalfEdge :=
  (List.range D.arcs.size).flatMap fun c => ports.map (c, ·)

def SignedPD.incidence (D : SignedPD) : Array (List HalfEdge) :=
  D.darts.foldl (fun incid (c, p) =>
    let a := D.arc c p
    incid.set! a ((c, p) :: incid.getD a [])) (Array.replicate (2 * D.arcs.size) [])

def SignedPD.boundaries (D : SignedPD) : List Nat :=
  (D.componentSizes.toList.scanl (· + ·) 0).tail

def SignedPD.component (D : SignedPD) (arc : Nat) : Nat :=
  (D.boundaries.takeWhile (· ≤ arc)).length

def SignedPD.nextArc (D : SignedPD) (arc : Nat) : Nat :=
  let i := D.component arc
  if D.boundaries[i]? = some (arc + 1) then
    if i = 0 then 0 else D.boundaries[i - 1]?.getD 0
  else arc + 1

/-- The local cyclic coordinate is chosen so slot zero is incoming Y,
one is outgoing X, two is outgoing Y, and three is incoming X. -/
def SignedPD.direction (D : SignedPD) (c p : Nat) : Nat :=
  if D.pos c then p else (p + 3) % 4

def SignedPD.inverseDirection (D : SignedPD) (c d : Nat) : Nat :=
  if D.pos c then d else (d + 1) % 4

def incoming (d : Nat) : Bool := d == 0 || d == 3

def isX (d : Nat) : Bool := d % 2 == 1

def SignedPD.oppositeDart (D : SignedPD) (I : Array (List HalfEdge))
    (c d : Nat) : HalfEdge :=
  let p := D.inverseDirection c d
  let oc := I.getD (D.arc c p) []
  (oc.find? (· != (c, p))).getD (c, p)

def SignedPD.checkWith (D : SignedPD) (I : Array (List HalfEdge)) : Bool :=
  D.positive.size == D.arcs.size &&
  D.arcs.all (fun a => a.size == 4 && a.all (· < 2 * D.arcs.size)) &&
  D.componentSizes.all (0 < ·) &&
  D.componentSizes.toList.sum == 2 * D.arcs.size &&
  I.all (fun os => os.length == 2) &&
  D.darts.all (fun (c, p) =>
    let d := D.direction c p
    let (other, q) := D.oppositeDart I c d
    incoming d != incoming (D.direction other q) &&
    (!incoming d || D.nextArc (D.arc c p) == D.arc c ((p + 2) % 4)))

def SignedPD.check (D : SignedPD) : Bool := D.checkWith D.incidence

/-- Pole cusps use labels zero and one. Actual link components start at two.
Curves use the indexing of the triangulation checker. -/
structure InitialExterior where
  tetrahedra : Triangulation
  cusps : CuspMarking

private def neighboringTet (D : SignedPD) (I : Array (List HalfEdge))
    (c d x y : Nat) : Nat :=
  let (other, p) := D.oppositeDart I c d
  4 * other + (if isX (D.direction other p) then x else y)

private def octahedralFaces (D : SignedPD) (I : Array (List HalfEdge))
    (c tet : Nat) : Array TetImage :=
  let inside :=
    if D.pos c then #[(1,3), (0,2), (3,1), (2,0)]
    else #[(3,1), (2,0), (1,3), (0,2)]
  let (south, north) := inside.getD tet (0,0)
  let follow := neighboringTet D I c
  let second :=
    match tet with
    | 0 => follow 2 2 3
    | 1 => follow 3 0 1
    | 2 => follow 0 0 1
    | _ => follow 1 2 3
  let third :=
    match tet with
    | 0 => follow 1 1 2
    | 1 => follow 2 1 2
    | 2 => follow 3 3 0
    | _ => follow 0 3 0
  #[4*c + south, 4*c + north, second, third].map (fun u => ⟨u, #[0,1,3,2]⟩)

private def strandComponent (D : SignedPD) (c : Nat) (x : Bool) : Nat :=
  D.component (D.arc c (D.inverseDirection c (if x then 3 else 0)))

private def localCusps (D : SignedPD) (c t : Nat) : Array Nat :=
  let x := 2 + strandComponent D c true
  let y := 2 + strandComponent D c false
  if t % 2 == 0 then #[0, 1, x, y] else #[0, 1, y, x]

private def crossOver (D : SignedPD) (c : Nat) (x : Bool) : Bool := D.pos c == x

private def forward (D : SignedPD) (I : Array (List HalfEdge))
    (c : Nat) (x : Bool) : Nat × Bool :=
  let (other, p) := D.oppositeDart I c (if x then 1 else 2)
  (other, isX (D.direction other p))

private def transition (D : SignedPD) (I : Array (List HalfEdge))
    (c : Nat) (x : Bool) : Nat → Option ((Nat × Bool) × (Nat × Bool))
  | 0 => none
  | fuel + 1 =>
      let (other, y) := forward D I c x
      if crossOver D c x && !crossOver D other y then some ((c, x), (other, y))
      else transition D I other y fuel

private abbrev LocalCurve := List (Nat × Nat × Nat × Int)

private def overMeridian (x : Bool) : LocalCurve :=
  if x then [(3,3,1,-1), (3,3,2,1), (0,2,1,1), (0,2,3,-1)]
  else [(0,3,1,-1), (0,3,2,1), (1,2,1,1), (1,2,3,-1)]

private def underMeridian (x : Bool) : LocalCurve :=
  if x then [(1,3,0,-1), (1,3,2,1), (2,2,0,1), (2,2,3,-1)]
  else [(2,3,0,-1), (2,3,2,1), (3,2,0,1), (3,2,3,-1)]

private def parallelLongitude (p : Bool) : LocalCurve :=
  let (x, y) := if p then (0,1) else (1,0)
  [(2,2,3,1), (3,3,2,-1), (2,2,x,-1), (3,3,x,1),
   (3,2,3,1), (0,3,2,-1), (3,2,y,-1), (0,3,y,1)]

private def addLocal (a : Array Int) (c : Nat) (L : LocalCurve) : Array Int :=
  L.foldl (fun result (tet, v, f, w) => result.set! (16*(4*c+tet)+4*v+f) w) a

private def meridianTable (D : SignedPD) (I : Array (List HalfEdge)) :
    Option (Array Int) :=
  let initial := (Array.replicate (64 * D.arcs.size) 0, ([] : List Nat))
  let choices := (List.range D.arcs.size).foldlM (fun (a, done) c =>
    let component := strandComponent D c true
    if done.contains component then some (a, done) else do
      let ((over, x), (under, y)) ← transition D I c true (2 * D.arcs.size)
      pure (addLocal (addLocal a over (overMeridian x)) under (underMeridian y),
        component :: done)) initial
  choices.bind fun (m, seen) => if seen.length = D.componentSizes.size then some m else none

private def selfWrithe (D : SignedPD) : Array Int :=
  (List.range D.arcs.size).foldl (fun w c =>
    let x := strandComponent D c true
    if x = strandComponent D c false then
      w.set! x (w.getD x 0 + if D.pos c then 1 else -1)
    else w) (Array.replicate D.componentSizes.size 0)

/-- The local checks use explicitly named intermediate tables, so
the same folds need not be reduced at each arc or curve lookup. -/
def givenFaces (D : SignedPD) (I : Array (List HalfEdge)) : Array Nat :=
  (Array.range (4 * D.arcs.size)).flatMap fun u =>
    (octahedralFaces D I (u / 4) (u % 4)).map TetImage.tet

def givenCusps (D : SignedPD) : Array Nat :=
  (Array.range (4 * D.arcs.size)).flatMap (fun u => localCusps D (u / 4) (u % 4))

def givenParallel (D : SignedPD) : Array Int :=
  (List.range D.arcs.size).foldl
    (fun a c => addLocal a c (parallelLongitude (D.pos c)))
    (Array.replicate (64 * D.arcs.size) 0)

def givenWrithe (D : SignedPD) : Array Int := selfWrithe D

def givenMeridians (D : SignedPD) (I : Array (List HalfEdge)) : Option (Array Int) :=
  meridianTable D I

def correctLongitudes (mu para : Array Int) (cusps : Array Nat) (writhe : Array Int) :
    Array Int :=
  (Array.range mu.size).map fun j =>
    let cuspLabel := cusps.getD (j / 4) 0
    para.getD j 0 - writhe.getD (cuspLabel - 2) 0 * mu.getD j 0

private def buildUsing (D : SignedPD) (I : Array (List HalfEdge)) : Option InitialExterior :=
  (givenMeridians D I).map fun meridian =>
    let tets := (Array.range (4*D.arcs.size)).map
      (fun u => octahedralFaces D I (u / 4) (u % 4))
    let cusps := givenCusps D
    let adjusted := correctLongitudes meridian (givenParallel D) cusps (givenWrithe D)
    ⟨tets, ⟨2+D.componentSizes.size, cusps, .array meridian, .array adjusted⟩⟩

/-- The exact incidence and markings of the octahedral diagram exterior. -/
def build (D : SignedPD) : Option InitialExterior :=
  buildUsing D D.incidence

private def checkBuilt (E : InitialExterior) (neighbor cuspLabels : Array Nat)
    (mu lambda : Array Int) : Bool :=
  (E.tetrahedra.flatMap (fun row => row.map TetImage.tet)) == neighbor &&
  E.cusps.cuspIndices == cuspLabels &&
  (match E.cusps.meridian with
    | .array a => a == mu
    | .packed .. => false) &&
  (match E.cusps.longitude with
    | .array a => a == lambda
    | .packed .. => false)

/-- Check the finite snapshot of the marked octahedral exterior. The
vertex map on all its faces is the fixed transposition of 2 and 3. -/
def checkSnapshot (D : SignedPD) (neighbor cuspLabels : Array Nat)
    (mu lambda : Array Int) : Bool :=
  D.check && (build D).any (fun E => checkBuilt E neighbor cuspLabels mu lambda)

/-- A staged evaluation of the same explicit exterior. The intermediate
table equalities can be checked independently of the larger final arrays. -/
theorem checkSnapshot_of_tables (D : SignedPD) (I : Array (List HalfEdge))
    (neighbor cuspLabels : Array Nat) (mu para lambda : Array Int) (writhe : Array Int)
    (hI : D.incidence = I) (hD : D.checkWith I = true)
    (hFaces : (givenFaces D I == neighbor) = true)
    (hCusps : givenCusps D = cuspLabels)
    (hMu : givenMeridians D I = some mu) (hPara : givenParallel D = para)
    (hWrithe : givenWrithe D = writhe)
    (hLambda : (correctLongitudes mu para cuspLabels writhe == lambda) = true) :
    checkSnapshot D neighbor cuspLabels mu lambda = true := by
  have hTets : ((Array.range (4*D.arcs.size)).map
      (fun u => octahedralFaces D I (u / 4) (u % 4))).flatMap
      (fun row => row.map TetImage.tet) = givenFaces D I := by
    simp [givenFaces, Array.flatMap_map]
  simp [checkSnapshot, SignedPD.check, build, buildUsing, hI, hD,
    hMu, hPara, hCusps, hWrithe, checkBuilt, hTets, hFaces, hLambda]

end Trefoil.Section2InitialExterior
