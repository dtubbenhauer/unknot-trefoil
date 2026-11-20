import Mathlib.Data.List.Basic
import Lean.Elab.Tactic.Omega

/-!
# Finite diagram moves for Section 2

A crossing has four darts in counterclockwise order. Darts 0 and 2 are
the under strand. The diagram is given by the fixed-point-free involution
pairing its darts across edges, together with its isolated circles.

The finite checks use unoriented diagrams. Interpreting their rotation
systems as planar diagrams, the moves are local Reidemeister moves,
even port rotations and vertex relabeling, an over/under arc isotopy,
and the cut along a common pair of dual faces. The link interpretation
and the general soundness of the corresponding geometry are separate.
-/

namespace Trefoil.Section2DiagramMoves

abbrev Dart := ℕ

def vertex (a : Dart) : ℕ := a / 4

def port (a : Dart) : ℕ := a % 4

def rotate (a : Dart) (k : ℕ) : Dart := 4 * vertex a + (port a + k) % 4

/-- Sparse table of four adjacent darts for each crossing, and the number
of circle components with zero crossings. Indices may remain unused after
crossings are deleted. -/
structure Diagram where
  rows : List (Option (List Dart))
  circles : ℕ
  deriving DecidableEq, Repr

def Diagram.row (D : Diagram) (i : ℕ) : Option (List Dart) :=
  (D.rows[i]?).join

def Diagram.active (D : Diagram) (i : ℕ) : Bool := (D.row i).isSome

def Diagram.adj (D : Diagram) (a : Dart) : Option Dart :=
  (D.row (vertex a)).bind (fun r => r[port a]?)

def Diagram.darts (D : Diagram) : List Dart :=
  (List.range D.rows.length).flatMap fun i =>
    if D.active i then [4 * i, 4 * i + 1, 4 * i + 2, 4 * i + 3] else []

/-- Convert arc labels of a planar diagram code to the half-edge pairing.
The validity check rejects a label without exactly two occurrences. -/
def Diagram.ofPD (pd : List (List ℕ)) : Diagram :=
  let labels := pd.flatten
  let slots := List.range labels.length
  let opposite := fun a => slots.find? (fun b => a != b && labels[a]? == labels[b]?)
  ⟨(List.range pd.length).map (fun i => some
    ((List.range 4).map fun p => (opposite (4 * i + p)).getD (4 * i + p))), 0⟩

/-- Check the two-sided edge pairing and row lengths. -/
def Diagram.valid (D : Diagram) : Bool :=
  D.rows.all (fun row => row.all (fun p => p.length == 4)) &&
    D.darts.all (fun a =>
      match D.adj a with
      | none => false
      | some b => a != b && D.adj b == some a)

/-- Bounded list of darts in an orbit, starting at the specified dart.
The supplied fuel exceeds the size of every dart set used here. -/
def orbit (next : Dart → Option Dart) (a : Dart) : ℕ → List Dart
  | 0 => []
  | n + 1 => a :: match next a with | some b => orbit next b n | none => []

def Diagram.faceCorner (D : Diagram) (a : Dart) : Option Dart :=
  D.adj (rotate a 1)

def Diagram.strandNext (D : Diagram) (a : Dart) : Option Dart :=
  D.adj (rotate a 2)

def Diagram.face (D : Diagram) (a : Dart) : List Dart :=
  orbit D.faceCorner a (4 * D.rows.length)

def Diagram.component (D : Diagram) (a : Dart) : List Dart :=
  orbit D.strandNext a (4 * D.rows.length)

/-- Local pairings expressed as a short symmetric list of dart pairs. -/
def paired (pairs : List (Dart × Dart)) (a : Dart) : Option Dart :=
  match pairs with
  | [] => none
  | (x, y) :: tail =>
      if a == x then some y else if a == y then some x else paired tail a

def checkRows (E : Diagram) (allowed : List Dart) (adj : Dart → Option Dart) : Bool :=
  E.darts == allowed && allowed.all (fun a => E.adj a == adj a)

/-- Follow one segment of the local smoothing, to the first outside dart. -/
def smoothingNext (D : Diagram) (pairs : List (Dart × Dart)) (current : Dart) :
    ℕ → Option Dart
  | 0 => none
  | n + 1 => (D.adj current).bind fun a =>
      match paired pairs a with
      | none => some a
      | some b => smoothingNext D pairs b n

def Diagram.smoothingIncludes (D : Diagram) (dead : List ℕ)
    (pairs : List (Dart × Dart)) (E : Diagram) : Bool :=
  let outside := D.darts.filter (fun a => !(dead.contains (vertex a)))
  checkRows E outside (fun a => smoothingNext D pairs a (2 * pairs.length + 1))

/-- A newly isolated circle is a closed component of the local smoothing.
On at most four boundary darts, identify it by the least dart in its orbit. -/
def closedSmoothCount (D : Diagram) (pairs : List (Dart × Dart)) : ℕ :=
  let boundary := pairs.flatMap (fun (a, b) => [a, b])
  (boundary.filter fun a =>
    let traverse : Dart → Option Dart := fun x => (D.adj x).bind (paired pairs)
    let visited := orbit traverse a (boundary.length + 1)
    (visited.length == boundary.length + 1) &&
      visited.all (fun b => a ≤ b) &&
      -- The two directions around a smoothed circle must be counted once.
      (paired pairs a).all (fun b => (orbit traverse b (boundary.length + 1)).all
        (fun c => a ≤ c))).length

def Diagram.checkRI (D E : Diagram) (a : Dart) : Bool :=
  let r := rotate a
  let pairs := [(r 2, r 3)]
  D.adj a == some (r 1) &&
    D.smoothingIncludes [vertex a] pairs E &&
    E.circles == D.circles + closedSmoothCount D pairs

def Diagram.checkRII (D E : Diagram) (a b : Dart) : Bool :=
  let r := rotate a
  let s := rotate b
  let pairs := [(r 2, s 2), (r 3, s 1)]
  vertex a != vertex b && a % 2 == b % 2 &&
    D.adj a == some b && D.adj (r 1) == some (s 3) &&
    D.smoothingIncludes [vertex a, vertex b] pairs E &&
    E.circles == D.circles + closedSmoothCount D pairs

def lookup (a : Dart) (data : List (Dart × Dart)) : Dart :=
  (data.lookup a).getD a

def triangleBoundary (a b c : Dart) : List (Dart × Dart) :=
  let r := rotate a
  let s := rotate b
  let t := rotate c
  [(t 3, a), (t 2, s 1), (r 3, b), (r 2, t 1), (s 3, c), (s 2, r 1)]

def Diagram.checkRIII (D E : Diagram) (a b c : Dart) : Bool :=
  let r := rotate a
  let s := rotate b
  let t := rotate c
  let relocate := triangleBoundary a b c
  let restore := relocate.map Prod.swap
  let inside := [(r 3, s 2), (s 3, t 2), (t 3, r 2)]
  vertex a != vertex b && vertex b != vertex c && vertex c != vertex a &&
    b % 2 == 0 && c % 2 == 1 &&
    D.faceCorner a == some b && D.faceCorner b == some c && D.faceCorner c == some a &&
    E.circles == D.circles &&
    checkRows E D.darts (fun x =>
      match paired inside x with
      | some y => some y
      | none => (D.adj (lookup x restore)).map (fun y => lookup y relocate))

def Diagram.checkRelabel (D E : Diagram) (image : List (Dart × Dart)) : Bool :=
  let target := D.darts.map (fun a => lookup a image)
  target.Nodup && target.all E.darts.contains && target.length == E.darts.length &&
    E.circles == D.circles &&
    D.darts.all (fun a =>
      let b := lookup a image
      a % 2 == b % 2 && lookup (rotate a 1) image == rotate b 1 &&
        (D.adj a).map (fun c => lookup c image) == E.adj b)

/-- Follow the other strand through crossings that disappear when an arc
is lifted above or below the rest of the diagram. -/
def skipArc (D : Diagram) (dead : List ℕ) (a : Dart) : ℕ → Option Dart
  | 0 => none
  | n + 1 => if dead.contains (vertex a) then
      (D.adj (rotate a 2)).bind (fun b => skipArc D dead b n)
    else some a

/-- Remove a simple all-over or all-under arc, leaving the remaining
projection and the two ordered endpoints of the removed arc. -/
def Diagram.eraseArc (D : Diagram) (over : Bool) (arc : List Dart) :
    Option (Dart × Dart × List (Dart × Option Dart)) := do
  let first ← arc.head?
  let last ← arc.getLast?
  let left ← D.adj first
  let right ← D.adj (rotate last 2)
  let dead := arc.map vertex
  if !(dead.Nodup && arc.all (fun a => D.darts.contains a && (a % 2 == 1) == over) &&
    (arc.zip arc.tail).all (fun (a, b) => D.strandNext a == some b) &&
      !dead.contains (vertex left) && !dead.contains (vertex right) && left != right) then
    none
  else
    let otherDarts := arc.flatMap (fun a => [rotate a 1, rotate a 3])
    let outside := D.darts.filter (fun a => !dead.contains (vertex a))
    let remaining := outside.map (fun a => (a,
      if a == left || a == right then none else
        (D.adj a).bind (fun b => skipArc D dead b (arc.length + 1))))
    -- Every remaining strand through a lifted crossing reaches an outside
    -- dart. This rules out losing a component supported only there.
    if otherDarts.all (fun a => (skipArc D dead a (arc.length + 1)).isSome) then
      some (left, right, remaining)
    else none

def Diagram.checkArc (D E : Diagram) (over : Bool) (old new : List Dart) : Bool :=
  D.circles == E.circles &&
    match D.eraseArc over old, E.eraseArc over new with
    | some x, some y => x == y
    | _, _ => false

inductive Move where
  | ri (dart : Dart)
  | rii (first second : Dart)
  | riii (first second third : Dart)
  | relabel (image : List (Dart × Dart))
  | arc (over : Bool) (old new : List Dart)
  deriving DecidableEq, Repr

def checkMove (D E : Diagram) : Move → Bool
  | .ri a => D.checkRI E a
  | .rii a b => D.checkRII E a b
  | .riii a b c => D.checkRIII E a b c
  | .relabel p => D.checkRelabel E p
  | .arc over old new => D.checkArc E over old new

abbrev Trace := List (Move × Diagram)

def Trace.endpoint (D : Diagram) : Trace → Diagram
  | [] => D
  | (_, E) :: rest => Trace.endpoint E rest

def Trace.check (D : Diagram) : Trace → Bool
  | [] => true
  | (move, E) :: rest => E.valid && checkMove D E move && Trace.check E rest

/-- An accepted trace starts at a valid diagram and passes the corresponding
local check at every step. -/
def CertifiedMoves (D : Diagram) (trace : Trace) : Prop :=
  D.valid && Trace.check D trace

instance (D : Diagram) (trace : Trace) : Decidable (CertifiedMoves D trace) :=
  inferInstanceAs (Decidable ((D.valid && Trace.check D trace) = true))

/-- Transport an anchor by the unchanged strands, the marked boundary
of a type III move, or the checked map of a relabeling. -/
def Move.transportAnchor (a : Dart) : Move → Option Dart
  | .ri b => if vertex a == vertex b then none else some a
  | .rii b c => if [vertex b, vertex c].contains (vertex a) then none else some a
  | .riii b c d =>
      if [vertex b, vertex c, vertex d].contains (vertex a) then
        let border := triangleBoundary b c d
        (border.lookup a).or (border.lookup (rotate a 2))
      else some a
  | .relabel image => some (lookup a image)
  | .arc _ old new =>
      if ((old ++ new).map vertex).contains (vertex a) then none else some a

def Trace.anchor (D : Diagram) (mark : Dart) : Trace → Option Dart
  | [] => if D.darts.contains mark then some mark else none
  | (move, E) :: rest =>
      if D.darts.contains mark then
        (move.transportAnchor mark).bind (fun mark' => Trace.anchor E mark' rest)
      else none

/-- The certified moves generate an equivalence in any interpretation that
respects the indicated local moves. -/
theorem CertifiedMoves.sound {α : Type*} (interpret : Diagram → α)
    (localMove : ∀ D E move, D.valid = true → E.valid = true →
      checkMove D E move = true → interpret D = interpret E)
    {D : Diagram} {trace : Trace} (h : CertifiedMoves D trace) :
    interpret D = interpret (Trace.endpoint D trace) := by
  induction trace generalizing D with
  | nil => rfl
  | cons step rest ih =>
    rcases step with ⟨move, E⟩
    simp only [CertifiedMoves, Trace.check, Bool.and_eq_true] at h
    exact (localMove D E move h.1 h.2.1.1 h.2.1.2).trans
      (ih (D := E) (by simpa [CertifiedMoves] using And.intro h.2.1.1 h.2.2))

/-- For an interpretation of marked diagrams, the same checked trace
respects the component of a transported anchor. -/
theorem CertifiedMoves.markedSound {α : Type*} (interpret : Diagram → Dart → α)
    (localMove : ∀ D E move a b, D.valid = true → E.valid = true →
      checkMove D E move = true → D.darts.contains a = true →
      E.darts.contains b = true →
      move.transportAnchor a = some b → interpret D a = interpret E b)
    {D : Diagram} {trace : Trace} {a b : Dart} (h : CertifiedMoves D trace)
    (ha : Trace.anchor D a trace = some b) :
    interpret D a = interpret (Trace.endpoint D trace) b := by
  induction trace generalizing D a b with
  | nil =>
    by_cases hD : D.darts.contains a = true
    · have hab : a = b := by
        simpa only [Trace.anchor, hD, if_true, Option.some.injEq] using ha
      subst b
      rfl
    · simp only [Trace.anchor, hD, if_false, reduceCtorEq] at ha
  | cons step rest ih =>
    rcases step with ⟨move, E⟩
    simp only [CertifiedMoves, Trace.check, Bool.and_eq_true] at h
    by_cases hD : D.darts.contains a = true
    · cases hm : move.transportAnchor a with
      | none => simp only [Trace.anchor, hD, if_true, hm, Option.bind_none, reduceCtorEq] at ha
      | some c =>
        have ht : Trace.anchor E c rest = some b := by
          simpa only [Trace.anchor, hD, if_true, hm, Option.bind_some] using ha
        have hc : E.darts.contains c = true := by
          by_contra hnot
          cases rest <;> simp only [Trace.anchor, hnot, if_false, reduceCtorEq] at ht
        exact (localMove D E move a c h.1 h.2.1.1 h.2.1.2 hD hc hm).trans
          (ih (D := E) (by simpa [CertifiedMoves] using And.intro h.2.1.1 h.2.2) ht)
    · simp only [Trace.anchor, hD, if_false, reduceCtorEq] at ha

/-- A two-edge cut. The directed darts specify the dual corners on one
side. The check requires distinct common faces and a cut on a single
link component, away from the marked component when present. It checks
the two reclosures against the explicitly given union of the outputs. -/
def Diagram.checkSplit (D : Diagram) (a b : Dart) (mark : Option Dart)
    (left right : Diagram) : Bool :=
  match D.adj a, D.adj b with
  | some x, some y =>
    let reroute := [(x, b), (a, y)]
    let component := D.component a ++ D.component (rotate a 2)
    let avoid := mark.all (fun c =>
      D.darts.contains c && right.darts.contains c &&
        ([a, b, x, y].all (fun d =>
          !(D.component c).contains d && !(D.component (rotate c 2)).contains d)))
    let sides :=
      (left.darts.contains x && left.darts.contains b &&
        right.darts.contains a && right.darts.contains y) ||
      (right.darts.contains x && right.darts.contains b &&
        left.darts.contains a && left.darts.contains y)
    a != b && a != y && sides &&
      !(D.face a).contains x && (D.face a).contains b && (D.face x).contains y &&
      (component.contains b || component.contains (rotate b 2)) && avoid &&
      left.valid && right.valid &&
      left.circles + right.circles == D.circles &&
      left.darts.all (fun c => !(right.darts.contains c)) &&
      D.darts.all (fun c =>
        let new := (paired reroute c).or (D.adj c)
        (left.darts.contains c && left.adj c == new) ||
          (right.darts.contains c && right.adj c == new)) &&
      (left.darts ++ right.darts).all D.darts.contains
  | _, _ => false

end Trefoil.Section2DiagramMoves
