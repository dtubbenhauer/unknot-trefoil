import Trefoil.Section2DiagramMoves

/-!
# Crossing switches of the augmented movie

A crossing switch acts on the planar projection by the identity and
exchanges over and under at one vertex. A dart relabeling permits
independent changes of port numbering between the recorded stages.
-/

namespace Trefoil.Section2Switches

open Section2DiagramMoves

/-- The complete dart orbit, independent of its traversal direction. -/
def unorientedComponent (D : Diagram) (a : Dart) : List Dart :=
  D.component a ++ D.component (rotate a 2)

/-- The diagram and axis conditions for one switch. The crossing is
specified in the source numbering. The dart permutation preserves
cyclic order and all edges, and reverses parity only at that crossing. -/
def checkSwitch (D E : Diagram) (crossing : ℕ) (sourceAxis targetAxis : Option Dart)
    (image : List (Dart × Dart)) : Bool :=
  let vertices := D.darts
  let map := fun a => lookup a image
  let target := vertices.map map
  let markAgrees :=
    match sourceAxis, targetAxis with
    | none, none => true
    | some a, some b =>
        vertices.contains a && E.darts.contains b &&
          (unorientedComponent E b).contains (map a) &&
          (unorientedComponent D a).all (fun d => vertex d != crossing)
    | _, _ => false
  D.valid && E.valid && D.active crossing &&
    target.Nodup && target.all E.darts.contains && target.length == E.darts.length &&
    D.circles == E.circles && markAgrees &&
    vertices.all (fun a =>
      let b := map a
      (if vertex a == crossing then a % 2 != b % 2 else a % 2 == b % 2) &&
        map (rotate a 1) == rotate b 1 &&
        (D.adj a).map map == E.adj b)

end Trefoil.Section2Switches
