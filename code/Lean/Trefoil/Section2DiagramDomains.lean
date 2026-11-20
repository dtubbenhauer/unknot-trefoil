import Trefoil.Section2DiagramMoves

/-!
# Domains of the Section 2 diagram operations

For a valid half-edge table, rotating a crossing and reversing a diagram
edge give its orientable ribbon graph. The face count and projection
component count give the genus of the capped ribbon surface. The unoriented
link-component count is half the number of oriented strand cycles, plus
the circles stored separately in the diagram.
-/

namespace Trefoil.Section2DiagramMoves

private def visitDarts (next : Dart → Option Dart) : ℕ → Dart → List Dart → List Dart
  | 0, _, seen => seen
  | n + 1, a, seen =>
      if seen.contains a then seen
      else
        let seen' := a :: seen
        match next a with
        | none => seen'
        | some b => visitDarts next n b seen'

private def cycleCount (darts : List Dart) (next : Dart → Option Dart) : ℕ :=
  (darts.foldl (fun (count, seen) a =>
    if seen.contains a then (count, seen)
    else (count + 1, visitDarts next darts.length a seen)) (0, ([] : List Dart))).1

private def Diagram.activeVertices (D : Diagram) : List ℕ :=
  (List.range D.rows.length).filter D.active

private def Diagram.neighbors (D : Diagram) (a : ℕ) : List ℕ :=
  ((D.row a).getD []).map vertex

private def Diagram.visitShadow (D : Diagram) : ℕ → List ℕ → List ℕ → List ℕ
  | 0, _, seen => seen
  | _ + 1, [], seen => seen
  | n + 1, a :: todo, seen =>
      if seen.contains a then D.visitShadow n todo seen
      else D.visitShadow n (D.neighbors a ++ todo) (a :: seen)

/-- Connected components of the projection graph that contain crossings. -/
def Diagram.numShadowComponents (D : Diagram) : ℕ :=
  let vertices := D.activeVertices
  (vertices.foldl (fun (count, seen) a =>
    if seen.contains a then (count, seen)
    else (count + 1, D.visitShadow (4 * vertices.length + 1) [a] seen))
    (0, ([] : List ℕ))).1

/-- Faces of the embedded rotation system, before adding isolated circles. -/
def Diagram.numFaces (D : Diagram) : ℕ :=
  cycleCount D.darts D.faceCorner

/-- Each rotation-system component is planar. The discrete equality is
`vertices + faces = edges + 2 * components`, with `edges = 2 * vertices`.
An isolated circle is always planar and has no darts. -/
def Diagram.planar (D : Diagram) : Bool :=
  let vertices := D.activeVertices.length
  D.valid && vertices + D.numFaces == 2 * vertices + 2 * D.numShadowComponents

/-- Number of link components, including circles with no crossings. -/
def Diagram.numComponents (D : Diagram) : ℕ :=
  D.circles + cycleCount D.darts D.strandNext / 2

/-- A diagram representing a knot has one link component. -/
def Diagram.knotDiagram (D : Diagram) : Bool :=
  D.planar && D.numComponents == 1

/-- The marked component is an unknotted projection component. Its
crossing list visits each crossing at most once along this strand. -/
def Diagram.markedDiagram (D : Diagram) (mark : Dart) : Bool :=
  D.planar && D.numComponents == 2 && D.darts.contains mark &&
    ((visitDarts D.strandNext D.darts.length mark []).map vertex).Nodup

/-- All states of an unmarked trace lie in the planar domain. -/
def Trace.planar (D : Diagram) (trace : Trace) : Bool :=
  D.planar && trace.all (fun (_, E) => E.planar)

/-- All states of a trace are planar with the given number of link components. -/
def Trace.withComponents (D : Diagram) (n : ℕ) (trace : Trace) : Bool :=
  let check := fun E : Diagram => E.planar && E.numComponents == n
  check D && trace.all (fun (_, E) => check E)

/-- All states of a knot trace have exactly one planar link component. -/
def Trace.knot (D : Diagram) (trace : Trace) : Bool :=
  D.knotDiagram && trace.all (fun (_, E) => E.knotDiagram)

/-- All states of an anchor-preserving trace lie in the marked domain. -/
def Trace.marked (D : Diagram) (mark : Dart) : Trace → Bool
  | [] => D.markedDiagram mark
  | (move, E) :: rest => D.markedDiagram mark &&
    match move.transportAnchor mark with
    | none => false
    | some mark' => Trace.marked E mark' rest

/-- In a trace all of whose states are planar, use a local move theorem
restricted to planar diagrams. -/
theorem CertifiedMoves.planarSound {α : Type*} (interpret : Diagram → α)
    (localMove : ∀ D E move, D.planar = true → E.planar = true →
      checkMove D E move = true → interpret D = interpret E)
    {D : Diagram} {trace : Trace} (h : CertifiedMoves D trace)
    (hp : Trace.planar D trace = true) :
    interpret D = interpret (Trace.endpoint D trace) := by
  induction trace generalizing D with
  | nil => rfl
  | cons step rest ih =>
    rcases step with ⟨move, E⟩
    simp only [CertifiedMoves, Trace.check, Bool.and_eq_true] at h
    simp only [Trace.planar, List.all_cons, Bool.and_eq_true] at hp
    exact (localMove D E move hp.1 hp.2.1 h.2.1.2).trans
      (ih (D := E) (by simpa [CertifiedMoves] using And.intro h.2.1.1 h.2.2)
        (by simpa [Trace.planar] using And.intro hp.2.1 hp.2.2))

/-- A generic move theorem on knots applies throughout the full knot trace. -/
theorem CertifiedMoves.knotSound {α : Type*} (interpret : Diagram → α)
    (localMove : ∀ D E move, D.knotDiagram = true → E.knotDiagram = true →
      checkMove D E move = true → interpret D = interpret E)
    {D : Diagram} {trace : Trace} (h : CertifiedMoves D trace)
    (hp : Trace.knot D trace = true) :
    interpret D = interpret (Trace.endpoint D trace) := by
  induction trace generalizing D with
  | nil => rfl
  | cons step rest ih =>
    rcases step with ⟨move, E⟩
    simp only [CertifiedMoves, Trace.check, Bool.and_eq_true] at h
    simp only [Trace.knot, List.all_cons, Bool.and_eq_true] at hp
    exact (localMove D E move hp.1 hp.2.1 h.2.1.2).trans
      (ih (D := E) (by simpa [CertifiedMoves] using And.intro h.2.1.1 h.2.2)
        (by simpa [Trace.knot] using And.intro hp.2.1 hp.2.2))

/-- Moving an anchor through a checked trace in the marked planar domain
preserves its geometric interpretation and its distinguished component. -/
theorem CertifiedMoves.markedPlanarSound {α : Type*} (interpret : Diagram → Dart → α)
    (localMove : ∀ D E move a b, D.markedDiagram a = true → E.markedDiagram b = true →
      checkMove D E move = true →
      move.transportAnchor a = some b → interpret D a = interpret E b)
    {D : Diagram} {trace : Trace} {a b : Dart} (h : CertifiedMoves D trace)
    (ha : Trace.anchor D a trace = some b) (hm : Trace.marked D a trace = true) :
    interpret D a = interpret (Trace.endpoint D trace) b := by
  induction trace generalizing D a b with
  | nil =>
    by_cases hd : D.darts.contains a = true
    · have hEq : a = b := by
        simpa only [Trace.anchor, hd, if_true, Option.some.injEq] using ha
      subst b
      rfl
    · simp only [Trace.anchor, hd, if_false, reduceCtorEq] at ha
  | cons step rest ih =>
    rcases step with ⟨move, E⟩
    simp only [CertifiedMoves, Trace.check, Bool.and_eq_true] at h
    cases hn : move.transportAnchor a with
    | none => simp [Trace.marked, hn] at hm
    | some c =>
      have hp : D.markedDiagram a = true ∧ Trace.marked E c rest = true := by
        simpa only [Trace.marked, hn, Bool.and_eq_true] using hm
      have hq : E.markedDiagram c = true := by
        cases rest <;> simp [Trace.marked] at hp
        · exact hp.2
        · exact hp.2.1
      have hd : D.darts.contains a = true := by
        have hd' := hp.1
        simp only [Diagram.markedDiagram, Bool.and_eq_true, decide_eq_true_eq] at hd'
        exact hd'.1.2
      have hrest : Trace.anchor E c rest = some b := by
        simpa only [Trace.anchor, hd, if_true, hn, Option.bind_some] using ha
      exact (localMove D E move a c hp.1 hq h.2.1.2 hn).trans
        (ih (D := E) (by simpa [CertifiedMoves] using And.intro h.2.1.1 h.2.2) hrest hp.2)

end Trefoil.Section2DiagramMoves
