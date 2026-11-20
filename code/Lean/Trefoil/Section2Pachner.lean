import Trefoil.Section2Triangulations
import Mathlib.Data.List.Perm.Basic

/-!
# Certifying a bistellar replacement in a triangulation

The local vertex labels are 0, 1, 2 for the equatorial face and 3, 4 for its
two apices. The checker compares the actual six boundary triangles with their
face pairings on both sides, including pairings to other cavity triangles.
This handles generalized triangulations with repeated vertices or edges.

The output is a finite combinatorial replacement. Its geometric
interpretation uses the bistellar-move theorem with the displayed labeled
bipyramid.
-/

namespace Trefoil.Section2Pachner

open Section2Triangulations

abbrev Charts := Array (Array ℕ)

/-- A local chart lists the five-vertex model label of each native vertex of
a participating tetrahedron. An empty chart marks a surviving tetrahedron.
The two arrays of optional indices identify those surviving tetrahedra. -/
structure CavityWitness where
  beforeCharts : Charts
  afterCharts : Charts
  oldToNew : Array (Option ℕ)
  newToOld : Array (Option ℕ)
  deriving Repr

inductive Side where
  | two
  | three
  deriving DecidableEq, Repr

/-- Vertex sets of the two subdivisions of a triangular bipyramid. -/
def Side.simplices : Side → List (List ℕ)
  | .two => [[0, 1, 2, 3], [0, 1, 2, 4]]
  | .three => [[0, 1, 3, 4], [0, 2, 3, 4], [1, 2, 3, 4]]

def Side.other : Side → Side
  | .two => .three
  | .three => .two

def boundaryTriangles : List (List ℕ) :=
  [[0, 1, 3], [0, 1, 4], [0, 2, 3], [0, 2, 4], [1, 2, 3], [1, 2, 4]]

def chart (charts : Charts) (t : ℕ) : Array ℕ :=
  charts.getD t #[]

def survives (charts : Charts) (t : ℕ) : Bool :=
  (chart charts t).isEmpty

def localLabel (charts : Charts) (t v : ℕ) : ℕ :=
  (chart charts t).getD v 0

/-- A structural sort lets the trusted evaluator check the witness without
unfolding any well-founded termination proofs. -/
def insertBy {α : Type} (le : α → α → Bool) (x : α) : List α → List α
  | [] => [x]
  | y :: ys => if le x y then x :: y :: ys else y :: insertBy le x ys

def sortBy {α : Type} (le : α → α → Bool) : List α → List α
  | [] => []
  | x :: xs => insertBy le x (sortBy le xs)

theorem insertBy_perm {α : Type} (le : α → α → Bool) (x : α) (xs : List α) :
    (insertBy le x xs).Perm (x :: xs) := by
  induction xs with
  | nil => exact .refl _
  | cons y ys ih =>
    simp only [insertBy]
    split
    · exact .refl _
    · exact (List.Perm.cons y ih).trans (List.Perm.swap x y ys)

theorem sortBy_perm {α : Type} (le : α → α → Bool) (xs : List α) :
    (sortBy le xs).Perm xs := by
  induction xs with
  | nil => exact .nil
  | cons x xs ih => exact (insertBy_perm ..).trans (.cons x ih)

def sortedSites (charts : Charts) : List (List ℕ) :=
  charts.toList.filterMap fun x =>
    if x.isEmpty then none else some (sortBy (· ≤ ·) x.toList)

/-- The labeled tetrahedra are exactly the chosen subdivision. -/
def HasSite (S : Triangulation) (charts : Charts) (side : Side) : Prop :=
  charts.size = S.size ∧ (sortedSites charts).Perm side.simplices

private def chartKey (vertices : List ℕ) : ℕ := (vertices.map (2 ^ ·)).sum

def checkSite (S : Triangulation) (charts : Charts) (side : Side) : Bool :=
  decide (charts.size = S.size) &&
    decide (sortBy (fun a b => chartKey a ≤ chartKey b) (sortedSites charts) =
      sortBy (fun a b => chartKey a ≤ chartKey b) side.simplices)

theorem checkSite_sound {S : Triangulation} {charts : Charts} {side : Side}
    (h : checkSite S charts side = true) : HasSite S charts side := by
  simp only [checkSite, Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1, (sortBy_perm _ _).symm.trans (h.2.symm ▸ sortBy_perm _ _)⟩

def SourceSurvivor (T : Triangulation) (w : CavityWitness) (t : ℕ) : Prop :=
  match w.oldToNew.getD t none with
  | none => survives w.beforeCharts t = false
  | some u => survives w.beforeCharts t = true ∧ u < T.size ∧
      survives w.afterCharts u = true ∧ w.newToOld.getD u none = some t

def checkSourceSurvivor (T : Triangulation) (w : CavityWitness) (t : ℕ) : Bool :=
  match w.oldToNew.getD t none with
  | none => !survives w.beforeCharts t
  | some u => survives w.beforeCharts t && decide (u < T.size) &&
      survives w.afterCharts u && decide (w.newToOld.getD u none = some t)

theorem checkSourceSurvivor_true {T : Triangulation} {w : CavityWitness} {t : ℕ} :
    checkSourceSurvivor T w t = true ↔ SourceSurvivor T w t := by
  cases h : w.oldToNew.getD t none <;>
    simp only [checkSourceSurvivor, SourceSurvivor, h, Bool.not_eq_true',
      Bool.and_eq_true, decide_eq_true_eq, and_assoc]

def TargetSurvivor (S : Triangulation) (w : CavityWitness) (u : ℕ) : Prop :=
  match w.newToOld.getD u none with
  | none => survives w.afterCharts u = false
  | some t => survives w.afterCharts u = true ∧ t < S.size ∧
      survives w.beforeCharts t = true ∧ w.oldToNew.getD t none = some u

def checkTargetSurvivor (S : Triangulation) (w : CavityWitness) (u : ℕ) : Bool :=
  match w.newToOld.getD u none with
  | none => !survives w.afterCharts u
  | some t => survives w.afterCharts u && decide (t < S.size) &&
      survives w.beforeCharts t && decide (w.oldToNew.getD t none = some u)

theorem checkTargetSurvivor_true {S : Triangulation} {w : CavityWitness} {u : ℕ} :
    checkTargetSurvivor S w u = true ↔ TargetSurvivor S w u := by
  cases h : w.newToOld.getD u none <;>
    simp only [checkTargetSurvivor, TargetSurvivor, h, Bool.not_eq_true',
      Bool.and_eq_true, decide_eq_true_eq, and_assoc]

/-- On each side, every surviving tetrahedron has a unique corresponding
tetrahedron on the other side. Its four native vertex labels are unchanged. -/
def SurvivingTetrahedra (S T : Triangulation) (w : CavityWitness) : Prop :=
  w.oldToNew.size = S.size ∧ w.newToOld.size = T.size ∧
  (∀ t : Fin S.size, SourceSurvivor T w t) ∧
  ∀ u : Fin T.size, TargetSurvivor S w u

private def allP (n : ℕ) (f : Fin n → Bool) : Bool := (List.finRange n).all f

private theorem allP_true {n : ℕ} {f : Fin n → Bool} :
    allP n f = true ↔ ∀ i, f i = true := by
  simp [allP, List.mem_finRange]

def checkSurvivors (S T : Triangulation) (w : CavityWitness) : Bool :=
  decide (w.oldToNew.size = S.size) && decide (w.newToOld.size = T.size) &&
    allP S.size (fun t => checkSourceSurvivor T w t) &&
    allP T.size (fun t => checkTargetSurvivor S w t)

theorem checkSurvivors_sound {S T : Triangulation} {w : CavityWitness}
    (h : checkSurvivors S T w = true) : SurvivingTetrahedra S T w := by
  simpa only [checkSurvivors, SurvivingTetrahedra, Bool.and_eq_true, allP_true,
    decide_eq_true_eq, checkSourceSurvivor_true, checkTargetSurvivor_true, and_assoc] using h

def faceVertices (f : ℕ) : List ℕ :=
  [0, 1, 2, 3].filter (· != f)

def localFace (charts : Charts) (t f : ℕ) : List ℕ :=
  sortBy (· ≤ ·) ((faceVertices f).map (localLabel charts t))

def interiorFace (charts : Charts) (t f : ℕ) : Bool :=
  !survives charts t && !boundaryTriangles.contains (localFace charts t f)

/-- Interior face identifications must respect the common labels of the
model, and pair distinct tetrahedra inside the same cavity. -/
def InternalGluings (S : Triangulation) (charts : Charts) : Prop :=
  ∀ (t : Fin S.size) (f : Vertex), interiorFace charts t f = true →
    let a := face S t f
    a.tet ≠ t.val ∧ interiorFace charts a.tet (vertex a f) = true ∧
    ∀ v : Vertex, v ≠ f →
      localLabel charts t v = localLabel charts a.tet (vertex a v)

def checkInternal (S : Triangulation) (charts : Charts) : Bool :=
  allP S.size fun t => allP 4 fun f =>
    let a := face S t f
    !interiorFace charts t f || (decide (a.tet ≠ t.val) &&
      interiorFace charts a.tet (vertex a f) &&
      allP 4 (fun v => decide (v ≠ f →
        localLabel charts t v = localLabel charts a.tet (vertex a v))))

theorem checkInternal_sound {S : Triangulation} {charts : Charts}
    (h : checkInternal S charts = true) : InternalGluings S charts := by
  intro t f hf
  have h' := (allP_true.mp (allP_true.mp h t)) f
  simpa only [hf, Bool.not_true, Bool.false_or, Bool.and_eq_true,
    allP_true, decide_eq_true_eq, and_assoc] using h'

/-- Compare the orientation of a native tetrahedron with the ordered
bipyramid. Use the affine model with vertices
`(0,0,0),(3,0,0),(0,3,0),(1,1,3),(1,1,-3)`. -/
def sitePolarity (labels : Array ℕ) : Bool :=
  let odd := oddVertices ⟨0, labels⟩
  let sorted := sortBy (· ≤ ·) labels.toList
  let modelOdd := [[0, 1, 2, 4], [0, 1, 3, 4], [1, 2, 3, 4]].contains sorted
  odd != modelOdd

def polarityList (w : CavityWitness) : List Bool :=
  ((w.beforeCharts.toList ++ w.afterCharts.toList).filter (!·.isEmpty)).map sitePolarity

/-- Both subdivisions induce the same relative orientation. -/
def SamePolarity (w : CavityWitness) : Prop :=
  ∃ p : Bool, ∀ q ∈ polarityList w, q = p

def checkPolarity (w : CavityWitness) : Bool :=
  (polarityList w).all (· == true) || (polarityList w).all (· == false)

theorem checkPolarity_sound {w : CavityWitness} (h : checkPolarity w = true) :
    SamePolarity w := by
  simp only [checkPolarity, Bool.or_eq_true] at h
  rcases h with ht | hf
  · exact ⟨true, fun _ hq => by simpa using List.all_eq_true.mp ht _ hq⟩
  · exact ⟨false, fun _ hq => by simpa using List.all_eq_true.mp hf _ hq⟩

/-- Name a noninterior face by its old surviving tetrahedron index, or by
its three common bipyramid vertex labels. -/
inductive FaceName where
  | outside (oldTet face : ℕ)
  | boundary (vertices : List ℕ)
  deriving DecidableEq, Repr

def faceName (charts : Charts) (oldIndex : ℕ → ℕ) (t f : ℕ) : FaceName :=
  if survives charts t then .outside (oldIndex t) f else .boundary (localFace charts t f)

def faceVertexLabel (charts : Charts) (t v : ℕ) : ℕ :=
  if survives charts t then v else localLabel charts t v

/-- One complete oriented boundary arrow, including all three vertex
images. Opposite vertices play no role in a gluing along a face. -/
structure FaceArrow where
  source : FaceName
  target : FaceName
  vertexPairs : List (ℕ × ℕ)
  deriving DecidableEq, Repr

def faceArrow (S : Triangulation) (charts : Charts) (oldIndex : ℕ → ℕ)
    (t f : ℕ) : FaceArrow :=
  let a := face S t f
  let pairs := (faceVertices f).map fun v =>
    (faceVertexLabel charts t v, faceVertexLabel charts a.tet (vertex a v))
  ⟨faceName charts oldIndex t f, faceName charts oldIndex a.tet (vertex a f),
    sortBy (fun p q => p.1 ≤ q.1) pairs⟩

def boundaryPosition (charts : Charts) (sites : List ℕ) (vertices : List ℕ) :
    Option (ℕ × ℕ) :=
  sites.findSome? fun u =>
    ((List.range 4).find? fun v => localFace charts u v == vertices).map fun v => (u, v)

def correspondingFace (S T : Charts) (kept : Array (Option ℕ))
    (targetSites : List ℕ) (t f : ℕ) : Option (ℕ × ℕ) :=
  if survives S t then (kept.getD t none).map fun u => (u, f)
  else boundaryPosition T targetSites (localFace S t f)

private def matchedFaces (n m : ℕ) (S T : Charts) (kept : Array (Option ℕ))
    (compare : ℕ → ℕ → ℕ → ℕ → Bool) : Bool :=
  let targetSites := (List.range T.size).filter fun t => !survives T t
  allP n fun t => allP 4 fun f =>
    if interiorFace S t f then true
    else match correspondingFace S T kept targetSites t f with
      | none => false
      | some (u, g) => decide (u < m) && decide (g < 4) &&
          !interiorFace T u g && compare t f u g

/-- Every exterior face has a mate in the other subdivision with the
indicated relation. We check this in both directions. -/
def EveryExteriorFace (n m : ℕ) (S T : Charts)
    (agree : ℕ → ℕ → ℕ → ℕ → Prop) : Prop :=
  ∀ (t : Fin n) (f : Vertex), interiorFace S t f = false →
    ∃ (u : Fin m) (g : Vertex), interiorFace T u g = false ∧ agree t f u g

private theorem matchedFaces_sound {n m : ℕ} {S T : Charts}
    {kept : Array (Option ℕ)} {compare : ℕ → ℕ → ℕ → ℕ → Bool}
    (h : matchedFaces n m S T kept compare = true) :
    EveryExteriorFace n m S T (fun t f u g => compare t f u g = true) := by
  intro t f hf
  have h' := (allP_true.mp (allP_true.mp h t)) f
  simp only [hf, Bool.false_eq_true, ↓reduceIte] at h'
  split at h'
  · contradiction
  · rename_i u g _
    simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at h'
    exact ⟨⟨u, h'.1.1.1⟩, ⟨g, h'.1.1.2⟩, h'.1.2, h'.2⟩

private def outsideId (w : CavityWitness) (t : ℕ) : ℕ :=
  (w.newToOld.getD t none).getD 0

def ExternalAgreement (S T : Triangulation) (w : CavityWitness) : Prop :=
  let a := faceArrow S w.beforeCharts id
  let b := faceArrow T w.afterCharts (outsideId w)
  EveryExteriorFace S.size T.size w.beforeCharts w.afterCharts
    (fun t f u g => a t f = b u g) ∧
  EveryExteriorFace T.size S.size w.afterCharts w.beforeCharts
    (fun u g t f => b u g = a t f)

def checkExternal (S T : Triangulation) (w : CavityWitness) : Bool :=
  let a := faceArrow S w.beforeCharts id
  let b := faceArrow T w.afterCharts (outsideId w)
  matchedFaces S.size T.size w.beforeCharts w.afterCharts w.oldToNew
    (fun t f u g => decide (a t f = b u g)) &&
  matchedFaces T.size S.size w.afterCharts w.beforeCharts w.newToOld
    (fun u g t f => decide (b u g = a t f))

theorem checkExternal_sound {S T : Triangulation} {w : CavityWitness}
    (h : checkExternal S T w = true) : ExternalAgreement S T w := by
  simp only [checkExternal, Bool.and_eq_true] at h
  have h₁ := matchedFaces_sound h.1
  have h₂ := matchedFaces_sound h.2
  simpa only [ExternalAgreement, EveryExteriorFace, decide_eq_true_eq] using And.intro h₁ h₂

/-- All local charts, interior face relations, and remaining face gluings
are checked for the same bistellar replacement. -/
structure CavityReplacement (S T : Triangulation) (w : CavityWitness) (side : Side) : Prop where
  sourceValid : Valid S
  targetValid : Valid T
  beforeSite : HasSite S w.beforeCharts side
  afterSite : HasSite T w.afterCharts side.other
  retained : SurvivingTetrahedra S T w
  beforeInternal : InternalGluings S w.beforeCharts
  afterInternal : InternalGluings T w.afterCharts
  external : ExternalAgreement S T w
  polarity : SamePolarity w

def checkMove (S T : Triangulation) (w : CavityWitness) (side : Side) : Bool :=
  checkTriangulation S && checkTriangulation T &&
  checkSite S w.beforeCharts side && checkSite T w.afterCharts side.other &&
  checkSurvivors S T w && checkInternal S w.beforeCharts && checkInternal T w.afterCharts &&
  checkExternal S T w && checkPolarity w

theorem checkMove_sound {S T : Triangulation} {w : CavityWitness} {side : Side}
    (h : checkMove S T w side = true) : CavityReplacement S T w side := by
  simp only [checkMove, Bool.and_eq_true] at h
  rcases h with ⟨⟨⟨⟨⟨⟨⟨⟨hs, ht⟩, hb⟩, ha⟩, hr⟩, hbi⟩, hai⟩, he⟩, hp⟩
  exact ⟨checkTriangulation_sound hs, checkTriangulation_sound ht, checkSite_sound hb, checkSite_sound ha,
    checkSurvivors_sound hr, checkInternal_sound hbi, checkInternal_sound hai,
    checkExternal_sound he, checkPolarity_sound hp⟩

/-- State of a triangulation with its meridian and longitude cycles. -/
structure MarkedState where
  triangulation : Triangulation
  marking : CuspMarking
  deriving Repr

/-- For every vertex of every exterior face, compare the labeled cusp and
the two signed normal-curve fluxes. The three rows are sorted by vertex,
using native labels outside the cavity and bipyramid labels on its boundary. -/
structure CuspCorner where
  vertexLabel : ℕ
  cuspLabel : ℕ
  meridian : ℤ
  longitude : ℤ
  deriving DecidableEq, Repr

structure PeripheralFace where
  face : FaceName
  corners : List CuspCorner
  deriving DecidableEq, Repr

def peripheralFace (S : MarkedState) (charts : Charts) (oldIndex : ℕ → ℕ)
    (t f : ℕ) : PeripheralFace :=
  let rows := (faceVertices f).map fun v => CuspCorner.mk
    (faceVertexLabel charts t v) (cusp S.marking t v)
    (entry S.marking.meridian t v f) (entry S.marking.longitude t v f)
  ⟨faceName charts oldIndex t f, sortBy (fun x y => x.vertexLabel ≤ y.vertexLabel) rows⟩

/-- The cusp cycles have unchanged flux on each exterior seam. On an
individual model corner of the bipyramid the two normal curves are
chains in a disk with the same boundary flux. -/
def SameSeamFlux (S T : MarkedState) (w : CavityWitness) : Prop :=
  let a := peripheralFace S w.beforeCharts id
  let b := peripheralFace T w.afterCharts (outsideId w)
  S.marking.cuspCount = T.marking.cuspCount ∧
  EveryExteriorFace S.triangulation.size T.triangulation.size w.beforeCharts w.afterCharts
    (fun t f u g => a t f = b u g) ∧
  EveryExteriorFace T.triangulation.size S.triangulation.size w.afterCharts w.beforeCharts
    (fun u g t f => b u g = a t f)

def checkSeamFlux (S T : MarkedState) (w : CavityWitness) : Bool :=
  let a := peripheralFace S w.beforeCharts id
  let b := peripheralFace T w.afterCharts (outsideId w)
  decide (S.marking.cuspCount = T.marking.cuspCount) &&
  matchedFaces S.triangulation.size T.triangulation.size w.beforeCharts w.afterCharts w.oldToNew
    (fun t f u g => decide (a t f = b u g)) &&
  matchedFaces T.triangulation.size S.triangulation.size w.afterCharts w.beforeCharts w.newToOld
    (fun u g t f => decide (b u g = a t f))

theorem checkSeamFlux_sound {S T : MarkedState} {w : CavityWitness}
    (h : checkSeamFlux S T w = true) : SameSeamFlux S T w := by
  simp only [checkSeamFlux, Bool.and_eq_true, decide_eq_true_eq] at h
  have h₁ := matchedFaces_sound h.1.2
  have h₂ := matchedFaces_sound h.2
  have checked := And.intro h.1.1 (And.intro h₁ h₂)
  simpa only [SameSeamFlux, EveryExteriorFace, decide_eq_true_eq] using checked

/-- A bistellar replacement with the same marked peripheral homology
classes, relative to the usual homology interpretation of the corner disks. -/
structure MarkedReplacement (S T : MarkedState) (w : CavityWitness) (side : Side) : Prop where
  move : CavityReplacement S.triangulation T.triangulation w side
  sourceMarking : MarkingConditions S.triangulation S.marking
  targetMarking : MarkingConditions T.triangulation T.marking
  seam : SameSeamFlux S T w

def checkMarkedMove (S T : MarkedState) (w : CavityWitness) (side : Side) : Bool :=
  checkMove S.triangulation T.triangulation w side &&
    checkCuspMarking S.triangulation S.marking && checkCuspMarking T.triangulation T.marking &&
    checkSeamFlux S T w

theorem checkMarkedMove_sound {S T : MarkedState} {w : CavityWitness} {side : Side}
    (h : checkMarkedMove S T w side = true) : MarkedReplacement S T w side := by
  simp only [checkMarkedMove, Bool.and_eq_true] at h
  rcases h with ⟨⟨⟨hm, hb⟩, ht⟩, hs⟩
  exact ⟨checkMove_sound hm, checkCuspMarking_sound hb, checkCuspMarking_sound ht,
    checkSeamFlux_sound hs⟩

/-- A path of marked bistellar moves. -/
inductive MarkedReplacementPath : MarkedState → MarkedState → Prop
  | nil (S) : MarkedReplacementPath S S
  | cons {S U T w side} :
      MarkedReplacement S U w side → MarkedReplacementPath U T → MarkedReplacementPath S T

/-- A path of bistellar moves, with a separate witness checked at every
transition. -/
inductive ReplacementPath : Triangulation → Triangulation → Prop
  | nil (S) : ReplacementPath S S
  | cons {S U T w side} :
      CavityReplacement S U w side → ReplacementPath U T → ReplacementPath S T

end Trefoil.Section2Pachner
