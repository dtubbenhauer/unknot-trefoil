import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.OfMap
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Finite triangulation certificates for Section 2

A certificate supplies the destination tetrahedron and the vertex
permutation for each tetrahedron. The same convention is used for face
gluings: face `f` is opposite vertex `f`, and a permutation acts from source
vertex labels to target vertex labels.
-/

namespace Trefoil.Section2Triangulations

abbrev Vertex := Fin 4

/-- The raw action on one tetrahedron, including its vertex labels. -/
structure TetImage where
  tet : ℕ
  vertices : Array ℕ
  deriving Inhabited, Repr

/-- A raw triangulation lists the four gluings of each tetrahedron. -/
abbrev Triangulation := Array (Array TetImage)

/-- Out-of-bounds lookups are used only inside the decidable condition.
Every index in a certified gluing or isomorphism is proved to be in range. -/
def face (T : Triangulation) (t f : ℕ) : TetImage := (T.getD t #[]).getD f default

def vertex (a : TetImage) (v : ℕ) : ℕ := a.vertices.getD v 0

def VertexPermutation (a : TetImage) : Prop :=
  a.vertices.size = 4 ∧
  (∀ v : Vertex, vertex a v < 4) ∧
  ∀ v w : Vertex, vertex a v = vertex a w → v = w

instance (a : TetImage) : Decidable (VertexPermutation a) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- The parity of the inversion count in the four vertex labels. -/
def oddVertices (a : TetImage) : Bool :=
  let inv (i j : ℕ) : ℕ := if vertex a j < vertex a i then 1 else 0
  (inv 0 1 + inv 0 2 + inv 0 3 + inv 1 2 + inv 1 3 + inv 2 3) % 2 == 1

/-- Every face has a destination, the two face maps are inverse, and the
standard orientations on tetrahedra agree across faces. -/
def Valid (T : Triangulation) : Prop :=
  0 < T.size ∧
  ∀ t : Fin T.size, (T.getD t #[]).size = 4 ∧
    ∀ f : Vertex,
      let a := face T t f
      let b := face T a.tet (vertex a f)
      a.tet < T.size ∧ VertexPermutation a ∧ oddVertices a = true ∧
      (a.tet ≠ t.val ∨ vertex a f ≠ f.val) ∧ b.tet = t.val ∧
      ∀ v : Vertex, vertex b (vertex a v) = v.val

instance (T : Triangulation) : Decidable (Valid T) :=
  inferInstanceAs (Decidable (_ ∧ _))

def image (certificate : Array TetImage) (t : ℕ) : TetImage :=
  certificate.getD t default

/-- The finite equations for a marked, oriented combinatorial isomorphism.
The face equation compares the two paths around each gluing square. -/
def IsoConditions (S T : Triangulation) (certificate : Array TetImage)
    (reverse : Bool) : Prop :=
  certificate.size = S.size ∧ S.size = T.size ∧
  (∀ t u : Fin S.size, (image certificate t).tet = (image certificate u).tet → t = u) ∧
  ∀ t : Fin S.size,
    let p := image certificate t
    p.tet < T.size ∧ VertexPermutation p ∧ oddVertices p = reverse ∧
    ∀ f : Vertex,
      let a := face S t f
      let b := face T p.tet (vertex p f)
      let q := image certificate a.tet
      q.tet = b.tet ∧
      ∀ v : Vertex, vertex q (vertex a v) = vertex b (vertex p v)

instance (S T : Triangulation) (certificate : Array TetImage) (reverse : Bool) :
    Decidable (IsoConditions S T certificate reverse) :=
  inferInstanceAs (Decidable (_ ∧ _))

private def allFin (n : ℕ) (test : Fin n → Bool) : Bool :=
  (List.finRange n).all test

private theorem allFin_true {n : ℕ} {test : Fin n → Bool} :
    allFin n test = true ↔ ∀ i, test i = true := by
  simp [allFin, List.mem_finRange]

private def anyFin (n : ℕ) (test : Fin n → Bool) : Bool :=
  (List.finRange n).any test

private theorem anyFin_true {n : ℕ} {test : Fin n → Bool} :
    anyFin n test = true ↔ ∃ i, test i = true := by
  simp [anyFin, List.mem_finRange]

private def checkVertexPermutation (a : TetImage) : Bool :=
  decide (a.vertices.size = 4) &&
  allFin 4 (fun v => decide (vertex a v < 4)) &&
  allFin 4 (fun v => allFin 4 (fun w => decide (vertex a v = vertex a w → v = w)))

private theorem checkVertexPermutation_true {a : TetImage} :
    checkVertexPermutation a = true ↔ VertexPermutation a := by
  simp only [checkVertexPermutation, VertexPermutation, allFin_true, Bool.and_eq_true,
    decide_eq_true_eq, and_assoc]

def checkTriangulation (T : Triangulation) : Bool :=
  decide (0 < T.size) &&
  allFin T.size (fun t => decide ((T.getD t #[]).size = 4) &&
    allFin 4 (fun f =>
      let a := face T t f
      let b := face T a.tet (vertex a f)
      decide (a.tet < T.size) && checkVertexPermutation a && oddVertices a &&
      decide (a.tet ≠ t.val ∨ vertex a f ≠ f.val) && decide (b.tet = t.val) &&
      allFin 4 (fun v => decide (vertex b (vertex a v) = v.val))))

def checkIso (S T : Triangulation) (certificate : Array TetImage) (reverse : Bool) : Bool :=
  decide (certificate.size = S.size) && decide (S.size = T.size) &&
  allFin S.size (fun t => allFin S.size (fun u =>
    decide ((image certificate t).tet = (image certificate u).tet → t = u))) &&
  allFin S.size (fun t =>
    let p := image certificate t
    decide (p.tet < T.size) && checkVertexPermutation p &&
    decide (oddVertices p = reverse) &&
    allFin 4 (fun f =>
      let a := face S t f
      let b := face T p.tet (vertex p f)
      let q := image certificate a.tet
      decide (q.tet = b.tet) &&
      allFin 4 (fun v => decide (vertex q (vertex a v) = vertex b (vertex p v)))))

theorem checkTriangulation_sound {T : Triangulation} (h : checkTriangulation T = true) :
    Valid T := by
  simpa only [checkTriangulation, Valid, allFin_true, checkVertexPermutation_true,
    Bool.and_eq_true, decide_eq_true_eq, and_assoc] using h

theorem checkIso_conditions {S T : Triangulation} {c : Array TetImage} {r : Bool}
    (h : checkIso S T c r = true) : IsoConditions S T c r := by
  simpa only [checkIso, IsoConditions, allFin_true, checkVertexPermutation_true,
    Bool.and_eq_true, decide_eq_true_eq, and_assoc] using h

/-- Turn the checked local vertex permutation into an actual equivalence. -/
noncomputable def localEquiv (a : TetImage) (h : VertexPermutation a) : Vertex ≃ Vertex :=
  Equiv.ofBijective (fun v => ⟨vertex a v, h.2.1 v⟩)
    ⟨fun _ _ he => h.2.2 _ _ (congrArg Fin.val he), by
      apply Finite.surjective_of_injective
      intro v w he
      exact h.2.2 v w (congrArg Fin.val he)⟩

@[simp] theorem localEquiv_val (a : TetImage) (h : VertexPermutation a) (v : Vertex) :
    (localEquiv a h v).val = vertex a v :=
  rfl

/-- The geometric interpretation of the isomorphism has typed, bijective
actions on tetrahedra and vertices. The raw certificate is retained so
that cusp checks use exactly the same maps. -/
structure Isomorphism (S T : Triangulation) (certificate : Array TetImage) (reverse : Bool) where
  sourceValid : Valid S
  targetValid : Valid T
  conditions : IsoConditions S T certificate reverse
  tetrahedra : Fin S.size ≃ Fin T.size
  vertices : Fin S.size → (Vertex ≃ Vertex)
  tetrahedronImage : ∀ t, (tetrahedra t).val = (image certificate t).tet
  vertexImage : ∀ t v, (vertices t v).val = vertex (image certificate t) v

/-- The checker produces bijections with the checked face relations. -/
noncomputable def checkIso_sound {S T : Triangulation} {c : Array TetImage} {r : Bool}
    (hs : checkTriangulation S = true) (ht : checkTriangulation T = true)
    (h : checkIso S T c r = true) : Isomorphism S T c r := by
  have hok := checkIso_conditions h
  let f (t : Fin S.size) : Fin T.size := ⟨(image c t).tet, (hok.2.2.2 t).1⟩
  have hi : Function.Injective f := fun s t he => hok.2.2.1 s t (congrArg Fin.val he)
  have hsurj : Function.Surjective f := by
    apply (Finite.injective_iff_surjective_of_equiv (finCongr hok.2.1)).mp
    exact hi
  exact ⟨checkTriangulation_sound hs, checkTriangulation_sound ht, hok,
    Equiv.ofBijective f ⟨hi, hsurj⟩,
    fun t => localEquiv (image c t) (hok.2.2.2 t).2.1,
    fun _ => rfl, fun _ _ => rfl⟩


/-- A table of signed integers. The packed form stores each zigzag-encoded
integer in one fixed-width binary block, with the first entry in the least
significant block. This keeps kernel lookup independent of array length. -/
inductive SignedTable where
  | array (data : Array Int)
  | packed (size width word : ℕ)
  deriving Repr

instance : Coe (Array Int) SignedTable := ⟨SignedTable.array⟩

def SignedTable.size : SignedTable → ℕ
  | .array data => data.size
  | .packed n _ _ => n

def SignedTable.getD : SignedTable → ℕ → Int → Int
  | .array data, i, fallback => data.getD i fallback
  | .packed n width word, i, fallback =>
      if i < n then
        let k := (word >>> (width * i)) % (1 <<< width)
        if k % 2 = 0 then Int.ofNat (k / 2) else Int.negSucc (k / 2)
      else fallback

/-- Cusp labels and signed normal-curve weights across the sides of the
truncated cusp triangles. The last two arrays have entries indexed by
`16 * tetrahedron + 4 * cuspVertex + face`. -/
structure CuspMarking where
  cuspCount : ℕ
  cuspIndices : Array ℕ
  meridian : SignedTable
  longitude : SignedTable
  deriving Repr

def cusp (M : CuspMarking) (t v : ℕ) : ℕ :=
  M.cuspIndices.getD (4 * t + v) 0

/-- The same array layout is used for normal curves and corner potentials;
the final index is a tetrahedron face for curves and a tetrahedron vertex
for potentials. -/
def entry (data : SignedTable) (t v f : ℕ) : Int :=
  data.getD (16 * t + 4 * v + f) 0

def ClosedCurve (T : Triangulation) (curve : SignedTable) : Prop :=
  curve.size = 16 * T.size ∧
  ∀ (t : Fin T.size) (v : Vertex),
    entry curve t v v = 0 ∧
    entry curve t v 0 + entry curve t v 1 + entry curve t v 2 + entry curve t v 3 = 0 ∧
    ∀ f : Vertex, f ≠ v →
      let g := face T t f
      entry curve t v f = -(entry curve g.tet (vertex g v) (vertex g f))

instance (T : Triangulation) (curve : SignedTable) : Decidable (ClosedCurve T curve) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- Corner labels identify the cusps on paired faces, and the meridian
and longitude data are cycles in the dual cell decomposition. -/
def MarkingConditions (T : Triangulation) (M : CuspMarking) : Prop :=
  0 < M.cuspCount ∧ M.cuspIndices.size = 4 * T.size ∧
  (∀ c : Fin M.cuspCount, ∃ (t : Fin T.size) (v : Vertex), cusp M t v = c.val) ∧
  (∀ (t : Fin T.size) (v : Vertex), cusp M t v < M.cuspCount ∧
    ∀ f : Vertex, f ≠ v →
      let g := face T t f
      cusp M t v = cusp M g.tet (vertex g v)) ∧
  ClosedCurve T M.meridian ∧ ClosedCurve T M.longitude

instance (T : Triangulation) (M : CuspMarking) : Decidable (MarkingConditions T M) :=
  inferInstanceAs (Decidable (_ ∧ _))

private def checkClosedCurve (T : Triangulation) (curve : SignedTable) : Bool :=
  decide (curve.size = 16 * T.size) &&
  allFin T.size (fun t => allFin 4 (fun v =>
    decide (entry curve t v v = 0) &&
    decide (entry curve t v 0 + entry curve t v 1 + entry curve t v 2 + entry curve t v 3 = 0) &&
    allFin 4 (fun f => decide (f ≠ v →
      let g := face T t f
      entry curve t v f = -(entry curve g.tet (vertex g v) (vertex g f))))))

private theorem checkClosedCurve_true {T : Triangulation} {curve : SignedTable} :
    checkClosedCurve T curve = true ↔ ClosedCurve T curve := by
  simp only [checkClosedCurve, ClosedCurve, allFin_true, Bool.and_eq_true,
    decide_eq_true_eq, and_assoc]

def checkCuspMarking (T : Triangulation) (M : CuspMarking) : Bool :=
  decide (0 < M.cuspCount) && decide (M.cuspIndices.size = 4 * T.size) &&
  allFin M.cuspCount (fun c => anyFin T.size (fun t => anyFin 4 (fun v =>
    decide (cusp M t v = c.val)))) &&
  allFin T.size (fun t => allFin 4 (fun v =>
    decide (cusp M t v < M.cuspCount) &&
    allFin 4 (fun f => decide (f ≠ v →
      let g := face T t f
      cusp M t v = cusp M g.tet (vertex g v))))) &&
  checkClosedCurve T M.meridian && checkClosedCurve T M.longitude

theorem checkCuspMarking_sound {T : Triangulation} {M : CuspMarking}
    (h : checkCuspMarking T M = true) : MarkingConditions T M := by
  simpa only [checkCuspMarking, MarkingConditions, allFin_true, anyFin_true, checkClosedCurve_true,
    Bool.and_eq_true, decide_eq_true_eq,
    and_assoc] using h

/-- The map on each cusp in the ordered meridian-longitude basis.
Entries are in row-major order, so the columns are the images of the
source meridian and source longitude. -/
structure CuspImage where
  cusp : ℕ
  mm : Int
  ml : Int
  lm : Int
  ll : Int
  deriving Inhabited, Repr

/-- A potential is the coefficient of a dual 2-cell around a cusp vertex.
Separate potentials exhibit the relations for the source meridian and
longitude, with each supported over all target cusps. -/
structure PeripheralWitness where
  maps : Array CuspImage
  meridianPotential : SignedTable
  longitudePotential : SignedTable
  deriving Repr

def peripheralImage (w : PeripheralWitness) (c : ℕ) : CuspImage :=
  w.maps.getD c default

/-- A potential has one common value at the corners identified by a gluing.
The corners are indexed by the two endpoints of the original tetrahedron
edge they truncate. -/
def GluedPotential (T : Triangulation) (P : SignedTable) : Prop :=
  P.size = 16 * T.size ∧
  ∀ (t : Fin T.size) (v f w : Vertex), f ≠ v → f ≠ w → v ≠ w →
    let g := face T t f
    entry P t v w = entry P g.tet (vertex g v) (vertex g w)

instance (T : Triangulation) (P : SignedTable) : Decidable (GluedPotential T P) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- The difference of the dual 2-cell coefficients at the two endpoints of
a cusp triangle side. The sign uses the orientation of the truncated
triangle from the ordered tetrahedron. Reversing the orientation convention
for all boundaries would also negate all potentials. -/
def boundaryEntry (P : SignedTable) (t v f : ℕ) : Int :=
  let endpoints := [0, 1, 2, 3].filter (fun w => w != v && w != f)
  let parity := (v + f - (if v < f then 1 else 0)) % 2
  let difference := entry P t v (endpoints.getD 1 0) - entry P t v (endpoints.getD 0 0)
  if parity = 0 then difference else -difference

/-- Check the cusp bijection and the induced maps on both cycles. The
peripheral matrices are verified by integral chain differences, rather
than copied from the external isomorphism search as conclusions. -/
def PeripheralConditions (S T : Triangulation) (certificate : Array TetImage)
    (MS MT : CuspMarking) (w : PeripheralWitness) : Prop :=
  w.maps.size = MS.cuspCount ∧ MS.cuspCount = MT.cuspCount ∧
  (∀ c : Fin MS.cuspCount, (peripheralImage w c).cusp < MT.cuspCount) ∧
  (∀ c d : Fin MS.cuspCount, (peripheralImage w c).cusp = (peripheralImage w d).cusp → c = d) ∧
  GluedPotential T w.meridianPotential ∧ GluedPotential T w.longitudePotential ∧
  ∀ (t : Fin S.size) (v : Vertex),
    let p := image certificate t
    let dest := peripheralImage w (cusp MS t v)
    let u := vertex p v
    cusp MT p.tet u = dest.cusp ∧
    ∀ f : Vertex, f ≠ v →
      let g := vertex p f
      let targetMu := entry MT.meridian p.tet u g
      let targetLambda := entry MT.longitude p.tet u g
      entry MS.meridian t v f - (dest.mm * targetMu + dest.lm * targetLambda) =
        boundaryEntry w.meridianPotential p.tet u g ∧
      entry MS.longitude t v f - (dest.ml * targetMu + dest.ll * targetLambda) =
        boundaryEntry w.longitudePotential p.tet u g

instance (S T : Triangulation) (certificate : Array TetImage) (MS MT : CuspMarking)
    (w : PeripheralWitness) : Decidable (PeripheralConditions S T certificate MS MT w) :=
  inferInstanceAs (Decidable (_ ∧ _))

private def checkGluedPotential (T : Triangulation) (P : SignedTable) : Bool :=
  decide (P.size = 16 * T.size) &&
  allFin T.size (fun t => allFin 4 (fun v => allFin 4 (fun f => allFin 4 (fun w =>
    decide (f ≠ v → f ≠ w → v ≠ w →
      let g := face T t f
      entry P t v w = entry P g.tet (vertex g v) (vertex g w))))))

private theorem checkGluedPotential_true {T : Triangulation} {P : SignedTable} :
    checkGluedPotential T P = true ↔ GluedPotential T P := by
  simp only [checkGluedPotential, GluedPotential, allFin_true, Bool.and_eq_true, decide_eq_true_eq]

def checkPeripheral (S T : Triangulation) (certificate : Array TetImage)
    (MS MT : CuspMarking) (w : PeripheralWitness) : Bool :=
  decide (w.maps.size = MS.cuspCount) && decide (MS.cuspCount = MT.cuspCount) &&
  allFin MS.cuspCount (fun c => decide ((peripheralImage w c).cusp < MT.cuspCount)) &&
  allFin MS.cuspCount (fun c => allFin MS.cuspCount (fun d =>
    decide ((peripheralImage w c).cusp = (peripheralImage w d).cusp → c = d))) &&
  checkGluedPotential T w.meridianPotential && checkGluedPotential T w.longitudePotential &&
  allFin S.size (fun t => allFin 4 (fun v =>
    let p := image certificate t
    let dest := peripheralImage w (cusp MS t v)
    let u := vertex p v
    decide (cusp MT p.tet u = dest.cusp) &&
    allFin 4 (fun f => decide (f ≠ v →
      let g := vertex p f
      let targetMu := entry MT.meridian p.tet u g
      let targetLambda := entry MT.longitude p.tet u g
      entry MS.meridian t v f - (dest.mm * targetMu + dest.lm * targetLambda) =
        boundaryEntry w.meridianPotential p.tet u g ∧
      entry MS.longitude t v f - (dest.ml * targetMu + dest.ll * targetLambda) =
        boundaryEntry w.longitudePotential p.tet u g))))

theorem checkPeripheral_sound {S T : Triangulation} {c : Array TetImage}
    {MS MT : CuspMarking} {w : PeripheralWitness}
    (h : checkPeripheral S T c MS MT w = true) :
    PeripheralConditions S T c MS MT w := by
  simpa only [checkPeripheral, PeripheralConditions, allFin_true, checkGluedPotential_true,
    Bool.and_eq_true, decide_eq_true_eq,
    and_assoc] using h

/-- The certified action is typed on the finite set of cusp labels. -/
noncomputable def peripheralEquiv {S T : Triangulation} {c : Array TetImage}
    {MS MT : CuspMarking} {w : PeripheralWitness}
    (h : PeripheralConditions S T c MS MT w) :
    Fin MS.cuspCount ≃ Fin MT.cuspCount := by
  let f (i : Fin MS.cuspCount) : Fin MT.cuspCount :=
    ⟨(peripheralImage w i).cusp, h.2.2.1 i⟩
  have hi : Function.Injective f := fun i j hij => h.2.2.2.1 i j (congrArg Fin.val hij)
  exact Equiv.ofBijective f
    ⟨hi, (Finite.injective_iff_surjective_of_equiv (finCongr h.2.1)).mp hi⟩

/-- An oriented combinatorial isomorphism with its checked peripheral
action. The potential data witnesses equality of homology classes in the
dual cusp cellulations. A separate realization identifies each supplied
marked triangulation with the exterior of its designated link. -/
structure MarkedIsomorphism (S T : Triangulation) (c : Array TetImage)
    (reverse : Bool) (MS MT : CuspMarking) (w : PeripheralWitness) where
  iso : Isomorphism S T c reverse
  sourceMarking : MarkingConditions S MS
  targetMarking : MarkingConditions T MT
  peripheral : PeripheralConditions S T c MS MT w

noncomputable def checkMarkedIso_sound {S T : Triangulation} {c : Array TetImage} {r : Bool}
    {MS MT : CuspMarking} {w : PeripheralWitness}
    (hs : checkTriangulation S = true) (ht : checkTriangulation T = true)
    (hi : checkIso S T c r = true) (hms : checkCuspMarking S MS = true)
    (hmt : checkCuspMarking T MT = true) (hp : checkPeripheral S T c MS MT w = true) :
    MarkedIsomorphism S T c r MS MT w :=
  ⟨checkIso_sound hs ht hi, checkCuspMarking_sound hms, checkCuspMarking_sound hmt,
    checkPeripheral_sound hp⟩

end Trefoil.Section2Triangulations
