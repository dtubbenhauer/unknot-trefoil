import Trefoil.Section3APlumbing
import Trefoil.Section3ASignature
import Trefoil.Section3ACoefficients
import Trefoil.LatticeExtraction
import Mathlib.LinearAlgebra.Pi
import Mathlib.LinearAlgebra.Isomorphisms

/-!
# Section 3A relative to general topology

`Geometry` names the geometric objects, invariants and coefficient maps.
`References` contains the uniform topology statements used with those objects.
The specialization to the paper's parameter, the glued form, the rank, the
mod-two independence and the lattice obstruction are proved below.
-/

namespace Trefoil.Section3ATopology

open scoped BigOperators
open LatticeEmbedding Section3APlumbing Section3ASignature Section3ACoefficients

abbrev F₂ := ZMod 2

/-- A homology module with its coefficient-ring structure. -/
structure Homology (R : Type) [Ring R] where
  carrier : Type
  [addGroup : AddCommGroup carrier]
  [module : Module R carrier]

attribute [instance] Homology.addGroup Homology.module

instance {R : Type} [Ring R] : CoeSort (Homology R) Type :=
  ⟨Homology.carrier⟩

/-- The intended four-manifolds are smooth, compact, connected and oriented.
Boundary and knot equalities are equalities of oriented diffeomorphism and
isotopy classes respectively. Homology maps have the indicated coefficients. -/
structure Geometry where
  Knot : Type
  Three : Type
  Four : Type
  conway : List ℤ → Knot
  twoBridge : ℕ → ℕ → Knot
  mirror : Knot → Knot
  unknotting : Knot → ℕ
  signature : Knot → ℤ
  crossingChanges : Knot → ℕ → ℕ → Prop
  doubleCover : Knot → Three
  lens : ℕ → ℕ → Three
  reverse : Three → Three
  boundary : Four → Three
  closed : Four → Prop
  simplyConnected : Four → Prop
  nonemptyPathConnected : Three → Prop
  H1BoundaryZ : Three → Homology ℤ
  H2BoundaryZ : Three → Homology ℤ
  H1BoundaryF2 : Three → Homology F₂
  H2BoundaryF2 : Three → Homology F₂
  H2Z : Four → Homology ℤ
  H2F2 : Four → Homology F₂
  intersection : ∀ X, H2Z X →ₗ[ℤ] H2Z X →ₗ[ℤ] ℤ
  reduce : ∀ X, H2Z X →+ H2F2 X

variable {T : Geometry}

/-- Positivity of the integral intersection form, in the torsion-free
cases in which it is used. It is equivalent to real positive definiteness
for a finite-rank integral intersection lattice. -/
def Positive (T : Geometry) (X : T.Four) : Prop :=
  ∀ x : T.H2Z X, x ≠ 0 → 0 < T.intersection X x x

/-- A framed handle basis for a simply connected 2-handlebody. -/
structure Handlebody (T : Geometry) (n : ℕ) where
  X : T.Four
  simplyConnected : T.simplyConnected X
  coordinates : T.H2Z X ≃ₗ[ℤ] (Fin n → ℤ)

/-- The integral class of a handle in the specified basis. -/
noncomputable def Handlebody.handle {n : ℕ} (H : Handlebody T n) (i : Fin n) :
    T.H2Z H.X :=
  H.coordinates.symm (Pi.single i 1)

/-- The manifold and the homology maps induced by the gluing of collared
pieces. No exactness or intersection-form properties are part of this data. -/
structure Gluing (T : Geometry) (G W : T.Four) where
  X : T.Four
  inclZ : (T.H2Z G × T.H2Z W) →ₗ[ℤ] T.H2Z X
  inclF2 : (T.H2F2 G × T.H2F2 W) →ₗ[F₂] T.H2F2 X
  fromBoundaryF2 : T.H2BoundaryF2 (T.boundary W) →ₗ[F₂] (T.H2F2 G × T.H2F2 W)
  toBoundaryF2 : T.H2F2 X →ₗ[F₂] T.H1BoundaryF2 (T.boundary W)
  fromBoundaryZ : T.H2BoundaryZ (T.boundary W) →ₗ[ℤ] (T.H2Z G × T.H2Z W)
  toBoundaryZ : T.H2Z X →ₗ[ℤ] T.H1BoundaryZ (T.boundary W)

/-- The degree-two lens-space cellular boundary with mod-two coefficients. -/
def lensD2 (p : ℕ) : F₂ →ₗ[F₂] F₂ where
  toFun x := (p : F₂) * x
  map_add' x y := mul_add _ _ _
  map_smul' a x := by simp [smul_eq_mul, mul_left_comm]

/-- The meridian for one of the crossing changes in the basis used for the
integral surgery presentation of the Owens filling. -/
def meridian {r : ℕ} (i : Fin r) : Fin (2 * r) :=
  i.castLE (by omega)

/-- Geometry inputs. All fields are uniform in knots, surgery coefficients,
weights, or manifolds. `glue` uses an oriented boundary identification and
distinguishes the maps for the chosen gluing. Pairing preservation describes
the orthogonal sum of the two pieces by naturality and disjoint support. -/
structure References (T : Geometry) where
  sig : SignatureReferences T.twoBridge T.signature
  mirror_unknotting : ∀ K, T.unknotting (T.mirror K) = T.unknotting K
  conway_fraction : ∀ (weights : List ℤ) (p q : ℕ),
    weights ≠ [] → (∀ a ∈ weights, 0 < a) →
    Arithmetic.plusPair weights = ((p : ℤ), (q : ℤ)) →
    Odd p → q < p → Nat.Coprime p q →
    T.conway weights = T.twoBridge p q ∨ T.mirror (T.conway weights) = T.twoBridge p q
  bridge_cover : ∀ p q, Odd p → 0 < q → q < p → Nat.Coprime p q →
    T.doubleCover (T.twoBridge p q) = T.lens p q
  minimal_crossing_changes : ∀ K,
    ∃ pos neg, pos + neg = T.unknotting K ∧ T.crossingChanges K pos neg
  signature_crossing_bound : ∀ K pos neg, T.crossingChanges K pos neg →
    T.signature K ≤ 2 * (neg : ℤ)
  owens : ∀ K pos neg, T.crossingChanges K pos neg → T.signature K = 2 * (neg : ℤ) →
    ∃ W : Handlebody T (2 * (pos + neg)),
      T.boundary W.X = T.doubleCover K ∧ Positive T W.X ∧
        Matrix.det (fun i j => T.intersection W.X (W.handle i) (W.handle j)) =
          (Nat.card (T.H1BoundaryZ (T.doubleCover K)) : ℤ) ∧
        ∀ i j : Fin (pos + neg),
          T.intersection W.X (W.handle (meridian i)) (W.handle (meridian j)) =
            (if i = j then 2 else 0)
  chain_plumbing : ∀ (weights : List ℤ) (p q : ℕ),
    Arithmetic.minusPair weights = ((p : ℤ), (q : ℤ)) → 0 < q → q < p → Nat.Coprime p q →
    ∃ G : Handlebody T weights.length,
      T.boundary G.X = T.lens p q ∧
        ∀ i j, T.intersection G.X (G.handle i) (G.handle j) = chainGram weights i j
  lens_reverse : ∀ p q, 0 < q → q < p → Nat.Coprime p q →
    T.lens p (p - q) = T.reverse (T.lens p q)
  lens_connected : ∀ p q, 0 < q → q < p → Nat.Coprime p q →
    T.nonemptyPathConnected (T.lens p q)
  lens_h1_Z : ∀ p q, 0 < q → q < p → Nat.Coprime p q →
    Nonempty (T.H1BoundaryZ (T.lens p q) ≃ₗ[ℤ] ZMod p)
  lens_h2_Z : ∀ p q, 0 < q → q < p → Nat.Coprime p q →
    Subsingleton (T.H2BoundaryZ (T.lens p q))
  lens_h1_F2 : ∀ p q, 0 < q → q < p → Nat.Coprime p q →
    Nonempty (T.H1BoundaryF2 (T.lens p q) ≃ₗ[F₂] (F₂ ⧸ LinearMap.range (lensD2 p)))
  lens_h2_F2 : ∀ p q, 0 < q → q < p → Nat.Coprime p q →
    Nonempty (T.H2BoundaryF2 (T.lens p q) ≃ₗ[F₂] ↥(LinearMap.ker (lensD2 p)))
  glue : ∀ G W, T.boundary G = T.reverse (T.boundary W) → Gluing T G W
  glued_closed : ∀ G W (h : T.boundary G = T.reverse (T.boundary W)),
    T.closed (glue G W h).X
  glued_simplyConnected : ∀ G W (h : T.boundary G = T.reverse (T.boundary W)),
    T.nonemptyPathConnected (T.boundary W) →
    T.simplyConnected G → T.simplyConnected W → T.simplyConnected (glue G W h).X
  glued_intersection : ∀ G W (h : T.boundary G = T.reverse (T.boundary W)) x y,
    T.intersection (glue G W h).X ((glue G W h).inclZ x) ((glue G W h).inclZ y) =
      T.intersection G x.1 y.1 + T.intersection W x.2 y.2
  mv_Z_pieces : ∀ G W (h : T.boundary G = T.reverse (T.boundary W)) z,
    (glue G W h).inclZ z = 0 ↔ ∃ y, (glue G W h).fromBoundaryZ y = z
  mv_Z_surjective : ∀ G W (h : T.boundary G = T.reverse (T.boundary W)),
    T.simplyConnected G → T.simplyConnected W →
    Function.Surjective (glue G W h).toBoundaryZ
  mv_Z : ∀ G W (h : T.boundary G = T.reverse (T.boundary W)) x,
    (glue G W h).toBoundaryZ x = 0 ↔ ∃ z, (glue G W h).inclZ z = x
  mv_F2_pieces : ∀ G W (h : T.boundary G = T.reverse (T.boundary W)) z,
    (glue G W h).inclF2 z = 0 ↔ ∃ y, (glue G W h).fromBoundaryF2 y = z
  mv_F2_closed : ∀ G W (h : T.boundary G = T.reverse (T.boundary W)) x,
    (glue G W h).toBoundaryF2 x = 0 ↔ ∃ z, (glue G W h).inclF2 z = x
  closed_h2_torsionFree : ∀ X, T.closed X → T.simplyConnected X →
    ∀ (k : ℤ) (x : T.H2Z X), k ≠ 0 → k • x = 0 → x = 0
  uct_surjective : ∀ X, T.simplyConnected X → Function.Surjective (T.reduce X)
  uct_kernel : ∀ X, T.simplyConnected X → ∀ x,
    T.reduce X x = 0 ↔ ∃ y, x = y + y
  coefficient_naturality : ∀ G W (h : T.boundary G = T.reverse (T.boundary W)) x,
    T.reduce (glue G W h).X ((glue G W h).inclZ x) =
      (glue G W h).inclF2 (T.reduce G x.1, T.reduce W x.2)
  donaldson : ∀ X, T.closed X → T.simplyConnected X → Positive T X →
    ∃ n, ∃ e : T.H2Z X ≃ₗ[ℤ] (Fin n → ℤ),
      ∀ x y, Trefoil.LatticeSupports.dot (e x) (e y) = T.intersection X x y

/-- The two primary homology groups of the common boundary relevant to mod-two
Mayer--Vietoris vanish because the degree-two differential is multiplication
by the odd integer `p`. -/
theorem lens_F2_vanish (R : References T) {p q : ℕ} (hp : Odd p)
    (hq : 0 < q) (hqp : q < p) (hc : Nat.Coprime p q) :
    Subsingleton (T.H2BoundaryF2 (T.lens p q)) ∧
    Subsingleton (T.H1BoundaryF2 (T.lens p q)) := by
  obtain ⟨k, rfl⟩ := hp
  have hs (x : F₂) : lensD2 (2 * k + 1) x = x := by
    change ((2 * k + 1 : ℕ) : F₂) * x = x
    push_cast
    change ((2 : ZMod 2) * (k : ZMod 2) + 1) * x = x
    have hz : (2 : ZMod 2) = 0 := by decide
    simp [hz]
  obtain ⟨e₂⟩ := R.lens_h2_F2 _ _ hq hqp hc
  obtain ⟨e₁⟩ := R.lens_h1_F2 _ _ hq hqp hc
  constructor
  · refine ⟨fun x y => e₂.injective (Subtype.ext ?_)⟩
    have hx := LinearMap.mem_ker.mp (e₂ x).property
    have hy := LinearMap.mem_ker.mp (e₂ y).property
    rw [hs] at hx hy
    exact hx.trans hy.symm
  · have hr : LinearMap.range (lensD2 (2 * k + 1)) = ⊤ :=
      LinearMap.range_eq_top.mpr (fun x => ⟨x, hs x⟩)
    refine ⟨fun x y => e₁.injective ?_⟩
    have hzero (a : T.H1BoundaryF2 (T.lens (2*k+1) q)) : e₁ a = 0 := by
      obtain ⟨z, hz⟩ := Submodule.Quotient.mk_surjective _ (e₁ a)
      rw [← hz]
      exact (Submodule.Quotient.mk_eq_zero _).mpr (by rw [hr]; trivial)
    rw [hzero x, hzero y]

/-- Exactness at the two successive mod-two Mayer--Vietoris terms gives an
isomorphism between the piece homology and the glued homology. -/
theorem mv_F2_bijective (R : References T) {G W : T.Four}
    (h : T.boundary G = T.reverse (T.boundary W))
    (h₂ : Subsingleton (T.H2BoundaryF2 (T.boundary W)))
    (h₁ : Subsingleton (T.H1BoundaryF2 (T.boundary W))) :
    Function.Bijective (R.glue G W h).inclF2 := by
  constructor
  · intro u v huv
    have hz : (R.glue G W h).inclF2 (u - v) = 0 := by simp [huv]
    obtain ⟨y, hy⟩ := (R.mv_F2_pieces G W h (u - v)).mp hz
    rw [h₂.elim y 0, map_zero] at hy
    exact sub_eq_zero.mp hy.symm
  · intro x
    exact (R.mv_F2_closed G W h x).mp (h₁.elim _ _)

/-- The integral joint inclusion is injective and its cokernel is the
first integral homology of the lens boundary. -/
theorem integral_joint_exact (R : References T) {G W : T.Four}
    (h : T.boundary G = T.reverse (T.boundary W))
    (hG : T.simplyConnected G) (hW : T.simplyConnected W) {p q : ℕ}
    (hw : T.boundary W = T.lens p q) (hq : 0 < q) (hqp : q < p)
    (hc : Nat.Coprime p q) :
    Function.Injective (R.glue G W h).inclZ ∧
    Nonempty ((T.H2Z (R.glue G W h).X ⧸ LinearMap.range (R.glue G W h).inclZ) ≃ₗ[ℤ] ZMod p) := by
  let D := R.glue G W h
  have hB : Subsingleton (T.H2BoundaryZ (T.boundary W)) :=
    hw.symm ▸ R.lens_h2_Z p q hq hqp hc
  obtain ⟨e⟩ := R.lens_h1_Z p q hq hqp hc
  have e' : T.H1BoundaryZ (T.boundary W) ≃ₗ[ℤ] ZMod p := hw.symm ▸ e
  constructor
  · intro u v huv
    have hz : D.inclZ (u - v) = 0 := by
      rw [map_sub]
      exact sub_eq_zero.mpr huv
    obtain ⟨y, hy⟩ := (R.mv_Z_pieces G W h (u - v)).mp hz
    rw [hB.elim y 0, map_zero] at hy
    exact sub_eq_zero.mp hy.symm
  · have heq : LinearMap.ker D.toBoundaryZ = LinearMap.range D.inclZ := by
      ext x
      exact R.mv_Z G W h x
    change Nonempty ((T.H2Z D.X ⧸ LinearMap.range D.inclZ) ≃ₗ[ℤ] ZMod p)
    rw [← heq]
    exact ⟨(D.toBoundaryZ.quotKerEquivOfSurjective
      (R.mv_Z_surjective G W h hG hW)).trans e'⟩

/-- The inclusion of the integral joint basis has index `p`.
This follows from integral Mayer–Vietoris, independently of the mod-two
argument used for the lattice obstruction. -/
theorem integral_joint_index (R : References T) {G W : T.Four}
    (h : T.boundary G = T.reverse (T.boundary W))
    (hG : T.simplyConnected G) (hW : T.simplyConnected W) {p q : ℕ}
    (hw : T.boundary W = T.lens p q) (hq : 0 < q) (hqp : q < p)
    (hc : Nat.Coprime p q) :
    Nat.card (T.H2Z (R.glue G W h).X ⧸ LinearMap.range (R.glue G W h).inclZ) = p := by
  obtain ⟨_, ⟨e⟩⟩ := integral_joint_exact R h hG hW hw hq hqp hc
  haveI : NeZero p := ⟨by omega⟩
  rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, ZMod.card]

/-- The rational consequence of integral Mayer--Vietoris used for positivity:
the lens numerator times any integral class lifts from the two pieces.
Because the closed simply connected manifold has torsion-free (H_2),
the lift of a nonzero multiple is nonzero. -/
theorem glue_positive (R : References T) {G W : T.Four}
    (h : T.boundary G = T.reverse (T.boundary W))
    (hG : T.simplyConnected G) (hW : T.simplyConnected W)
    (pG : Positive T G) (pW : Positive T W) {p q : ℕ}
    (hw : T.boundary W = T.lens p q) (hq : 0 < q) (hqp : q < p)
    (hc : Nat.Coprime p q) : Positive T (R.glue G W h).X := by
  intro x hx
  let D := R.glue G W h
  have hp : (p : ℤ) ≠ 0 := by omega
  have hcW : T.nonemptyPathConnected (T.boundary W) :=
    hw.symm ▸ R.lens_connected p q hq hqp hc
  have hk : (p : ℤ) • x ≠ 0 := fun hz =>
    hx (R.closed_h2_torsionFree D.X (R.glued_closed G W h)
      (R.glued_simplyConnected G W h hcW hG hW) (p : ℤ) x hp hz)
  have annihilate (z : T.H1BoundaryZ (T.boundary W)) : (p : ℤ) • z = 0 := by
    revert z
    rw [hw]
    obtain ⟨e⟩ := R.lens_h1_Z p q hq hqp hc
    intro z
    apply e.injective
    rw [map_smul, map_zero]
    simp
  obtain ⟨z, hz⟩ := (R.mv_Z G W h ((p : ℤ) • x)).mp (by
    rw [map_smul]
    exact annihilate (D.toBoundaryZ x))
  have hz' : z ≠ 0 := by
    intro hz0
    apply hk
    rw [← hz, hz0, map_zero]
  have hpiece : 0 < T.intersection G z.1 z.1 + T.intersection W z.2 z.2 := by
    have hf : 0 ≤ T.intersection G z.1 z.1 := by
      by_cases he : z.1 = 0
      · simp [he]
      · exact (pG _ he).le
    have hs : 0 ≤ T.intersection W z.2 z.2 := by
      by_cases he : z.2 = 0
      · simp [he]
      · exact (pW _ he).le
    by_cases he : z.1 = 0
    · have he' : z.2 ≠ 0 := fun he' => hz' (Prod.ext he he')
      exact add_pos_of_nonneg_of_pos hf (pW _ he')
    · exact add_pos_of_pos_of_nonneg (pG _ he) hs
  have hscaled : 0 < T.intersection D.X ((p : ℤ) • x) ((p : ℤ) • x) := by
    rw [← hz, R.glued_intersection G W h]
    exact hpiece
  simp only [map_smul, LinearMap.smul_apply, zsmul_eq_mul] at hscaled
  by_contra hnot
  exact (not_lt_of_ge (mul_nonpos_of_nonneg_of_nonpos (by positivity)
    (mul_nonpos_of_nonneg_of_nonpos (by positivity) (le_of_not_gt hnot)))) hscaled


/-- Coordinates of a 2-handlebody evaluate its intersection form using the
linking matrix of its ordered, oriented handle classes. -/
theorem Handlebody.form_eq_sum {n : ℕ} (H : Handlebody T n) (x y : T.H2Z H.X) :
    T.intersection H.X x y =
      ∑ i, ∑ j, H.coordinates x i *
        T.intersection H.X (H.handle i) (H.handle j) * H.coordinates y j := by
  classical
  have expand (z : T.H2Z H.X) : (∑ i, H.coordinates z i • H.handle i) = z := by
    apply H.coordinates.injective
    simp only [map_sum, map_smul, Handlebody.handle, LinearEquiv.apply_symm_apply]
    ext k
    simp [Finset.sum_apply, Pi.single_apply, mul_ite]
  calc
    _ = T.intersection H.X (∑ i, H.coordinates x i • H.handle i)
      (∑ j, H.coordinates y j • H.handle j) := by rw [expand, expand]
    _ = _ := by
      simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
        smul_eq_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
      ring

/-- Change the length presentation of a handle list, in this case from the
computed length of the actual surgery weights to `(m - 1) + 5`. -/
def Handlebody.reindex {n k : ℕ} (H : Handlebody T n) (hk : k = n) : Handlebody T k :=
  ⟨H.X, H.simplyConnected, H.coordinates.trans
    (LinearEquiv.funCongrLeft ℤ ℤ (finCongr hk))⟩

theorem Handlebody.reindex_handle {n k : ℕ} (H : Handlebody T n) (hk : k = n)
    (i : Fin k) : (H.reindex hk).handle i = H.handle (Fin.cast hk i) := by
  subst k
  rfl

/-- The handlebody intersection calculations and the oriented boundary match
are established for the explicit surgery weights. -/
theorem explicit_plumbing (R : References T) (m : ℕ) (hm : 1 ≤ m) :
    ∃ G : Handlebody T (plumbingRank m),
      T.boundary G.X = T.reverse (T.lens (104 * m + 37) 104) ∧ Positive T G.X ∧
        ∀ i j, T.intersection G.X (G.handle i) (G.handle j) = plumbingGram m i j := by
  let p := 104 * m + 37
  have hp : 104 < p := by dsimp [p]; omega
  have hq : 0 < p - 104 := by omega
  have hqp : p - 104 < p := by omega
  have hc : Nat.Coprime p 104 := Arithmetic.determinant_coprime m
  have hcc : Nat.Coprime p (p - 104) := by
    rw [Nat.coprime_self_sub_right hp.le]
    exact hc
  have hfrac : Arithmetic.minusPair (plumbingWeights m) = ((p : ℤ), ((p - 104 : ℕ) : ℤ)) := by
    rw [plumbing_fraction m hm, Nat.cast_sub hp.le]
    simp [p]
  obtain ⟨raw, hbound, hgram⟩ := R.chain_plumbing _ _ _ hfrac hq hqp hcc
  let G := raw.reindex (plumbingWeights_length m).symm
  have hentries (i j) : T.intersection G.X (G.handle i) (G.handle j) = plumbingGram m i j := by
    rw [Handlebody.reindex_handle, Handlebody.reindex_handle]
    change T.intersection raw.X (raw.handle _) (raw.handle _) = _
    rw [hgram, chainGram_plumbing]
  refine ⟨G, hbound.trans (R.lens_reverse p 104 (by decide) hp hc), ?_, hentries⟩
  intro x hx
  rw [G.form_eq_sum]
  simp_rw [hentries]
  exact plumbing_positiveDefinite m (G.coordinates x) (fun hz => hx (G.coordinates.injective
    (hz.trans (map_zero G.coordinates).symm)))

/-- The two-bridge knot with the surgery orientation used in the proof. -/
def orientedPartner (T : Geometry) (m : ℕ) : T.Knot :=
  T.twoBridge (104 * m + 37) 104

/-- The knot in the paper, given by the positive Conway diagram. -/
def partner (T : Geometry) (m : ℕ) : T.Knot :=
  T.conway [m, 2, 1, 4, 3, 2]

/-- Signature four makes a shortest sequence with at most two moves have
exactly two moves, both negative in Owens's convention. -/
theorem two_negative_changes (R : References T) {m : ℕ} (hm : 1 ≤ m)
    (hu : T.unknotting (orientedPartner T m) < 3) :
    T.crossingChanges (orientedPartner T m) 0 2 := by
  have hsig : T.signature (orientedPartner T m) = 4 :=
    partner_signature_four R.sig m hm
  obtain ⟨pos, neg, hcount, hseq⟩ := R.minimal_crossing_changes (orientedPartner T m)
  have hbound := R.signature_crossing_bound _ _ _ hseq
  rw [hsig] at hbound
  have hpos : pos = 0 := by omega
  have hneg : neg = 2 := by omega
  simpa [hpos, hneg] using hseq

/-- Owens's general result after the specific signature and crossing-count
calculation. The meridians are the first two of four handles. -/
theorem owens_filling (R : References T) {m : ℕ} (hm : 1 ≤ m)
    (hu : T.unknotting (orientedPartner T m) < 3) :
    ∃ W : Handlebody T 4,
      T.boundary W.X = T.lens (104 * m + 37) 104 ∧ Positive T W.X ∧
        Matrix.det (fun i j => T.intersection W.X (W.handle i) (W.handle j)) = 104 * (m : ℤ) + 37 ∧
        ∀ i j : Fin 2, T.intersection W.X (W.handle (owensRoot i)) (W.handle (owensRoot j)) =
          (if i = j then 2 else 0) := by
  have hsig := partner_signature_four R.sig m hm
  obtain ⟨W, hb, hp, hd, hw⟩ := R.owens _ 0 2 (two_negative_changes R hm hu) (by
    simpa [orientedPartner] using hsig)
  have hcover : T.doubleCover (orientedPartner T m) = T.lens (104 * m + 37) 104 :=
    R.bridge_cover _ _ (Arithmetic.determinant_odd m) (by decide)
      (by omega) (Arithmetic.determinant_coprime m)
  obtain ⟨e⟩ := R.lens_h1_Z (104 * m + 37) 104 (by decide) (by omega)
    (Arithmetic.determinant_coprime m)
  haveI : NeZero (104 * m + 37) := ⟨by omega⟩
  rw [hcover, Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, ZMod.card] at hd
  push_cast at hd
  exact ⟨W, hb.trans hcover, hp, hd, hw⟩

/-- The handle from a given summand, viewed in the disjoint pieces. -/
noncomputable def jointHandle {m : ℕ} (G : Handlebody T (plumbingRank m)) (W : Handlebody T 4) :
    JointIndex m → (T.H2Z G.X × T.H2Z W.X)
  | .inl i => (G.handle i, 0)
  | .inr j => (0, W.handle j)

private theorem joint_diagonal_rank {m n : ℕ} (hm : 1 ≤ m)
    (G : Handlebody T (plumbingRank m)) (W : Handlebody T 4)
    {X : T.Four} (diag : T.H2Z X ≃ₗ[ℤ] (Fin n → ℤ)) (hx : T.simplyConnected X)
    (R : References T) (incl : (T.H2F2 G.X × T.H2F2 W.X) →ₗ[F₂] T.H2F2 X)
    (hincl : Function.Bijective incl) : n = m + 8 := by
  let eG := reductionLinearEquiv G.coordinates (T.reduce G.X)
    (R.uct_surjective G.X G.simplyConnected) (R.uct_kernel G.X G.simplyConnected)
  let eW := reductionLinearEquiv W.coordinates (T.reduce W.X)
    (R.uct_surjective W.X W.simplyConnected) (R.uct_kernel W.X W.simplyConnected)
  let eX := reductionLinearEquiv diag (T.reduce X)
    (R.uct_surjective X hx) (R.uct_kernel X hx)
  let h : (JointIndex m → F₂) ≃ₗ[F₂] (Fin n → F₂) :=
    (LinearEquiv.sumArrowLequivProdArrow _ _ _ _).trans
      ((eG.prodCongr eW).symm.trans ((LinearEquiv.ofBijective incl hincl).trans eX))
  have hcard := Fintype.card_congr h.toEquiv
  simp only [Fintype.card_fun, ZMod.card, Fintype.card_fin, joint_card m hm] at hcard
  exact (Nat.pow_right_injective (a := 2) (by decide) hcard).symm

/-- Apply the geometric inputs in their natural order. The coordinate
columns are images of the original handle classes under the actual map
in integral Mayer--Vietoris and Donaldson's isometry. Mod-two reduction
of that map is an isomorphism, so no independence is assumed. -/
theorem no_two_change_gluing (R : References T) {m : ℕ} (hm : m = 4 ∨ 6 ≤ m)
    (G : Handlebody T (plumbingRank m)) (W : Handlebody T 4)
    (hG : T.boundary G.X = T.reverse (T.lens (104 * m + 37) 104))
    (hW : T.boundary W.X = T.lens (104 * m + 37) 104)
    (pG : Positive T G.X) (pW : Positive T W.X)
    (gGram : ∀ i j, T.intersection G.X (G.handle i) (G.handle j) = plumbingGram m i j)
    (wRoots : ∀ i j : Fin 2, T.intersection W.X (W.handle (owensRoot i)) (W.handle (owensRoot j)) =
      (if i = j then 2 else 0)) : False := by
  classical
  have hm1 : 1 ≤ m := by omega
  let p := 104 * m + 37
  have hqp : 104 < p := by dsimp [p]; omega
  have hcop : Nat.Coprime p 104 := Arithmetic.determinant_coprime m
  have hb : T.boundary G.X = T.reverse (T.boundary W.X) := hG.trans (congrArg T.reverse hW.symm)
  let D := R.glue G.X W.X hb
  have hXclosed := R.glued_closed G.X W.X hb
  have hcW : T.nonemptyPathConnected (T.boundary W.X) :=
    hW.symm ▸ R.lens_connected p 104 (by decide) hqp hcop
  have hXsc := R.glued_simplyConnected G.X W.X hb hcW G.simplyConnected W.simplyConnected
  have hXpos := glue_positive R hb G.simplyConnected W.simplyConnected pG pW
    hW (by decide) hqp hcop
  obtain ⟨b₂, b₁⟩ := lens_F2_vanish R (Arithmetic.determinant_odd m) (by decide) hqp hcop
  have hincl : Function.Bijective D.inclF2 :=
    mv_F2_bijective R hb (by simpa only [hW] using b₂) (by simpa only [hW] using b₁)
  obtain ⟨n, diag, isometry⟩ := R.donaldson D.X hXclosed hXsc hXpos
  have hn := joint_diagonal_rank hm1 G W diag hXsc R D.inclF2 hincl
  subst n
  let column (i : JointIndex m) : Vector m := diag (D.inclZ (jointHandle G W i))
  let wGram (i j : Fin 4) := T.intersection W.X (W.handle i) (W.handle j)
  have hGram (i j : JointIndex m) :
      LatticeSupports.dot (column i) (column j) = jointGram m wGram i j := by
    rw [isometry, R.glued_intersection G.X W.X hb]
    cases i <;> cases j <;> simp [jointHandle, jointGram, gGram, wGram]
  let ePieces : (T.H2Z G.X × T.H2Z W.X) ≃ₗ[ℤ] (JointIndex m → ℤ) :=
    (G.coordinates.prodCongr W.coordinates).trans
      (LinearEquiv.sumArrowLequivProdArrow _ _ ℤ ℤ).symm
  let redPieces := (T.reduce G.X).prodMap (T.reduce W.X)
  have redSurj : Function.Surjective redPieces := by
    intro ⟨x, y⟩
    obtain ⟨x', rfl⟩ := R.uct_surjective G.X G.simplyConnected x
    obtain ⟨y', rfl⟩ := R.uct_surjective W.X W.simplyConnected y
    exact ⟨(x', y'), rfl⟩
  have redKer (x : T.H2Z G.X × T.H2Z W.X) :
      redPieces x = 0 ↔ ∃ y, x = y + y := by
    constructor
    · intro hx
      obtain ⟨a, ha⟩ := (R.uct_kernel G.X G.simplyConnected x.1).mp (congrArg Prod.fst hx)
      obtain ⟨b, hb⟩ := (R.uct_kernel W.X W.simplyConnected x.2).mp (congrArg Prod.snd hx)
      exact ⟨(a, b), Prod.ext ha hb⟩
    · rintro ⟨y, rfl⟩
      exact Prod.ext ((R.uct_kernel G.X G.simplyConnected _).mpr ⟨y.1, rfl⟩)
        ((R.uct_kernel W.X W.simplyConnected _).mpr ⟨y.2, rfl⟩)
  have hs (i : JointIndex m) : ePieces.symm (Pi.single i 1) = jointHandle G W i := by
    apply ePieces.injective
    rw [LinearEquiv.apply_symm_apply]
    funext j
    cases i <;> cases j <;> simp [ePieces, jointHandle, Handlebody.handle, Pi.single_apply]
  have selectInd := reduced_columns_independent ePieces diag D.inclZ D.inclF2
    redPieces redSurj redKer (T.reduce D.X)
    (R.uct_surjective D.X hXsc) (R.uct_kernel D.X hXsc)
    (R.coefficient_naturality G.X W.X hb) hincl.1 (selectedIndex m) (selectedIndex_injective m)
  simp_rw [hs] at selectInd
  apply Trefoil.LatticeExtraction.no_embedding hm
  exact {
    root := fun r => column (jointRoot m r)
    A := column (plumbingA m)
    B := column (plumbingB m)
    C := column (plumbingC m)
    root_pairing := fun r s => (hGram _ _).trans (jointGram_root m wGram wRoots r s)
    normA := by simpa [LatticeSupports.dot, pow_two] using (hGram (plumbingA m) (plumbingA m))
    normB := by simpa [LatticeSupports.dot, pow_two] using (hGram (plumbingB m) (plumbingB m))
    normC := by simpa [LatticeSupports.dot, pow_two] using (hGram (plumbingC m) (plumbingC m))
    pairingAB := (hGram _ _).trans (jointGram_AB m wGram)
    pairingAC := (hGram _ _).trans (jointGram_AC m wGram)
    pairingBC := (hGram _ _).trans (jointGram_BC m wGram)
    pairingA_root := fun r => (hGram _ _).trans (jointGram_A_root m hm1 wGram r)
    pairingB_root := fun r => (hGram _ _).trans (jointGram_B_root m wGram r)
    pairingC_root := fun r => (hGram _ _).trans (jointGram_C_root m wGram r)
    independent := by
      convert selectInd using 1
      funext i
      cases i <;> rfl
  }

/-- Section 3A in the orientation for which the signature is positive four. -/
theorem section3A_oriented_lower_bound (R : References T) {m : ℕ}
    (hm : m = 4 ∨ 6 ≤ m) : 3 ≤ T.unknotting (orientedPartner T m) := by
  by_contra! hu
  have hm1 : 1 ≤ m := by omega
  obtain ⟨W, hW, pW, _, wRoots⟩ := owens_filling R hm1 hu
  obtain ⟨G, hG, pG, gGram⟩ := explicit_plumbing R m hm1
  exact no_two_change_gluing R hm G W hG hW pG pW gGram wRoots

/-- Section 3A for the paper's knots. All family-specific calculations
are proved by the construction above; the inputs state general topology. -/
theorem section3A_lower_bound (R : References T) {m : ℕ}
    (hm : m = 4 ∨ 6 ≤ m) : 3 ≤ T.unknotting (partner T m) := by
  have hu := section3A_oriented_lower_bound R hm
  have hpos : ∀ a ∈ [(m : ℤ), 2, 1, 4, 3, 2], 0 < a := by
    intro a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl <;> omega
  rcases R.conway_fraction [(m : ℤ), 2, 1, 4, 3, 2] (104 * m + 37) 104
      (by simp) hpos (by simpa using Arithmetic.partner_fraction (m : ℤ))
      (Arithmetic.determinant_odd m) (by omega) (Arithmetic.determinant_coprime m) with h | h
  · change partner T m = orientedPartner T m at h
    rwa [h]
  · change T.mirror (partner T m) = orientedPartner T m at h
    simpa only [← h, R.mirror_unknotting] using hu

end Trefoil.Section3ATopology
