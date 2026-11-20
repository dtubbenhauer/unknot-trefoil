import experimental.Section3ACanonicalTopology

/-!
# Section 3A: explicit homology comparisons in the relative gluing theorem

The previous canonical theorem modelled the homology of the boundary and
pieces by the canonical cellular/free modules *definitionally*.  The actual
manifolds have singular-homology groups, not these literal types.  The
comparison equivalences are now visible hypotheses, along with the genuine
Mayer--Vietoris inclusion/exactness maps and mod-2 Donaldson coordinates.

No conclusion of the lattice obstruction, no independence statement, and no
lattice embedding structure occurs among the fields of `ManifoldHomologyData`.
All the Gram entries are local 2-handlebody linking-form data.  Realizing
these fields for the specific two-bridge knot and Owens filling, relative to
standard topology and the cited theorems, is a separate geometric obligation.
-/

namespace Trefoil.RelativeTopology

open Trefoil.LatticeEmbedding Trefoil.LatticeSupports
open scoped BigOperators

variable {Y P X : Type*}
variable [AddCommGroup Y] [AddCommGroup P] [AddCommGroup X]
variable [Module (ZMod 2) Y] [Module (ZMod 2) P] [Module (ZMod 2) X]

/-- An explicit interface for the actual singular homology groups.

* `Y` is H₂ of the boundary over F₂;
* `P` is H₂ of the **disjoint two pieces** over F₂;
* `X` is H₂ of their closed gluing over F₂.

The two equivalences `cellularComparison` and `handleBasis` are general
standard-topology inputs, not definitional identifications of these groups.
The local pairings are obtained from the two framed 2-handle links.  The
naturality equation is the standard reduction of integral handle classes
in Donaldson coordinates, not a disguised independence hypothesis.
-/
structure ManifoldHomologyData (m : ℕ) (Y P X : Type*)
    [AddCommGroup Y] [AddCommGroup P] [AddCommGroup X]
    [Module (ZMod 2) Y] [Module (ZMod 2) P] [Module (ZMod 2) X] where
  cellularComparison : Y ≃ₗ[ZMod 2] lensTwoCycles m
  handleBasis : P ≃ₗ[ZMod 2] pieceHandleModule m
  boundaryMap : Y →ₗ[ZMod 2] P
  inclusion : P →ₗ[ZMod 2] X
  mvExact : ∀ z : P, inclusion z = 0 → ∃ y : Y, boundaryMap y = z
  coordinates : X ≃ₗ[ZMod 2] (Ambient m → ZMod 2)
  root : RootIndex m → Vector m
  A : Vector m
  Bheavy : Vector m
  C : Vector m
  root_pairing : ∀ r s, dot (root r) (root s) = rootGram r s
  normA : ∑ j, A j ^ 2 = 4
  normB : ∑ j, Bheavy j ^ 2 = 6
  normC : ∑ j, C j ^ 2 = 3
  pairingAB : dot A Bheavy = -1
  pairingAC : dot A C = 0
  pairingBC : dot Bheavy C = 0
  pairingA_root : ∀ r, dot A (root r) = aRootPairing r
  pairingB_root : ∀ r, dot Bheavy (root r) = bRootPairing r
  pairingC_root : ∀ r, dot C (root r) = cRootPairing r
  naturality : ∀ (r : Option (RootIndex m)) (j : Ambient m),
    coordinates (inclusion (handleBasis.symm
      (canonicalSelectedHandles m (Finsupp.single r 1)))) j =
      (match r with
        | none => (Bheavy j : ZMod 2)
        | some i => (root i j : ZMod 2))

/-- The boundary homology group vanishes, from the *explicit* cellular
comparison, rather than by declaring boundary singular homology to equal a
cellular kernel by definition. -/
theorem ManifoldHomologyData.boundarySubsingleton {m : ℕ}
    (d : ManifoldHomologyData m Y P X) : Subsingleton Y :=
  ⟨fun _ _ => d.cellularComparison.injective (Subsingleton.elim _ _)⟩

/-- Convert the actual homology models to the canonical relative bridge.
The conversion of the geometric maps is only basis transport; it does not
assume the desired lattice obstruction. -/
noncomputable def ManifoldHomologyData.toCanonical {m : ℕ}
    (d : ManifoldHomologyData m Y P X) : CanonicalGluingData m X where
  root := d.root
  A := d.A
  Bheavy := d.Bheavy
  C := d.C
  root_pairing := d.root_pairing
  normA := d.normA
  normB := d.normB
  normC := d.normC
  pairingAB := d.pairingAB
  pairingAC := d.pairingAC
  pairingBC := d.pairingBC
  pairingA_root := d.pairingA_root
  pairingB_root := d.pairingB_root
  pairingC_root := d.pairingC_root
  boundary := d.handleBasis.toLinearMap.comp
    (d.boundaryMap.comp d.cellularComparison.symm.toLinearMap)
  inclusion := d.inclusion.comp d.handleBasis.symm.toLinearMap
  exact_at_pieces := by
    intro z hz
    have hinc : d.inclusion (d.handleBasis.symm z) = 0 := hz
    obtain ⟨y, hy⟩ := d.mvExact (d.handleBasis.symm z) hinc
    refine ⟨d.cellularComparison y, ?_⟩
    change d.handleBasis (d.boundaryMap
      (d.cellularComparison.symm (d.cellularComparison y))) = z
    simp [hy]
  diagonal_coordinates := d.coordinates
  naturality := d.naturality

/-- Final relative topology-to-lattice implication with the *singular to
cellular* and *handle basis* comparison maps made explicit.  No separate
mod-two independence, determinant, coordinate normal form, or contradiction
is supplied in the input. -/
theorem no_manifold_homology_data {m : ℕ} (hm : m = 4 ∨ 6 ≤ m)
    (d : ManifoldHomologyData m Y P X) : False := by
  exact no_canonical_gluing_data hm d.toCanonical

end Trefoil.RelativeTopology
