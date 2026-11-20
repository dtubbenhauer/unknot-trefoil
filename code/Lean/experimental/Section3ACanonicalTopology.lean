import experimental.Section3ARelativeMVStandalone

/-!
# Section 3A: canonical mod-two homology models

This module eliminates **two** assumptions from the previous relative bridge:

* The boundary cycle module is the actual kernel of the lens-space cellular
  differential `d₂ = (104*m+37)`, which is zero over `ZMod 2`.
* The selected handle classes are the first summand of an explicitly free
  module with `m+8` handle generators, and their independence is proved.

The remaining inputs are the exactness of the Mayer--Vietoris segment for the
actual gluing, the transported local intersection numbers, the Donaldson
coordinates, and compatibility of coefficient reduction. These are genuinely
geometric and are **not** inferred merely from the cellular calculation.

The homology-comparison stage transports singular homology to these models.
-/

namespace Trefoil.RelativeTopology

open Trefoil.LatticeEmbedding Trefoil.LatticeSupports
open scoped BigOperators

/-- Degree-two boundary operator in the usual cellular complex of L(p,q),
with `p = 104*m+37`, reduced modulo two. -/
def lensD2 (m : ℕ) : ZMod 2 →ₗ[ZMod 2] ZMod 2 where
  toFun := fun x => ((104 * m + 37 : ℕ) : ZMod 2) * x
  map_add' := fun x y => mul_add _ x y
  map_smul' := by
    intro a x
    change ((104 * m + 37 : ℕ) : ZMod 2) * (a * x) =
      a * (((104 * m + 37 : ℕ) : ZMod 2) * x)
    exact mul_left_comm _ _ _

/-- Degree-two *cycles* in the standard lens-space cellular complex. The
identification with topological singular homology is a separate standard
cellular-homology input, not asserted by this definition. -/
abbrev lensTwoCycles (m : ℕ) := ↥(LinearMap.ker (lensD2 m))

/-- The degree-two cellular cycles vanish, uniformly in m. -/
theorem lensTwoCycles_eq_zero (m : ℕ) (x : lensTwoCycles m) : x = 0 := by
  apply Subtype.ext
  have hx : (lensD2 m) x.val = 0 := LinearMap.mem_ker.mp x.property
  change ((104 * m + 37 : ℕ) : ZMod 2) * x.val = 0 at hx
  exact lens_cellular_kernel_zero m x.val hx

instance lensTwoCycles_subsingleton (m : ℕ) : Subsingleton (lensTwoCycles m) :=
  ⟨fun x y => (lensTwoCycles_eq_zero m x).trans (lensTwoCycles_eq_zero m y).symm⟩

/-- A canonical free handle module. The first block consists of the selected
weight-six class and the norm-two roots. The second consists of the weight-four
and weight-three plumbing vertices and the two remaining Owens handles. -/
abbrev selectedHandleModule (m : ℕ) := Option (RootIndex m) →₀ ZMod 2
abbrev otherHandleModule := Fin 4 →₀ ZMod 2
abbrev pieceHandleModule (m : ℕ) := selectedHandleModule m × otherHandleModule

/-- The inclusion of the selected handle generators in the full handle basis.
No independent-family premise is needed before gluing. -/
def canonicalSelectedHandles (m : ℕ) :
    selectedHandleModule m →ₗ[ZMod 2] pieceHandleModule m where
  toFun := fun u => (u, 0)
  map_add' := by intro u v; simp
  map_smul' := by intro a u; simp

/-- Independence of those handle classes *before gluing* is automatic. -/
theorem canonicalSelectedHandles_injective (m : ℕ) :
    Function.Injective (canonicalSelectedHandles m) := by
  intro u v h
  exact congrArg Prod.fst h

variable {X : Type*}
variable [AddCommGroup X] [Module (ZMod 2) X]

/-- Remaining topological data for the concrete family.

No field assumes independence of the reduced lattice columns. The two
independence facts that were separate hypotheses in the preceding bridge
are proved by `lensTwoCycles_subsingleton` and
`canonicalSelectedHandles_injective`.

The Gram data, exactness, and coefficient naturality must still be *produced*
by the specified 2-handlebody gluing, not assumed to be properties of knots
without a proof. -/
structure CanonicalGluingData (m : ℕ) (X : Type*)
    [AddCommGroup X] [Module (ZMod 2) X] where
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
  -- A relative Mayer--Vietoris segment, after identifying the lens-space
  -- degree-two cycles and the two handlebody homology groups.
  boundary : lensTwoCycles m →ₗ[ZMod 2] pieceHandleModule m
  inclusion : pieceHandleModule m →ₗ[ZMod 2] X
  exact_at_pieces : ∀ z, inclusion z = 0 → ∃ b, boundary b = z
  -- Donaldson plus the naturality of mod-two reduction for the *particular*
  -- selected integral handle classes. This is NOT an independent-family field.
  diagonal_coordinates : X ≃ₗ[ZMod 2] (Ambient m → ZMod 2)
  naturality : ∀ (r : Option (RootIndex m)) (j : Ambient m),
    diagonal_coordinates (inclusion
      (canonicalSelectedHandles m (Finsupp.single r 1))) j =
      (match r with
        | none => (Bheavy j : ZMod 2)
        | some i => (root i j : ZMod 2))

/-- Specialize the earlier standalone bridge to an actual cellular lens
boundary module and a canonical free basis of the two handlebodies. -/
noncomputable def CanonicalGluingData.toGluingData {m : ℕ}
    (d : CanonicalGluingData m X) :
    GluingData m (lensTwoCycles m) (pieceHandleModule m) X where
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
  boundary := d.boundary
  inclusion := d.inclusion
  exact_at_pieces := d.exact_at_pieces
  selected_handles := canonicalSelectedHandles m
  selected_handles_injective := canonicalSelectedHandles_injective m
  diagonal_coordinates := d.diagonal_coordinates
  naturality := d.naturality

/-- The refined relative endpoint: zero boundary cycles and independence of
selected pre-gluing handles are internal lemmas, not additional hypotheses. -/
theorem no_canonical_gluing_data {m : ℕ} (hm : m = 4 ∨ 6 ≤ m)
    (d : CanonicalGluingData m X) : False := by
  exact no_gluing_data hm d.toGluingData

end Trefoil.RelativeTopology
