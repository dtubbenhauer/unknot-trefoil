import Trefoil.LatticeExtraction

/-!
# Section 3A: standalone relative Mayer--Vietoris assembly

This file is the first homology-level stage of the Section 3A development.
It imports the Trefoil lattice obstruction.

The topology input is stated at the homology level. In particular:
* the paper's local plumbing / Owens linking pairings are supplied explicitly;
* a two-handlebody basis gives an injective map on mod-two classes BEFORE gluing;
* Mayer--Vietoris exactness and a vanishing H₂ of the common boundary imply that
  this map stays injective AFTER gluing;
* the reduction compatibility with Donaldson's integral coordinates is required.

NO field assumes mod-two independence of the resulting integral columns, an odd
index, a Gram-matrix determinant, a coordinate normal form or the obstruction.

The later relative stages separate out the tasks of constructing the
homology comparisons and the integral coordinates.
-/

namespace Trefoil.RelativeTopology

open Trefoil.LatticeEmbedding Trefoil.LatticeSupports
open scoped BigOperators

/-! The cellular differential d₂ of L(p,q) is multiplication by p.
    We verify its mod-two algebra here; the topological CW identification
    itself is an external standard-topology input. -/

/-- The lens-space cellular boundary scalar is one modulo two. -/
theorem lens_boundary_scalar (m : ℕ) :
    ((104 * m + 37 : ℕ) : ZMod 2) = 1 := by
  have hp : 104 * m + 37 = 2 * (52 * m + 18) + 1 := by omega
  rw [hp]
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_one, ZMod.natCast_self,
    zero_mul, zero_add]

/-- The cellular d₂ has zero kernel over F₂. -/
theorem lens_cellular_kernel_zero (m : ℕ) (x : ZMod 2)
    (hx : ((104 * m + 37 : ℕ) : ZMod 2) * x = 0) : x = 0 := by
  simpa [lens_boundary_scalar m] using hx

/-- The same cellular d₂ is surjective over F₂. -/
theorem lens_cellular_boundary_surjective (m : ℕ) :
    Function.Surjective (fun x : ZMod 2 =>
      ((104 * m + 37 : ℕ) : ZMod 2) * x) := by
  intro y
  refine ⟨y, ?_⟩
  simp [lens_boundary_scalar m]

variable {B P X : Type*}
variable [AddCommGroup B] [AddCommGroup P] [AddCommGroup X]
variable [Module (ZMod 2) B] [Module (ZMod 2) P] [Module (ZMod 2) X]

/-- Precisely the geometric input still required to connect the given knot
and two handlebody pieces to the previously verified lattice obstruction.
The initial Gram fields are local linking-number data; the remaining fields
are independent standard homology and coefficient-transport inputs. -/
structure GluingData (m : ℕ) (B P X : Type*)
    [AddCommGroup B] [AddCommGroup P] [AddCommGroup X]
    [Module (ZMod 2) B] [Module (ZMod 2) P] [Module (ZMod 2) X] where
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
  -- MV segment H₂(Y;F₂) → H₂(G;F₂)⊕H₂(W;F₂) → H₂(X;F₂).
  boundary : B →ₗ[ZMod 2] P
  inclusion : P →ₗ[ZMod 2] X
  exact_at_pieces : ∀ z : P, inclusion z = 0 → ∃ b : B, boundary b = z
  -- This is the injective restriction of the standard handlebody basis map.
  -- It lives in the DISJOINT pieces, before Mayer--Vietoris is applied.
  selected_handles : (Option (RootIndex m) →₀ ZMod 2) →ₗ[ZMod 2] P
  selected_handles_injective : Function.Injective selected_handles
  -- Coordinates supplied by Donaldson and reduction of an integral isometry.
  diagonal_coordinates : X ≃ₗ[ZMod 2] (Ambient m → ZMod 2)
  -- Naturality of coefficient reduction for the selected actual handle classes.
  naturality : ∀ (r : Option (RootIndex m)) (j : Ambient m),
    diagonal_coordinates (inclusion
      (selected_handles (Finsupp.single r 1))) j =
      (match r with
        | none => (Bheavy j : ZMod 2)
        | some i => (root i j : ZMod 2))

/-- Mayer--Vietoris exactness and zero boundary H₂ force injectivity of the
inclusion map of the two handlebodies. -/
theorem GluingData.inclusion_injective {m : ℕ}
    (d : GluingData m B P X) [Subsingleton B] :
    Function.Injective d.inclusion := by
  intro u v huv
  have hz : d.inclusion (u - v) = 0 := by
    simp [map_sub, huv]
  obtain ⟨b, hb⟩ := d.exact_at_pieces (u - v) hz
  have hb0 : b = 0 := Subsingleton.elim b 0
  rw [hb0, map_zero] at hb
  exact sub_eq_zero.mp hb.symm

/-- The selected *integral* columns are independent modulo two. This is
proved from the MV exact sequence and functorial reduction, not postulated
as a topological input. -/
theorem GluingData.selected_independent {m : ℕ}
    (d : GluingData m B P X) [Subsingleton B] :
    LinearIndependent (ZMod 2)
      (fun r : Option (RootIndex m) =>
        match r with
        | none => fun j => (d.Bheavy j : ZMod 2)
        | some i => fun j => (d.root i j : ZMod 2)) := by
  classical
  let f : (Option (RootIndex m) →₀ ZMod 2) →ₗ[ZMod 2]
      (Ambient m → ZMod 2) :=
    d.diagonal_coordinates.toLinearMap.comp
      (d.inclusion.comp d.selected_handles)
  have hf : Function.Injective f := by
    intro u v huv
    apply d.selected_handles_injective
    apply d.inclusion_injective
    apply d.diagonal_coordinates.injective
    simpa [f] using huv
  have h_basis : LinearIndependent (ZMod 2)
      (fun r : Option (RootIndex m) => Finsupp.single r (1 : ZMod 2)) := by
    rw [linearIndependent_iff_injective_finsuppLinearCombination]
    have h_id : (Finsupp.linearCombination (ZMod 2)
        (fun r : Option (RootIndex m) => Finsupp.single r (1 : ZMod 2))) = LinearMap.id := by
      apply Finsupp.lhom_ext
      intro r c
      simp [Finsupp.smul_single, smul_eq_mul]
    rw [h_id]
    exact fun _ _ h => h
  have h : LinearIndependent (ZMod 2)
      (fun r : Option (RootIndex m) => f (Finsupp.single r 1)) := by
    change LinearIndependent (ZMod 2) (f ∘ fun r => Finsupp.single r 1)
    rw [linearIndependent_iff_injective_finsuppLinearCombination,
      Finsupp.linearCombination_linear_comp]
    exact hf.comp h_basis
  have hEq :
      (fun r : Option (RootIndex m) => f (Finsupp.single r 1)) =
      (fun r : Option (RootIndex m) =>
        match r with
        | none => fun j => (d.Bheavy j : ZMod 2)
        | some i => fun j => (d.root i j : ZMod 2)) := by
    funext r j
    cases r <;> exact d.naturality _ j
  rw [hEq] at h
  exact h

/-- Internal construction of the `Embedding` object from separate geometric
pairings and the *derived* mod-two independence. -/
noncomputable def GluingData.toEmbedding {m : ℕ}
    (d : GluingData m B P X) [Subsingleton B] :
    Trefoil.LatticeEmbedding.Embedding m where
  root := d.root
  A := d.A
  B := d.Bheavy
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
  independent := d.selected_independent

/-- Shortest standalone end-to-end *relative* theorem for Section 3A.
No experimental Gram/determinant/triangular module is imported. -/
theorem no_gluing_data {m : ℕ} (hm : m = 4 ∨ 6 ≤ m)
    (d : GluingData m B P X) [Subsingleton B] : False := by
  exact Trefoil.LatticeExtraction.no_embedding hm d.toEmbedding

end Trefoil.RelativeTopology
