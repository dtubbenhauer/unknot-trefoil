import Trefoil

/-! Diagnostic axiom audit and explicit theorem-interface guards.
The Python runner rejects any axiom beyond Lean's standard foundations.
These checks do not prove semantic fidelity or discharge missing bridges.
-/

#print axioms Trefoil.Arithmetic.partner_fraction
#print axioms Trefoil.Arithmetic.three_changes_infinity
#print axioms Trefoil.Arithmetic.plumbing_pair
#print axioms Trefoil.Arithmetic.even_pivot_signature
#print axioms Trefoil.Arithmetic.odd_pivot_signature
#print axioms Trefoil.LatticeBasics.norm_two_support_card
#print axioms Trefoil.LatticeBasics.odd_det_columns_independent_mod_two
#print axioms Trefoil.LatticePath.supports_form_path
#print axioms Trefoil.LatticeSupports.norm_two_chain_support_path
#print axioms Trefoil.LatticeSupports.dot_zero_iff_disjoint
#print axioms Trefoil.no_lattice_configuration
#print axioms Trefoil.LatticeSigns.signed_chain
#print axioms Trefoil.LatticeBlocks.exists_frame
#print axioms Trefoil.LatticeShapes.extract_rowA
#print axioms Trefoil.LatticeShapes.extract_rowB
#print axioms Trefoil.LatticeShapes.extract_rowC
#print axioms Trefoil.LatticeParity.mem_blockRootSpan_iff
#print axioms Trefoil.LatticeFrameParity.frame_B_not_mem
#print axioms Trefoil.LatticeExtraction.configuration_of_frame
#print axioms Trefoil.LatticeExtraction.no_embedding
#print axioms Trefoil.LatticeOddBasis.selected_columns_independent_mod_two
#print axioms Trefoil.LatticeOddBasis.of_odd_basis
#print axioms Trefoil.LatticeOddBasis.no_odd_basis_embedding
#print axioms Trefoil.Finite.candidates_complete
#print axioms Trefoil.Finite.scaled_correction_spec
#print axioms Trefoil.Finite.single_vector_obstructions
#print axioms Trefoil.Finite.doubling_obstruction
#print axioms Trefoil.Finite.no_reduced_correction_comparison
#print axioms Trefoil.Consequences.lower_bound_245
#print axioms Trefoil.Consequences.lower_bound_lattice
#print axioms Trefoil.Consequences.strict_saving
#print axioms Trefoil.Consequences.plumbing_saving
#print axioms Trefoil.Consequences.family_injective

-- A new premise in any core endpoint breaks these exact applications.
example : ∀ {m : ℕ}, (m = 4 ∨ 6 ≤ m) →
    Trefoil.LatticeEmbedding.Embedding m → False :=
  @Trefoil.LatticeExtraction.no_embedding
example : ∀ (m u : ℕ), (m = 4 ∨ 6 ≤ m) → 2 ≤ u →
    (u = 2 → Nonempty (Trefoil.LatticeEmbedding.Embedding m)) → 3 ≤ u :=
  Trefoil.Consequences.lower_bound_lattice
example : ∀ {m : ℤ}, (m = 4 ∨ 6 ≤ m) → Trefoil.LatticeConfiguration m → False :=
  @Trefoil.no_lattice_configuration
example : ∀ {h a s : ℤ}, Trefoil.Finite.ReducedForm h a s →
    ¬ Trefoil.Finite.HasCorrectionComparison h a s :=
  @Trefoil.Finite.no_reduced_correction_comparison

#print Trefoil.LatticeEmbedding.Embedding
#print Trefoil.LatticeConfiguration
#print Trefoil.Finite.ReducedForm
#print Trefoil.Finite.HasCorrectionComparison
#print Trefoil.Consequences.lower_bound_245
#print Trefoil.Consequences.lower_bound_lattice

/-!
## Literal model guards

Checking only a named endpoint type would not detect a stronger premise
hidden inside one of its input structures or predicates. These applications
fix the actual coordinate equations and comparison conditions. In particular,
an extra contradictory field or conjunct makes this audit fail to elaborate.
The statements below supply no obstruction conclusion as an assumption.
-/

namespace Trefoil.ModelAudit


open scoped BigOperators

-- Literal input guard for the pre-normalization endpoint. The ambient rank,
-- root families, Gram equations, and exact independence requirement are fixed
-- here, independently of the input structure's field projections.
def embeddingInputs :
    ∀ (m : ℕ)
      (root : (Fin (m-1) ⊕ (Fin 2 ⊕ Fin 2)) → (Fin (m+8) → ℤ))
      (A B C : Fin (m+8) → ℤ),
    (∀ r s, (∑ j, root r j * root s j) =
      if r = s then 2 else
        match r, s with
        | .inl i, .inl j => if i.val+1=j.val ∨ j.val+1=i.val then -1 else 0
        | .inr (.inl _), .inr (.inl _) => -1
        | _, _ => 0) →
    (∑ j, A j ^ 2) = 4 →
    (∑ j, B j ^ 2) = 6 →
    (∑ j, C j ^ 2) = 3 →
    (∑ j, A j * B j) = -1 →
    (∑ j, A j * C j) = 0 →
    (∑ j, B j * C j) = 0 →
    (∀ r, (∑ j, A j * root r j) =
      match r with
      | .inl i => if i.val+2=m then -1 else 0
      | _ => 0) →
    (∀ r, (∑ j, B j * root r j) =
      match r with
      | .inr (.inl i) => if i.val=0 then -1 else 0
      | _ => 0) →
    (∀ r, (∑ j, C j * root r j) =
      match r with
      | .inr (.inl i) => if i.val=1 then -1 else 0
      | _ => 0) →
    LinearIndependent (ZMod 2)
      (fun r : Option (Fin (m-1) ⊕ (Fin 2 ⊕ Fin 2)) =>
        match r with
        | none => fun j => (B j : ZMod 2)
        | some i => fun j => (root i j : ZMod 2)) →
    Trefoil.LatticeEmbedding.Embedding m :=
  @Trefoil.LatticeEmbedding.Embedding.mk

-- The stronger basis-matrix endpoint cannot acquire a separate independence
-- or coordinate-normalization premise without changing this guarded type.
open LatticeEmbedding LatticeSupports in
def oddBasisObstructionInputs :
    ∀ {m : ℕ}, (m = 4 ∨ 6 ≤ m) →
    ∀ (M : Matrix (Ambient m) (Ambient m) ℤ), Odd M.det →
    ∀ (choose : Option (RootIndex m) → Ambient m),
    Function.Injective choose → ∀ (A C : Vector m),
    (∀ r s, dot (M.col (choose (some r))) (M.col (choose (some s))) = rootGram r s) →
    (∑ j, A j ^ 2) = 4 →
    (∑ j, M.col (choose none) j ^ 2) = 6 →
    (∑ j, C j ^ 2) = 3 →
    dot A (M.col (choose none)) = -1 →
    dot A C = 0 →
    dot (M.col (choose none)) C = 0 →
    (∀ r, dot A (M.col (choose (some r))) = aRootPairing r) →
    (∀ r, dot (M.col (choose none)) (M.col (choose (some r))) = bRootPairing r) →
    (∀ r, dot C (M.col (choose (some r))) = cRootPairing r) → False :=
  @LatticeOddBasis.no_odd_basis_embedding

-- Every constructor argument is specified independently of the structure's
-- field projections. An added or changed premise breaks this application.
def latticeConfigurationInputs :
    ∀ (m a b c z g ell rA sA tA rB sB tB rC sC tC : ℤ),
    m * a^2 + 2*a + 1 + 3*z^2 + 2*rA^2 + 2*sA^2 + tA^2 = 4 →
    m * b^2 + (g-1)^2 + 2*g^2 + 2*rB^2 + 2*sB^2 + tB^2 = 6 →
    m * c^2 + 2*ell^2 + (ell+1)^2 + 2*rC^2 + 2*sC^2 + tC^2 = 3 →
    (m*a+1)*b + z*(3*g-1) + 2*(rA*rB+sA*sB) + tA*tB = -1 →
    (m*a+1)*c + z*(3*ell+1) + 2*(rA*rC+sA*sC) + tA*tC = 0 →
    m*b*c + 3*g*ell + g-ell + 2*(rB*rC+sB*sC) + tB*tC = 0 →
    (¬ ((m*b)%2 = 0 ∧ (3*g-1)%2 = 0 ∧ tB%2 = 0)) →
    Trefoil.LatticeConfiguration m :=
  @Trefoil.LatticeConfiguration.mk

theorem reducedFormDefinition (h a s : ℤ) :
    Trefoil.Finite.ReducedForm h a s ↔
      (0 ≤ a ∧ a < h ∧ h ≤ s ∧ h % 2 = 0 ∧ s % 2 = 0 ∧
        (2*h-1)*(2*s-1)-4*a^2 = 245) := Iff.rfl

theorem surgeryMatrixDefinition (h a s : ℤ) :
    Trefoil.Finite.surgeryMatrix h a s =
      (![![(h : ℚ), 1, (a : ℚ), 0], ![1, 2, 0, 0],
         ![(a : ℚ), 0, (s : ℚ), 1], ![0, 0, 1, 2]] :
        Matrix (Fin 4) (Fin 4) ℚ) := rfl

theorem quadraticBoundDefinition (x : Fin 4 → ℤ) (z : Fin 4 → ℚ) :
    Trefoil.Finite.quadraticBound x z =
      (∑ i : Fin 4, (x i : ℚ) * z i) - 1 := rfl

-- The right side spells out doubling, the characteristic-vector scale,
-- the spin shift, orientation parameters, and every quantified test vector.
theorem correctionComparisonDefinition (h a s : ℤ) :
    Trefoil.Finite.HasCorrectionComparison h a s ↔
      (∃ label : (Fin 4 → ℤ) → Fin 245,
        (∀ x, label (x + x) =
          (⟨(2 * (label x).val) % 245,
            Nat.mod_lt _ (by decide)⟩ : Fin 245)) ∧
        ∀ (x : Fin 4 → ℤ) (z : Fin 4 → ℚ),
          (Trefoil.Finite.surgeryMatrix h a s).mulVec z =
            (fun i => (x i : ℚ)) →
          ∃ n : ℕ,
            ((∑ i : Fin 4, (x i : ℚ) * z i) - 1) -
              Trefoil.Finite.correctionTerm 245 141
                ((70 + (label x).val) % 245) = 2 * (n : ℚ)) := Iff.rfl

-- The entire recursive recipe is guarded, rather than only the name of
-- a table-producing function whose implementation might later change.
theorem correctionRecurrence (p q i : ℕ) :
    Trefoil.Finite.correctionTerm p q i =
      if q = 0 then 0 else
        ((p : ℚ) * q - (2 * (i : ℚ) + 1 - p - q)^2) / (4 * p * q) -
          Trefoil.Finite.correctionTerm q (p % q) (i % q) := by
  rw [Trefoil.Finite.correctionTerm]
  by_cases hq : q = 0 <;> simp [hq]

end Trefoil.ModelAudit
