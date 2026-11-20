import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Module.ZMod
import Mathlib.LinearAlgebra.StdBasis
import Lean.Elab.Tactic.Omega

/-!
# Coefficient reduction for Section 3A

The coefficient maps and their kernel and image are inputs from the
homology coefficient sequence. Given these inputs, integral coordinates
induce mod-two coordinates and transfer Mayer–Vietoris injectivity to the
columns of the integral inclusion.
-/

namespace Trefoil.Section3ACoefficients

variable {ι : Type*} {I M : Type*}
variable [AddCommGroup I] [Module ℤ I] [AddCommGroup M]

/-- Pointwise coefficient reduction in a chosen integral basis. -/
def coordinateReduction (coordinates : I ≃ₗ[ℤ] (ι → ℤ)) :
    I →+ (ι → ZMod 2) where
  toFun x i := (coordinates x i : ZMod 2)
  map_zero' := by ext i; simp
  map_add' := by intro x y; ext i; simp

theorem coordinateReduction_apply (coordinates : I ≃ₗ[ℤ] (ι → ℤ)) (x : I) (i : ι) :
    coordinateReduction coordinates x i = (coordinates x i : ZMod 2) := rfl

theorem coordinateReduction_surjective (coordinates : I ≃ₗ[ℤ] (ι → ℤ)) :
    Function.Surjective (coordinateReduction coordinates) := by
  intro v
  refine ⟨coordinates.symm (fun i => (v i).val), ?_⟩
  ext i
  simp [coordinateReduction_apply]

theorem coordinateReduction_eq_zero (coordinates : I ≃ₗ[ℤ] (ι → ℤ)) (x : I) :
    coordinateReduction coordinates x = 0 ↔ ∃ y, x = y + y := by
  constructor
  · intro h
    refine ⟨coordinates.symm (fun i => coordinates x i / 2), coordinates.injective ?_⟩
    simp only [map_add, LinearEquiv.apply_symm_apply]
    funext i
    change coordinates x i = coordinates x i / 2 + coordinates x i / 2
    have hi : (coordinates x i : ZMod 2) = 0 := congrFun h i
    have hdvd := (ZMod.intCast_zmod_eq_zero_iff_dvd (coordinates x i) 2).mp hi
    omega
  · rintro ⟨y, rfl⟩
    funext i
    simp only [map_add, Pi.add_apply, Pi.zero_apply, coordinateReduction_apply]
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).mpr
      ⟨coordinates y i, by omega⟩

private theorem coordinateReduction_eq_iff (coordinates : I ≃ₗ[ℤ] (ι → ℤ))
    (reduce : I →+ M) (kernel : ∀ x, reduce x = 0 ↔ ∃ y, x = y + y) (x y : I) :
    coordinateReduction coordinates x = coordinateReduction coordinates y ↔
      reduce x = reduce y := by
  rw [← sub_eq_zero, ← sub_eq_zero (a := reduce x), ← map_sub, ← map_sub]
  exact (coordinateReduction_eq_zero coordinates _).trans (kernel _).symm

private theorem reductionKernel_le (coordinates : I ≃ₗ[ℤ] (ι → ℤ))
    (reduce : I →+ M) (kernel : ∀ x, reduce x = 0 ↔ ∃ y, x = y + y) :
    reduce.ker ≤ (coordinateReduction coordinates).ker := by
  intro x hx
  exact (coordinateReduction_eq_zero coordinates x).mpr ((kernel x).mp hx)

private noncomputable def descendedReduction (coordinates : I ≃ₗ[ℤ] (ι → ℤ))
    (reduce : I →+ M) (surj : Function.Surjective reduce)
    (kernel : ∀ x, reduce x = 0 ↔ ∃ y, x = y + y) : M →+ (ι → ZMod 2) :=
  reduce.liftOfSurjective surj ⟨coordinateReduction coordinates, reductionKernel_le coordinates reduce kernel⟩

private theorem descendedReduction_apply (coordinates : I ≃ₗ[ℤ] (ι → ℤ))
    (reduce : I →+ M) (surj : Function.Surjective reduce)
    (kernel : ∀ x, reduce x = 0 ↔ ∃ y, x = y + y) (x : I) :
    descendedReduction coordinates reduce surj kernel (reduce x) = coordinateReduction coordinates x := by
  simp [descendedReduction]

variable [Module (ZMod 2) M]

/-- An integral basis descends to mod-two coordinates whenever reduction is
surjective with kernel equal to the doubles. -/
noncomputable def reductionLinearEquiv (coordinates : I ≃ₗ[ℤ] (ι → ℤ))
    (reduce : I →+ M) (surj : Function.Surjective reduce)
    (kernel : ∀ x, reduce x = 0 ↔ ∃ y, x = y + y) : M ≃ₗ[ZMod 2] (ι → ZMod 2) := by
  let f := (descendedReduction coordinates reduce surj kernel).toZModLinearMap 2
  have hf (x : I) : f (reduce x) = coordinateReduction coordinates x :=
    descendedReduction_apply coordinates reduce surj kernel x
  apply LinearEquiv.ofBijective f
  constructor
  · intro x y h
    obtain ⟨u, rfl⟩ := surj x
    obtain ⟨v, rfl⟩ := surj y
    rw [hf, hf] at h
    exact (coordinateReduction_eq_iff coordinates reduce kernel u v).mp h
  · intro v
    obtain ⟨x, hx⟩ := coordinateReduction_surjective coordinates v
    exact ⟨reduce x, (hf x).trans hx⟩

/-- The descended coordinates send reduced integral classes to the reductions of
their integral coordinate vectors. -/
theorem reductionLinearEquiv_apply (coordinates : I ≃ₗ[ℤ] (ι → ℤ))
    (reduce : I →+ M) (surj : Function.Surjective reduce)
    (kernel : ∀ x, reduce x = 0 ↔ ∃ y, x = y + y) (x : I) (i : ι) :
    reductionLinearEquiv coordinates reduce surj kernel (reduce x) i =
      (coordinates x i : ZMod 2) :=
  congrFun (descendedReduction_apply coordinates reduce surj kernel x) i

section Inclusion

variable {β κ : Type*} [DecidableEq β]
variable {P X P₂ X₂ : Type*}
variable [AddCommGroup P] [Module ℤ P] [AddCommGroup X] [Module ℤ X]
variable [AddCommGroup P₂] [Module (ZMod 2) P₂] [AddCommGroup X₂] [Module (ZMod 2) X₂]

/-- An injective inclusion modulo two makes the reduced columns of the
integral inclusion independent. Naturality is required only for the ordinary
coefficient and inclusion maps. -/
theorem reduced_columns_independent
    (pieceCoordinates : P ≃ₗ[ℤ] (β → ℤ)) (closedCoordinates : X ≃ₗ[ℤ] (κ → ℤ))
    (includeIntegral : P →ₗ[ℤ] X) (includeModTwo : P₂ →ₗ[ZMod 2] X₂)
    (pieceReduce : P →+ P₂) (pieceSurj : Function.Surjective pieceReduce)
    (pieceKernel : ∀ x, pieceReduce x = 0 ↔ ∃ y, x = y + y)
    (closedReduce : X →+ X₂) (closedSurj : Function.Surjective closedReduce)
    (closedKernel : ∀ x, closedReduce x = 0 ↔ ∃ y, x = y + y)
    (natural : ∀ x, closedReduce (includeIntegral x) = includeModTwo (pieceReduce x))
    (injective : Function.Injective includeModTwo) (selected : ι → β)
    (selected_injective : Function.Injective selected) :
    LinearIndependent (ZMod 2) (fun i : ι => fun j : κ =>
      (closedCoordinates (includeIntegral (pieceCoordinates.symm
        (Pi.single (selected i) (1 : ℤ)))) j : ZMod 2)) := by
  let eP := reductionLinearEquiv pieceCoordinates pieceReduce pieceSurj pieceKernel
  let eX := reductionLinearEquiv closedCoordinates closedReduce closedSurj closedKernel
  let f := eX.toLinearMap.comp (includeModTwo.comp eP.symm.toLinearMap)
  have hf : Function.Injective f := eX.injective.comp (injective.comp eP.symm.injective)
  have hind := ((Pi.linearIndependent_single_one β (ZMod 2)).comp
    selected selected_injective).map' f (LinearMap.ker_eq_bot.mpr hf)
  have hval (i : ι) :
      eP (pieceReduce (pieceCoordinates.symm (Pi.single (selected i) (1 : ℤ)))) =
        Pi.single (selected i) (1 : ZMod 2) := by
    funext j
    dsimp only [eP]
    rw [reductionLinearEquiv_apply, LinearEquiv.apply_symm_apply]
    by_cases h : j = selected i
    · subst j
      simp
    · simp [Pi.single_eq_of_ne h]
  have hcolumns (i : ι) (j : κ) :
      f (Pi.single (selected i) (1 : ZMod 2)) j =
        (closedCoordinates (includeIntegral (pieceCoordinates.symm
          (Pi.single (selected i) (1 : ℤ)))) j : ZMod 2) := by
    rw [← hval i]
    change eX (includeModTwo (eP.symm (eP (pieceReduce (pieceCoordinates.symm
      (Pi.single (selected i) (1 : ℤ))))))) j = _
    rw [LinearEquiv.symm_apply_apply, ← natural]
    exact reductionLinearEquiv_apply closedCoordinates closedReduce closedSurj closedKernel _ j
  have heq :
      (f ∘ fun i : ι => Pi.single (selected i) (1 : ZMod 2)) =
        (fun i : ι => fun j : κ => (closedCoordinates (includeIntegral (pieceCoordinates.symm
          (Pi.single (selected i) (1 : ℤ)))) j : ZMod 2)) :=
    funext fun i => funext (hcolumns i)
  exact heq ▸ hind

end Inclusion

end Trefoil.Section3ACoefficients
