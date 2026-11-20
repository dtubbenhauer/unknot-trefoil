import Trefoil.Section3ATopology
import Trefoil.Section3BMinimum

/-!
# Section 3B: the determinant-245 knot

The reference interface uses correction terms of the oriented cover in
spin-centered coordinates. The Ozsváth–Szabó recursion uses its own raw
lens-space labels. The proof identifies the spin label and transports the
correction terms between those conventions.
-/

namespace Trefoil.Section3BTopology

open Trefoil.Section3ATopology
open Trefoil.Section3ASignature
open Trefoil.Section3BMinimum

/-- General lens-space and Floer inputs, with the correction term attached
to the oriented three-manifold. In each lens-space identification, `ZMod p`
acts on Spin-c structures from the unique spin structure as origin. -/
structure FloerReferences (T : Geometry) where
  alternating : T.Knot → Prop
  twoBridge_alternating : ∀ (p q : ℕ), Odd p →
    0 < q → q < p → Nat.Coprime p q → alternating (T.twoBridge p q)
  /-- The last surgery coefficient identifies the chart used for the
  cyclic coordinate. Equivalent surgery presentations can use different
  generators in first cohomology. -/
  correction : T.Three → (p t : ℕ) → ZMod p → ℚ
  /-- The position of the raw Ozsváth–Szabó index on the cyclic Spin-c
  torsor, expressed in spin-centered coordinates for the reversed lens space. -/
  rawLensLabel : (p t : ℕ) → Fin p → ZMod p
  /-- Consecutive raw indices differ by a fixed generator. Choose it as
  the generator for the centered cyclic labels. -/
  rawLabel_difference : ∀ p t, Odd p → 0 < t → t < p → Nat.Coprime p t →
    ∀ i k : Fin p,
      rawLensLabel p t i - rawLensLabel p t k = (i.val : ZMod p) - (k.val : ZMod p)
  /-- Conjugation sends the raw index i to p+t−1−i modulo p and negates
  the centered coordinate. Here only its action at a fixed point is needed. -/
  rawLabel_fixed_conjugation : ∀ p t, Odd p → 0 < t → t < p → Nat.Coprime p t →
    ∀ i : Fin p, (2 * i.val) % p = (p + t - 1) % p →
      rawLensLabel p t i = -rawLensLabel p t i
  /-- Ozsváth–Szabó, Proposition 4.8, in the `-L(p,t)` orientation. -/
  osz_negative_lens : ∀ p t, Odd p → 0 < t → t < p → Nat.Coprime p t →
    ∀ i : Fin p, correction (T.reverse (T.lens p t)) p t (rawLensLabel p t i) =
      Trefoil.Finite.correctionTerm p t i.val
  /-- The minimum function of the positive Goeritz matrix of a chosen
  alternating diagram, using the boundary Spin-c labeling. -/
  goeritzMinimum : T.Knot → (p t : ℕ) → ZMod p → ℚ
  /-- Sharpness of the positive Goeritz filling with boundary oriented
  as the double cover. This is the convention in Owens, Section 4. -/
  goeritz_sharp : ∀ (K : T.Knot) (p q : ℕ),
    alternating K → T.doubleCover K = T.lens p q →
    Odd p → 0 < q → q < p → Nat.Coprime p q →
    ∀ j, goeritzMinimum K p (p - q) j = correction (T.doubleCover K) p (p - q) j
  /-- Owens, Theorem 1, for signature four and two negative changes.
  The order of first homology of the lens-space cover is the determinant
  of the knot. The `m_Q` comparison is with `m_G` on the same diagram;
  its replacement by the correction term uses `goeritz_sharp`. -/
  owens_alternating : ∀ (K : T.Knot) (p q : ℕ),
    alternating K → T.signature K = 4 → T.crossingChanges K 0 2 →
    T.doubleCover K = T.lens p q →
    Odd p → 0 < q → q < p → Nat.Coprime p q →
    ∃ h a s : ℤ, 0 ≤ a ∧ a < h ∧ h ≤ s ∧ Even h ∧ Even s ∧
      Matrix.det (surgeryMatrixZ h a s) = (p : ℤ) ∧
      Nonempty (OwensMinimum p h a s (goeritzMinimum K p (p - q)))

variable {T : Geometry}

/-- Raw index 70 is spin. The raw fixed-point equation is checked in the
paper's numbering, and multiplication by two is invertible modulo 245. -/
theorem raw_spin_245 (F : FloerReferences T) :
    F.rawLensLabel 245 141 (70 : Fin 245) = 0 := by
  have hfixed : (2 * (70 : Fin 245).val) % 245 = (245 + 141 - 1) % 245 :=
    (Trefoil.Arithmetic.spin_label_unique (70 : Fin 245)).mpr rfl
  have h := F.rawLabel_fixed_conjugation 245 141
    (by decide) (by decide) (by decide) (by decide) (70 : Fin 245) hfixed
  let l := F.rawLensLabel 245 141 (70 : Fin 245)
  have htwo : (2 : ZMod 245) * l = 0 := by
    calc
      2 * l = l + l := two_mul l
      _ = -l + l := congrArg (fun x => x + l) h
      _ = 0 := neg_add_cancel l
  have hinverse : (123 : ZMod 245) * 2 = 1 := by decide
  change l = 0
  rw [← one_mul l, ← hinverse, mul_assoc, htwo, mul_zero]

/-- The labeled recursion on `-L(245,141)` gives the correction terms of
the actual positive-surgery lens space after the spin shift. -/
theorem oriented_correction_245 (R : References T) (F : FloerReferences T)
    (j : ZMod 245) :
    F.correction (T.lens 245 104) 245 141 j = lensCorrection 245 104 j := by
  have hreverse : T.lens 245 104 = T.reverse (T.lens 245 141) :=
    R.lens_reverse 245 141 (by decide) (by decide) (by decide)
  let i : Fin 245 := ⟨(70 + j.val) % 245, Nat.mod_lt _ (by decide)⟩
  have hi : (i.val : ZMod 245) = 70 + j := by
    change ((((70 : ℕ) + j.val) % 245 : ℕ) : ZMod 245) = _
    rw [ZMod.natCast_mod, Nat.cast_add, ZMod.natCast_zmod_val]
    rfl
  have hd := F.rawLabel_difference 245 141
    (by decide) (by decide) (by decide) (by decide) i (70 : Fin 245)
  have hlabel : F.rawLensLabel 245 141 i = j := by
    have hcast : (((70 : Fin 245).val : ℕ) : ZMod 245) = 70 := by decide
    simpa only [raw_spin_245, sub_zero, hi, hcast, add_sub_cancel_left] using hd
  calc
    F.correction (T.lens 245 104) 245 141 j =
        F.correction (T.reverse (T.lens 245 141)) 245 141 (F.rawLensLabel 245 141 i) := by
      rw [hreverse, hlabel]
    _ = Trefoil.Finite.correctionTerm 245 141 i.val :=
      F.osz_negative_lens 245 141 (by decide) (by decide) (by decide) (by decide) i
    _ = lensCorrection 245 104 j := by
      change Trefoil.Finite.correctionTerm 245 141 ((70 + j.val) % 245) =
        Trefoil.Finite.correctionTerm 245 141 ((spinBase 245 104 + j.val) % 245)
      rw [spinBase_245]

/-- The oriented partner has signature four and double cover `L(245,104)`.
Owens's obstruction for two negative crossing changes specializes to the
five-form contradiction. -/
theorem section3B_oriented_lower_bound (R : References T) (F : FloerReferences T) :
    3 ≤ T.unknotting (orientedPartner T 2) := by
  by_contra! hu
  have hsig : T.signature (orientedPartner T 2) = 4 := by
    simpa only [orientedPartner] using partner_signature_four R.sig 2 (by decide)
  have hchanges : T.crossingChanges (orientedPartner T 2) 0 2 :=
    two_negative_changes R (m := 2) (by decide) hu
  have hcover : T.doubleCover (orientedPartner T 2) = T.lens 245 104 := by
    simpa only [orientedPartner] using R.bridge_cover 245 104
      (by decide) (by decide) (by decide) (by decide)
  have halt : F.alternating (orientedPartner T 2) := by
    change F.alternating (T.twoBridge 245 104)
    exact F.twoBridge_alternating 245 104 (by decide) (by decide) (by decide) (by decide)
  obtain ⟨h, a, s, ha, hah, hhs, he, se, hd, ⟨w⟩⟩ :=
    F.owens_alternating (orientedPartner T 2) 245 104
      halt hsig hchanges hcover (by decide) (by decide) (by decide) (by decide)
  have hred : ReducedAt 245 h a s := by
    refine ⟨ha, hah, hhs, ?_, ?_, ?_⟩
    · obtain ⟨k, hk⟩ := he
      omega
    · obtain ⟨k, hk⟩ := se
      omega
    · simpa only [surgeryMatrixZ_det] using hd
  apply no_owens_minimum_245 hred
  apply w.changeCorrection
  intro j
  calc
    F.goeritzMinimum (orientedPartner T 2) 245 141 j =
        F.correction (T.doubleCover (orientedPartner T 2)) 245 141 j :=
      F.goeritz_sharp _ _ 104 halt hcover (by decide) (by decide) (by decide) (by decide) j
    _ = lensCorrection 245 104 j := by rw [hcover, oriented_correction_245 R F]

/-- Pass to the paper's Conway knot by mirror invariance. -/
theorem section3B_lower_bound (R : References T) (F : FloerReferences T) :
    3 ≤ T.unknotting (partner T 2) := by
  have hu := section3B_oriented_lower_bound R F
  have hpositive : ∀ a ∈ [(2 : ℤ), 2, 1, 4, 3, 2], 0 < a := by decide
  have hfrac : Trefoil.Arithmetic.plusPair [(2 : ℤ), 2, 1, 4, 3, 2] =
      ((245 : ℤ), (104 : ℤ)) := by
    norm_num [Trefoil.Arithmetic.plusPair]
  rcases R.conway_fraction [(2 : ℤ), 2, 1, 4, 3, 2] 245 104
      (by decide) hpositive hfrac (by decide) (by decide) (by decide) with h | h
  · change partner T 2 = orientedPartner T 2 at h
    rwa [h]
  · change T.mirror (partner T 2) = orientedPartner T 2 at h
    simpa only [← h, R.mirror_unknotting] using hu

end Trefoil.Section3BTopology
