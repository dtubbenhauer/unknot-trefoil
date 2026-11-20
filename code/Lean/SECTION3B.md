# Section 3B and the unified lower bound

`Trefoil.Section3BTopology.section3B_lower_bound` gives `3 ≤ u(P_2)`.
`Trefoil.Section3LowerBound.section3_lower_bound` combines it with Section 3A:

```lean
∀ {T : Geometry}, References T → FloerReferences T →
  ∀ {m : ℕ}, (m = 2 ∨ m = 4 ∨ 6 ≤ m) →
    3 ≤ T.unknotting (partner T m)
```

The result is relative to the cited topology and Floer theorems. A realization
of the generic interfaces in a concrete Lean model of knots, smooth manifolds
and Heegaard Floer theory remains outside this project.

## Proof map

| Manuscript step | Lean declaration |
| --- | --- |
| The Conway diagram at `m=2` has fraction `245/104`. Its chirality with positive surgery as cover has signature four. A shortest unknotting in fewer than three changes would use exactly two negative changes. | `Section3BTopology.section3B_lower_bound`, `section3B_oriented_lower_bound`, and the inherited `partner_signature_four` and `two_negative_changes` |
| For the alternating partner, Owens supplies a four-by-four integral form and one comparison map. The determinant and even weights give the reduced equations. | `FloerReferences.owens_alternating`, `Section3BMinimum.surgeryMatrixZ_det`, and `ReducedAt` |
| The positive Goeritz minimum equals the correction term for the oriented double cover. | `FloerReferences.goeritz_sharp`, applied inside `section3B_oriented_lower_bound` |
| Positive `245/104` surgery is `−L(245,141)`. The spin origin is raw label `70`, and the centered residue `j` uses raw index `(70+j) mod 245`. | `Section3BTopology.raw_spin_245`, `oriented_correction_245`, and `Section3BMinimum.lensCorrection_245` |
| The relevant characteristic covectors are exactly `2x`, with value `xᵀQ⁻¹x−1`. Doubling acts invertibly on the odd-order class group. | `characteristic_iff_twice`, `doubled_characteristic_value`, and `doubleClassesEquiv` |
| Changing a representative by `Qy` changes the value by `2 yᵀx + yᵀQy`, an even integer. Attainment and minimality make the gap from the minimum nonnegative. | `quadraticBound_translate`, `quadraticBound_translate_even`, and `OwensMinimum.minimizing_even_difference` |
| Transfer Owens's minimum comparison to every test vector. The same map controls the labels of `x` and `x+x`. | `minimum_to_comparison`, with `OwensMinimum.label` given by the quotient and the single additive isomorphism |
| Exclude the five reduced forms, and transfer the lower bound to the actual Conway knot up to mirror. | `no_owens_minimum_245`, `Finite.no_reduced_correction_comparison`, and `section3B_lower_bound` |

The inherited finite proof handles `(4,0,18)` by an explicit correction-term
test at `(-1,0,0,0)` with bound `-5/7`. For `(2,1,42)` it checks the two
tests for every cyclic label related by doubling. These stronger finite tests
supply the contradiction without using the manuscript's separate cyclicity
exclusion or its calculation restricted to unit multipliers. The conclusion
is the same lower bound on the same knot.

## Reference audit

The inputs below apply uniformly to knots or reduced lens-space charts.
Their sources and orientation conventions are expanded in
[literature-inputs.md](literature-inputs.md).

- `twoBridge_alternating` uses a reduced fraction with odd numerator and
  positive denominator smaller than the numerator. The odd-numerator
  condition gives a knot. An alternating Conway presentation exists in
  either chirality.
- `owens_alternating` applies Theorem 1 for an alternating knot with two
  negative changes and signature four. Owens requires two changes in
  total and a negative count of half the signature. The form and its
  determinant come from the theorem, with the determinant identified
  with the order of first homology of the cover. The standard lens-space
  homology identifies that order with `p`.
- `OwensMinimum` has the actual quotient by the image of the integral
  surgery matrix, one additive isomorphism to the cyclic group,
  and a characteristic minimum with attainment and minimality. Owens's
  convention may label `2x` by its class `[2x]`. Composing the class
  isomorphism with the checked odd-order doubling automorphism gives the
  labeling by the half-vector `[x]` used here. The even-integer difference
  for a general representative is a conclusion of the Lean proof.
- `goeritz_sharp` is the positive Goeritz sharp-filling statement for the
  chosen alternating diagram, with its boundary oriented as `Σ(K)`.
  The comparison to `m_G` and the conversion from `m_G` to `d(Σ(K),·)`
  use the same positive Goeritz labeling.
- `osz_negative_lens` supplies the Ozsváth–Szabó recursion at raw indices
  `0 ≤ i < p` of the reversed lens space. Its slope hypotheses are
  `0 < t < p` and coprimality. The record restricts the chart to odd
  `p` so the centered origin is unique. The recursion uses
  `d(S³)=0` at the terminal pair `(1,0)`.
- `rawLabel_difference` and `rawLabel_fixed_conjugation` are the affine
  label and conjugation conventions for that numbering. The generator
  for each chart is chosen to make a unit advance in raw labels a unit
  advance in the cyclic group. The centered computation retains the
  surgery chart because equivalent presentations can use different
  generators. Lean proves that the fixed raw index is `70` for the
  chart at hand and uses this to transport all `245` indices.

The endpoint specializes these inputs only after checking the knot's Conway
fraction, orientation, alternation, signature, and crossing count. The
independent Python replay in `reports/section3b-numerical-checks.txt`
corroborates the finite calculations. All comparison predicates used by the
endpoint come from the Lean proofs.
