# Section 3 assumptions audit

The unified endpoint is `Trefoil.Section3LowerBound.section3_lower_bound`.
It takes the following Section 3A references and the Section 3B Floer
references audited in [SECTION3B.md](SECTION3B.md). The full range is
`m = 2 ∨ m = 4 ∨ 6 ≤ m`.

For Section 2, see [its separate assumptions and proof map](SECTION2.md).

## Section 3A

The main theorem is `Trefoil.Section3ATopology.section3A_lower_bound`. Its hypotheses are an interpretation of the generic `Geometry` interface, a `References` argument for that interpretation, and the paper's range `m = 4 ∨ 6 ≤ m`. The endpoint supplies the lower bound for the manuscript's Conway diagram.

## Imported mathematical statements

| Fields | Scope and hypotheses |
| --- | --- |
| `sig` | The even linear plumbing realizes a symmetrized Seifert form of the two-bridge knot, using a positive, reduced surgery fraction with odd numerator. The signature of the associated rational symmetric chain matrix is the signed count of its nonzero elimination pivots. |
| `conway_fraction`, `mirror_unknotting`, `bridge_cover` | A positive Conway presentation with the stated reduced fraction gives the two-bridge knot up to mirror. The double branched cover of the specified chirality is the positive-surgery lens space. Mirroring preserves unknotting number. |
| `minimal_crossing_changes`, `signature_crossing_bound`, `owens` | A shortest sequence realizes the unknotting number. In Owens's sign convention a sequence with `neg` negative changes gives `σ(K) ≤ 2*neg`. The filling construction requires equality. For arbitrary `pos+neg` it produces a simply connected positive two-handlebody with twice that many generators and the orthogonal square-two meridians of its integral surgery diagram. Its determinant is the order of the cover's first homology. |
| `chain_plumbing`, `lens_reverse`, `lens_connected` | A framed linear chain gives the prescribed adjacent pairings and boundary in the negative continued-fraction convention. In the manuscript's positive-surgery convention, the oriented lens space with denominator `p−q` is the reverse of the one with denominator `q`. The lens boundary is nonempty and path connected. |
| `lens_h1_Z`, `lens_h2_Z`, `lens_h1_F2`, `lens_h2_F2` | The standard lens-space cellular complex identifies integral first homology with `ℤ/p`, integral second homology with zero, and mod-two first and second homology with the cokernel and kernel of multiplication by `p` on `F₂`. |
| `glue`, `glued_closed`, `glued_simplyConnected`, `glued_intersection` | A boundary match of opposite oriented diffeomorphism classes supplies a collared smooth gluing and its induced maps. Gluing simply connected pieces along the connected boundary gives a simply connected manifold. The intersection numbers of included classes restrict to the original pairings, and cross terms vanish. |
| `mv_Z`, `mv_Z_pieces`, `mv_Z_surjective`, `mv_F2_pieces`, `mv_F2_closed` | The indicated Mayer–Vietoris segments are exact for the chosen gluing and its maps. In the integral segment the boundary map to `H₁(Y;ℤ)` is onto when both pieces are simply connected. |
| `closed_h2_torsionFree`, `uct_surjective`, `uct_kernel`, `coefficient_naturality` | A closed simply connected oriented four-manifold has torsion-free integral second homology. For simply connected pieces and closed manifolds, reduction in degree two is onto with kernel the doubles. Reduction commutes with the inclusion of the pieces. |
| `donaldson` | A smooth, closed, connected, simply connected and oriented four-manifold with positive definite intersection pairing has an integral isometry to the positive diagonal form. The isometry's rank is initially existential. |

See [literature-inputs.md](literature-inputs.md) for exact references and orientation qualifications. These inputs have general parameters for knots, manifolds, slopes or weights. No field takes the Section 3A parameter range as a premise.

## Deductions inside the proof

The proof computes the Conway and surgery fractions, signature and crossing signs, plumbing positivity and pairings, and the hypotheses for gluing and diagonalization. It derives the closed rank and mod-two independence, applies the integral isometry to the actual handle images in the interface, and proves the lattice contradiction. Both filling determinants and the integral joint index are established separately. The final endpoint takes no family-specific realization function, integral coordinate configuration, independence assertion or lattice embedding.

The three compatibility modules under `experimental/` expose earlier homology-level versions of the bridge. Their more specialized structures are audited as separate declarations. The final lower bound depends on the geometric reference interface in `Section3ATopology.lean`.

## Exact missing formalizations

The remaining realization of `Geometry` and `References` would require all of the following in the same Lean model.

- Knot isotopy classes with Conway tangle diagrams, the mirror, crossing changes, oriented branched double covers, and the Seifert matrix realization and signature convention used by Owens.
- Oriented smooth four-manifolds with boundary, collared gluing, framing-dependent two-handle attachments, and identification of the basis and pairing from the linking matrix. For Owens, this includes his uniform half-integral surgery theorem and the integral surgery conversion in Lemma 2.2.
- The oriented lens-space surgery and plumbing relation, the cellular to singular homology comparison for the lens-space CW structure, the singular Mayer–Vietoris sequence on the gluing maps, and the compatibility of coefficient reduction and intersection pairings.
- Donaldson's diagonalization theorem for the resulting smooth, closed, simply connected four-manifold.

Mathlib at the pinned commit supplies basic singular homology constructions. The project uses the statements above as mathematical arguments for this relative theorem. The build and axiom audit do not construct an instance for the actual smooth category.

## Computational trust

The intended foundational dependencies are `propext`, `Classical.choice`, and `Quot.sound`. The verification script records actual axiom dependencies and the expanded interface. It checks the project sources for missing proofs, new axioms and native or unsafe proof escapes. The Python checks provide independent verification data. Their outputs are outside the Lean theorem inputs, following the convention in [mutwo](https://github.com/dtubbenhauer/mutwo/blob/main/code/Lean/ASSUMPTIONS.md).

The negative controls run on temporary, isolated Lean files. They test that the
verifier rejects a missing proof, an unexpected axiom and a changed endpoint
type. Their output is recorded in reports whose names begin with
`negative-`.
