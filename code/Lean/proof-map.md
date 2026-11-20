# Manuscript-to-Lean proof map

The Section 2 endpoint and certificates have their own [proof map](SECTION2.md).

The source is [the supplied manuscript](paper-reference/main.tex). The unified Section 3 endpoint is in [`Trefoil/Section3LowerBound.lean`](Trefoil/Section3LowerBound.lean).

```lean
Trefoil.Section3LowerBound.section3_lower_bound
  {T : Geometry} (R : References T) (F : FloerReferences T) {m : ℕ}
  (hm : m = 2 ∨ m = 4 ∨ 6 ≤ m) : 3 ≤ T.unknotting (partner T m)
```

The lattice branch is in [`Trefoil/Section3ATopology.lean`](Trefoil/Section3ATopology.lean).

```lean
Trefoil.Section3ATopology.section3A_lower_bound
  {T : Geometry} (R : References T) {m : ℕ}
  (hm : m = 4 ∨ 6 ≤ m) : 3 ≤ T.unknotting (partner T m)
```

`partner T m` is the positive Conway diagram from the manuscript. `section3A_oriented_lower_bound` gives the same bound for the chirality with oriented branched double cover given by positive surgery of slope `(104*m+37)/104`. The Conway fraction and invariance of unknotting number under mirror transfer that bound to `partner T m`.

## Section 2 — Upper bound

The inherited [Section 2 proof map](SECTION2.md) documents the three-change
proof and the remaining diagram-to-exterior hypotheses.

## Signature and Owens filling

| Manuscript step | Lean declaration | Reference input |
| --- | --- | --- |
| Both even-weight fraction presentations represent `p/104`, where `p = 104*m+37`. Each has nonzero pivots and signed count four. | `Arithmetic.even_seifert_pair`, `odd_seifert_pair`, `even_pivots`, `odd_pivots` and their signature lemmas. `Section3ASignature.partner_signature_four` selects the presentation according to the parity of `m`. | General identification of the even chain with a symmetrized Seifert form and the tridiagonal inertia rule. |
| A shortest unknotting with fewer than three moves would have two negative moves in Owens's convention. | `Section3ATopology.two_negative_changes` | Existence of a shortest crossing-change sequence and the signature change inequality. |
| The assumed sequence gives a positive simply connected two-handlebody `W` with four handles, determinant `p` and two orthogonal norm-two meridians. | `Section3ATopology.owens_filling` | Owens, Theorem 3 and Lemma 2.2(i), plus the general identification of the two-bridge cover and its integral homology. |

## The explicit positive plumbing

`Section3APlumbing.plumbingWeights` defines the ordered chain `(2^(m−1),4,6,2,2,3)`. `plumbing_fraction` proves that its homogeneous fraction is `(p,p−104)`. `plumbing_positiveDefinite` proves positive definiteness of the explicit matrix on its integral lattice. `plumbing_det` computes its determinant. `explicit_plumbing` applies the general linear-chain Kirby presentation and lens orientation rule to these weights. It derives the opposite-oriented boundary and the Gram matrix on the reindexed handle basis.

The selected plumbing classes are the long chain of twos, the two consecutive twos in the tail and the vertices `A,B,C` of weights `4,6,3`. `jointGram_root`, `jointGram_A_root`, `jointGram_B_root`, `jointGram_C_root` and the heavy-vertex lemmas compute the entries needed by the obstruction. `selectedIndex_injective` proves the selected roots and `B` are distinct handle indices.

## Gluing, rank and reduction

| Manuscript step | Lean declaration | Reference input |
| --- | --- | --- |
| Glue `G` and `W` using the opposite boundary orientations. The closed manifold is simply connected and the joint intersection form is the orthogonal sum on the included classes. | `Section3ATopology.no_two_change_gluing` uses the boundary match from the explicit fillings. | Collared gluing, van Kampen and the intersection number of included cycles, with zero cross terms by disjoint support. |
| The integral joint inclusion is injective with index `p`. | `integral_joint_exact` identifies its cokernel with `ℤ/p`. `integral_joint_index` computes its cardinality. | Integral Mayer–Vietoris, simple connectivity of the pieces and integral lens-space homology. |
| Prove the closed intersection form positive. | `glue_positive` uses that `p` annihilates `H₁(Y;ℤ)`. Exactness lifts `p*x` to the two pieces, and torsion-freeness makes that lift nonzero when `x` is nonzero. | Integral Mayer–Vietoris exactness, lens-space homology, and Poincaré duality with the universal coefficient theorem. |
| Apply Donaldson to obtain an integral diagonalization. Recover its rank as `m+8`. | `lens_F2_vanish` proves that the kernel and cokernel of the degree-two cellular differential vanish. `mv_F2_bijective` then identifies the two-piece and glued mod-two groups. `joint_diagonal_rank` compares their dimensions using the reduced integral bases. | Donaldson for closed simply connected positive definite smooth four-manifolds, cellular comparison, Mayer–Vietoris and coefficient reduction. |
| Prove the reduced joint columns independent. | `Section3ACoefficients.reductionLinearEquiv` descends an integral basis to coordinates modulo two. `no_two_change_gluing` transports the joint basis through the mod-two inclusion and restricts independence to the required handles. | Naturality of the coefficient maps with respect to inclusion. |

The formal route to the rank and independence uses the two vanishing mod-two boundary groups and the resulting Mayer–Vietoris isomorphism. The manuscript uses rational Mayer–Vietoris and an odd-index argument for independence.

## The integral lattice obstruction

`no_two_change_gluing` constructs `LatticeEmbedding.Embedding m` from the integral Donaldson coordinates of the handle images, their computed Gram entries and the proved independence. `LatticeExtraction.no_embedding` eliminates this object.

- `LatticeBasics` classifies integral norm-two vectors. `LatticePath` and `LatticeSupports` derive the support paths and disjointness.
- `LatticeSigns` and `LatticeBlocks` construct a signed permutation to blocks of sizes `m,3,2,2,1`.
- `LatticeShapes`, `LatticeCoordinates` and `LatticeIsometry` derive the three heavy-vector rows and compute their norms and pairings in those coordinates.
- `LatticeParity` and `LatticeFrameParity` identify the span of the roots over `ZMod 2` and transfer the independence of `B` to a block-sum condition.
- `LatticeArithmetic` derives the contradiction uniformly in the asserted parameter range. The range excludes `m=5`.

`LatticeOddBasis` also proves the independent algebraic route from an odd-determinant basis matrix to the same lattice obstruction.

## Section 3B — Determinant 245

`FiniteForms` derives `2 ≤ h ≤ 62` and proves the exhaustive five-form classification. `FiniteCorrectionTerms` implements the rational recurrence and certifies its exact numerators. `FiniteObstruction.no_reduced_correction_comparison` excludes a single compatible labeling for each candidate.

`Section3BMinimum` defines the integral surgery cokernel and proves the change in characteristic value under lattice translation. The genuine minimum and the single additive class map then give the comparison for every representative. `Section3BTopology` applies Owens to the oriented two-bridge knot after checking signature four, alternation and two negative changes. It uses the positive Goeritz sharpness identification, the reversed lens space and the spin label `70` to obtain the exact correction terms used by the finite proof. The Conway fraction and mirror invariance transfer the lower bound to the paper's knot. See [SECTION3B.md](SECTION3B.md).

## Section 4 — Consequences

`Consequences` contains conditional numeric deductions about exact unknotting number, the strict saving, distinctness and the positive trefoil plumbing stage count. Completing these claims for the actual knots still requires the geometric upper bound, the finite-case transfer, and the corresponding external results on connected sums and positive plumbing.
