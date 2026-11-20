# Section 2 upper-bound formalization

The main declarations are `Trefoil.Section2Topology.partner_upper_bound` for the partner alone and `Trefoil.Section2Certificate.family_upper_bound` for its connected sum with the trefoil. The latter is relative to the stated diagram and filling theorems and the explicit exterior-realization obligations. The family proof consumes the computed parity witnesses. It does not take the three-change movie or any upper bound as an input.

## From the finite calculation to every parameter

| Manuscript step | Lean declaration or witness |
| --- | --- |
| Write the parameter as one retained half twist or zero, plus full twists. | `Section2Arithmetic.halfTwists_decompose` |
| Switch the crossing in the one-crossing box and two in the three-crossing box, and cancel opposite crossings. The numerator closure has fraction ((1,0)). | `partner_three_local_switches`, `changedPartnerBoxes_infinity`, and `Section2Topology.partner_upper_bound` |
| Match the rational-tangle insertions and determine the twist handedness. | `firstChart_fraction`, `lastChart_fraction`, `firstChart_slopeSign`, and `lastChart_slopeSign` |
| Construct the reference closure with the correct fraction and axis. | `Section2ReferenceTangle.builtReference`, `evenReference_constructor`, `oddReference_constructor`, and `Section2Certificate.reference_chart` |
| Replay the marked switches away from the crossing circle. | `Section2SwitchData.evenAB_checked`, `evenCD_checked`, `evenEF_checked`, and the odd and named-example counterparts |
| Find the splitting sphere and simplify the final unlink. Identify the trefoil chirality. | `Section2DiagramData` contains the explicit verified move traces, marked split cuts, anchor transport, and relabelings of the trefoil. `Section2Certificate.split_start` uses them. |
| Verify the two boundary-marked exterior identifications and the match with the reference link in each parity. | `Section2TriangulationData.data_checked` and `data_slopes` check the explicit tetrahedron and vertex maps, orientation, cusp permutation and peripheral homology equations. |
| Extend the maps over the filled slopes, transport the switches, and chain the three changes. | `Section2Topology.filled_movie` and `Section2Certificate.family_upper_bound` |
| Independently replay the filled first example and match its partner to the table diagram up to mirror. | `Section2Certificate.seed_movie`, `seed_partner_is_table` and the four additional marked exterior witnesses. |

The pinned independent seed replay records signatures (+2,-4) in the repository convention. Lean tracks the chosen chirality by the oriented relabelings of the trefoil and by mirroring the reference partner.

The three successive changes go through the preserving map after the first switch and the reversing map after the second. On slopes the reversing map sends ((1,t)) to ((1,-t)). Filling commutes with a crossing change made away from the axis. The last switch is mirrored at both endpoints. This derives the family argument for arbitrary (t), with no bounded search over the twist parameter.

## Reference hypotheses and remaining geometry

- `KnotReferences` is the usual interpretation of individual twist-box changes, numerator closures and paths of crossing changes. It applies to knot closures, as checked by the odd numerator hypotheses.
- `FillingReferences` expresses locality of a crossing change, the persistence of a sphere disjoint from the surgery axis, filling a split pair of unknots, the extension of a peripheral-preserving homeomorphism over a solid torus, and the relation between surgery on the crossing circle and full twists. The crossing-locality argument appears in Baker–Miyazawa–Motegi, Lemma 2.2 and its proof. [ArXiv preprint](https://arxiv.org/abs/2504.03867)
- `DiagramReferences` gives the uniform geometric interpretations of the finite graph conditions, including planar diagram moves and relabelings, the split cut, the four-port chart, and the effect of marked simplicial maps on the two peripheral classes. The checked domain predicates enforce planarity, component counts and the marked crossing circle. The trefoil equality chooses the representative and chirality for the geometry model.
- `ExteriorBridges` and `SeedExteriorBridges` state which explicit marked triangulations are exteriors of the named planar diagrams, including the correct meridians and disk longitudes. They are specialized realization obligations. They remain arguments of the corresponding relative theorem and are not counted as established general literature inputs.

The archive includes the pinned SnapPy replay and an independent exact Python check of the twelve augmented signed-PD-to-octahedron computations and the 359 raw-to-canonical replacements with peripheral arc transport. `Section2InitialExterior` and `Section2Pachner` supply general Lean computations and soundness lemmas for parts of these steps. The concrete replays of those two steps are recorded in the Python reports. See the [certificate instructions](section2-certificates/README.md) for the checks and their scope. The missing exterior proof must connect each signed PD to its marked ideal exterior in Lean, including the finite-pole removal from the octahedral cellulation and the peripheral transport through triangular-pillow insertions and valence-two cancellations. A kernel check of the canonical isomorphisms and their cusp chains supplies the maps only after that exterior identification.

## Verification and provenance

The general and paper-specific Lean files compile from the same pinned Lean and Mathlib dependencies as Section 3A. The integer graph checks, cusp chain equations, and continued-fraction arithmetic use Lean reduction and ordinary proof terms. Python and SnapPy generate and independently replay witness data. No Python success value is used as a Lean premise.

The manuscript and the public verifier are included as provenance. The public code snapshot is [c4025240770f7f459c1e6cb10c02f5ca3a8cc9e8](https://github.com/dtubbenhauer/unknot-trefoil/tree/c4025240770f7f459c1e6cb10c02f5ca3a8cc9e8).
