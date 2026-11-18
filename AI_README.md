# AI reading guide

[Paper (PDF)](paper/trefoil-partners.pdf) · [Paper in Markdown](ai/paper.md) · [Theorem index](ai/theorem-index.json) · [Figures](figures/README.md) · [How to run the checks](code/README.md)

Read Theorem 1A.1 and Corollary 1B.1 in the introduction for the statements. The paper uses ordinary unknotting number: isotopy is allowed between crossing changes. The trefoil has unknotting number one. The partners in the theorem have unknotting number three. The paper gives the interval `[2,3]` for the unknotting number of their connected sums with the trefoil.

## Proof map

| Location | Argument |
| --- | --- |
| Section 2A | The six diagrams for `m = 2` show three switches, with two diagram identifications between them. The second identification reverses orientation, so the last switch uses the reflected diagram. |
| Section 2B | Three changes in the continued-fraction diagram unknot the partner on its own. |
| Sections 2C–2D | Write `m = b + 2t` with `b = 0, 1`. A crossing circle records the full twists. For the two choices of `b`, the marked exterior identifications match the peripheral slope data. This extends the sequence to the family. |
| Section 3A | A definite lattice obstruction rules out two changes for `m = 4` and `m ≥ 6`. |
| Section 3B | A separate correction-term obstruction rules out two changes for the determinant-245 knot, `m = 2`. |
| Section 1B | Deplumbing a positive trefoil plumbing to a trefoil extends the saving. For negative torus knots, mirror both summands. |
| Section 4 | The signed DT codes, tangle ports, switch indices and verification commands specify the finite checks. |

## Conventions that affect the result

- Choose the chirality of the partner so its signature has the opposite sign to that of the trefoil. The identification of the first partner as `14a7385` is up to mirror.
- The classification range for the partners is `m = 2, 4` and every integer `m ≥ 6`. The `m = 0` end of the construction recovers the earlier three-switch sequence with `10_6`, for which the paper quotes the interval `[2,3]`.
- The peripheral basis on the crossing circle is the meridian followed by the longitude from its spanning disk. The orientation-reversing exterior maps act by `diag(1,-1)` up to overall sign. Section 2D lists the stages with slopes `(1,t)` and `(1,-t)`.
- The geometric scripts use combinatorial triangulation isomorphisms with marked peripheral data for the finite exterior identifications. The argument over all twist parameters and the general lattice obstruction are in the manuscript. The standard-library script replays the arithmetic for determinant 245.
