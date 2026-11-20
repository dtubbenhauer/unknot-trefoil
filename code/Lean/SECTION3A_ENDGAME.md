# Section 3A relative proof

The final declaration is `Trefoil.Section3ATopology.section3A_lower_bound`. It uses the original manuscript's family and its range, with topology supplied through the generic `Geometry` and `References` interfaces. See [the proof map](proof-map.md) for declaration names and [the assumptions audit](ASSUMPTIONS.md) for the exact scope.

Write `p=104m+37`. For `m=4` or `m≥6`, suppose the oriented partner can be unknotted in fewer than three moves. The even continued-fraction expansion for each parity of `m` gives signature four, so a shortest sequence consists of two negative crossing changes. Owens supplies a positive definite filling of the oriented branched cover `Y=L(p,104)` with four 2-handles. The 2-framed meridians of the two surgery components give orthogonal norm-two classes.

The explicit positive chain has weights `(2^(m−1),4,6,2,2,3)` and fraction `p/(p−104)`. Its oriented boundary is the reverse of `Y`. The weight calculation and the uniform tridiagonal positivity argument supply the form of this plumbing before gluing. The two pieces glue to a closed simply connected four-manifold. On included classes its intersection form is the orthogonal sum of the two forms.

Since `H₁(Y;ℤ)=ℤ/p`, integral Mayer–Vietoris shows that every `p`-multiple in the glued second homology comes from the pieces. The glued second homology is torsion-free, so the square of any nonzero class has the same positive sign as the square of its nonzero `p`-multiple. This proves positive definiteness for the application of Donaldson. The same integral sequence separately shows that the integral inclusion is injective with cokernel `ℤ/p`, giving the stated index.

The mod-two degree-two cellular differential of `Y` is the identity because `p` is odd. Both relevant mod-two boundary groups vanish, so mod-two Mayer–Vietoris gives an isomorphism from the piece homology to the glued homology. Transporting the two piece bases and the unspecified-rank integral Donaldson coordinates through coefficient reduction proves the diagonal rank `m+8` and independence of the reduced integral columns.

The matrix of included handle classes now has all the required local pairings. The normal form puts the norm-two vectors into disjoint signed paths. The three heavier vectors are forced into the manuscript's coordinate patterns, whose parity and integer pairings lead to the contradiction.

The archive leaves the actual-knot interpretation of the general topology references open. The three earlier homology-level bridges are under `experimental/` and covered by the verification script. They are independent of the final theorem's proof path.
