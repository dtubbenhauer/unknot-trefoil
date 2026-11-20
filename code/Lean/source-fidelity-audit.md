# Source fidelity audit

For the determinant-245 case, see the separate [Section 3B audit](SECTION3B.md).

The reviewed Section 3A is the explicit lattice obstruction in [the supplied manuscript](paper-reference/main.tex). The SHA-256 of that TeX snapshot is `aa5c567f73a5cb08ba80e4c6d940198c244c29f26abae6c5294d635beebd0aa8`.

## Family and geometric interfaces

- The positive Conway weights are `[m,2,1,4,3,2]` and yield `p/104` for `p=104m+37`. The oriented version is the chirality whose branched cover is positive surgery of that slope. The theorem for the Conway presentation uses the general identification up to mirror and invariance under mirroring.
- The two even lists have the manuscript's respective lengths eight and six. Their homogeneous pairs differ by global sign and represent the same fraction. Right-to-left elimination gives two negative pivots in the even case and one in the odd case. In both cases the signature count is four.
- The signed crossing inequality gives two negative changes if the total is at most two. Owens is applied with this sign count and with the positive surgery orientation. The two square-two classes in `W` are handle meridians. Their pairings with the two other handles of `W` are unrestricted by the obstruction.
- The weights of `G` are the `m−1` leading twos and the tail `4,6,2,2,3`. Their continued fraction is `p/(p−104)`. The boundary is the reverse of the oriented cover. The chain has rank `m+4` and the two-handlebody from Owens has rank four. Both have determinant `p`.
- The hypotheses of Donaldson are established for the glued manifold. The reference gives an isometry of the closed form for an initially unspecified rank. The proof derives `m+8` from the two-piece mod-two homology and the integral bases, and proves independence of the reduced joint columns using the same comparison.

## Selected vectors and normal form

- The last long-chain root pairs with `A` by `−1`. On the short chain the first root pairs with `B` by `−1`, and the second with `C` by `−1`. All other heavy-root pairings vanish.
- The three heavy norms are `4,6,3`, and `(A·B,A·C,B·C)=(-1,0,0)`.
- The `m+3` roots use blocks of sizes `m,3,2,2`, leaving one ambient coordinate. Signed coordinate normalization is proved from the computed pairings and the independence of the reduced columns.
- On the long block, `A=(a,…,a,a+1)` has squared norm `m*a^2+2*a+1` and sum `m*a+1`. The triples are `A=(z,z,z)`, `B=(g−1,g,g)`, and `C=(ell,ell,ell+1)`. Their mutual contributions are `z*(3*g−1)`, `z*(3*ell+1)`, and `3*g*ell+g−ell`, respectively.
- Both pair blocks contribute even sums and doubled products. Independence of `B` from the roots therefore forces at least one odd block sum among the remaining blocks. The arithmetic proves that precisely the configurations required by the pairings are impossible.
- The final assertion is `3 ≤ u(P_m)` for `m=4` or `m≥6`. The parameter `m=5`, the separate case `m=2`, and the upper bound are outside this endpoint.

## Why the homology proof has a different route

The manuscript uses rational Mayer–Vietoris to get full rank and the determinant-index calculation to get independence modulo two. The Lean construction uses the actual integral inclusion map, proves its compatibility with coefficient reduction and obtains reduced independence directly. Since `p` is odd, both the kernel and cokernel of multiplication by `p` on `F₂` vanish. The mod-two Mayer–Vietoris map is therefore bijective. This also proves the rank when compared with the reduced integral bases. Integral Mayer–Vietoris separately computes the index as `p` from the order of the boundary's first integral homology.

The source checks and the axiom reports certify the Lean statements and their logical dependencies. The interpretation of the reference interface as the actual geometry remains a separate mathematical input.
