# Lean verification

This directory contains the Lean 4 verification for Sections 2 and 3 of *Unknotting number is strictly subadditive for the trefoil*. It accompanies the [paper](../../paper/trefoil-partners.pdf) and the [original repository README](../../README.md).

The unified lower-bound endpoint is
`Trefoil.Section3LowerBound.section3_lower_bound`. It proves `3 ≤ u(P_m)` for `m = 2`, `m = 4` or `m ≥ 6` **relative to explicit reference arguments**. Section 2 contains the rational-tangle checks and the marked-diagram certificates; the geometric interpretations of some diagram/exterior data remain explicit hypotheses. The project does not formalize Owens's theorem, Donaldson's theorem, all of smooth knot topology or Heegaard Floer theory from first principles.

## Reproduce the verification

Install [elan](https://github.com/leanprover/elan), Git and Python 3.11 or later. The toolchain and Mathlib revisions are pinned in `lean-toolchain` and `lake-manifest.json`.

From this directory run:

```sh
elan toolchain install leanprover/lean4:v4.22.0-rc2
bash verify_lean.sh --get-cache --clean
```

On a system with the pinned dependencies already installed, omit `--get-cache`. To verify only Section 3B and the unified lower-bound endpoint, run `bash verify_section3b.sh`. The larger Section 2 certificates are compiled in shards to control memory use.

The recorded handoff reports are in [`reports/`](reports/): [verification manifest](reports/verification.json), [Section 3A reference audit](reports/section3a-reference-axioms.txt), [Section 3B/unified reference audit](reports/section3b-reference-axioms.txt), and [project theorem/axiom audit](reports/project-theorems-and-axioms.txt). The verified handoff reports a successful build, but **not a clean build**; the [GitHub Actions workflow](../../.github/workflows/lean-section3a-endgame.yml) runs a clean build from the checked-in sources.

## Read the proof

- [Proof map](proof-map.md): paper statements and corresponding Lean declarations.
- [Assumptions audit](ASSUMPTIONS.md) and [literature inputs](literature-inputs.md): exact hypotheses and external results.
- [Section 2 certificate guide](SECTION2.md) and [Section 3A proof](SECTION3A_ENDGAME.md).
- [Section 3B and unified theorem](SECTION3B.md).
- [Source-fidelity audit](source-fidelity-audit.md): checked notation, orientations and coordinate identities. The [frozen TeX snapshot](paper-reference/main.tex) is retained solely to make its recorded SHA-256 reproducible; the live paper source is at [`paper/source/main.tex`](../../paper/source/main.tex).

The project has no additional mathematical axiom declarations in its verified proof path. Its reference-relative endpoint depends on the explicit general-theory hypotheses described above, together with Lean's usual foundational axioms.
