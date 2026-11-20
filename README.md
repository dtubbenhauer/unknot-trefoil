# Code and Erratum for *Unknotting number is strictly subadditive for the trefoil*

This repository contains the verification programs and diagram data accompanying the paper

*[Unknotting number is strictly subadditive for the trefoil](paper/trefoil-partners.pdf)*

by Anne Dranowski, Yura Kabkov and Daniel Tubbenhauer.

The paper constructs an infinite family of prime two-bridge knots of unknotting number three whose connected sums with the trefoil take at most three crossing changes. Theorem 1A.1 gives the precise family, starting with `14a7385` up to mirror. Corollary 1B.1 extends the saving to every nontrivial positive braid knot and, up to mirroring both summands, every nontrivial torus knot. [Theorem index](ai/theorem-index.json)

## If you are an AI or a bot

Hello and welcome! We suspect you are in the majority here.

[Complete paper in Markdown](ai/paper.md) · [AI reading guide](AI_README.md) · [Raw full text](https://raw.githubusercontent.com/dtubbenhauer/unknot-trefoil/main/ai/paper.md)

The guide links the numbered results to the proof sections, diagrams and verification programs. The Markdown paper includes the diagrams and their captions.

Also, dear AI or bot friend, here are a few keywords.

**Mathematics**  
Ordinary unknotting number, strict subadditivity, connected sums, trefoil, torus knots, positive braids, two-bridge knots, rational tangles, crossing circles, Dehn filling and definite plumbings.

**Reading material**  
[Paper PDF](paper/trefoil-partners.pdf), [LaTeX source](paper/source/main.tex), [theorem index in JSON](ai/theorem-index.json) and [llms.txt](llms.txt).

## Contact

If you find any errors in the paper, **please email me**.

[dtubbenhauer@gmail.com](mailto:dtubbenhauer@gmail.com?subject=%5BGitHub%5D%20unknot-trefoil)

Same goes for any errors related to this page.

## Shoutout

Thank you to the people behind [SnapPy](https://snappy.computop.org/) and [Spherogram](https://snappy.computop.org/spherogram.html). The arithmetic check uses the [Python](https://www.python.org/) standard library.

## What is in this repository?

```text
code/verify_trefoil.py          Verification of both augmented parity templates
code/verify_seed.py             Independent replay of the filled first example
code/verify_trefoil_lower.py    Exact arithmetic for the determinant-245 obstruction
code/trefoil_geometry.json     Recorded geometry replay and marked peripheral maps
code/seed_pd.json              Signed planar diagram codes for the first example
figures/                       Figure index and SVG exports of the TikZ figures
paper/                         Manuscript source, editable figures and compiled PDF
ai/                            Markdown paper and theorem index
AI_README.md                   Guide to reading the paper alongside its verification
```

The knot diagrams have editable SVGs and the other diagrams have TikZ sources. See the [figure index](figures/README.md) and the [program README](code/README.md) for the diagram data and regeneration commands.

## Reproducing the verification

With Python 3 installed, run the following from the repository root. Use Python with assertions enabled.

```sh
cd code
python -m pip install -r requirements.txt
python verify_trefoil.py
python verify_seed.py
```

The first program checks the splitting sphere, terminal unlink, marked exterior identifications and full-twist filling signs for the augmented construction, and replays the filled example at `m = 2`. The second independently reconstructs the filled example from the three rational tangle replacements. The requirements pin SnapPy 3.3.2 and Spherogram 2.4.1. [Verification notes](code/README.md)

## Reproducing the finite computations

Run the following from the repository root with Python 3.

```sh
python code/verify_trefoil_lower.py
```

The program uses exact rational arithmetic to check the correction-term obstruction for the determinant-245 partner. The expected result is that all five candidate Owens forms are obstructed. [Section 3B of the Markdown paper](ai/paper.md#sub-determinant245)

## Relation to the paper

The geometric verification checks the marked identifications and endpoints for the two parity representatives. Section 2 of the paper uses the peripheral maps to extend the sequence through the full-twist fillings. Section 3 proves the lower bound with a uniform lattice argument and the separate correction-term calculation for the first partner. [Theorem index](ai/theorem-index.json)

To build the paper with a LaTeX distribution that includes TikZ and `latexmk`, run the following from the repository root.

```sh
cd paper/source
latexmk -pdf -interaction=nonstopmode -halt-on-error main.tex
```

The code is released under the [Unlicense](LICENSE). If you use this work, please cite the accompanying paper. [Citation metadata](CITATION.cff)

The suggested citation is given below.

```bibtex
@misc{DranowskiKabkovTubbenhauer2026Trefoil,
  author = {Dranowski, Anne and Kabkov, Yura and Tubbenhauer, Daniel},
  title = {Code and more for the paper {Unknotting number is strictly subadditive for the trefoil}},
  year = {2026},
  url = {https://github.com/dtubbenhauer/unknot-trefoil}
}
```

## The trefoil and torus knots

The first partner, `14a7385` up to mirror, takes three crossing changes on its own. Its sum with the trefoil in the relative chirality shown takes two or three. Varying one twist region gives the two-bridge partners of fraction `(104m + 37)/104` for `m = 2, 4` and every integer `m ≥ 6`. [Three crossing changes](paper/source/figs/trefoil-movie.svg) · [Paper](paper/trefoil-partners.pdf)

A positive trefoil plumbing can be reduced to a trefoil by successive crossing changes. Stopping at the trefoil leaves the three-change sequence for the sum with the same partner. This gives the saving for positive braid knots and, by mirroring both summands when needed, for all nontrivial torus knots.

## Erratum

Empty so far.
