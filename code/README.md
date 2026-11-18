# Verification code and data

Use Python with assertions enabled. Run from this directory:

```sh
python -m pip install -r requirements.txt
python verify_trefoil.py
python verify_seed.py
python verify_trefoil_lower.py
```

| Script | What it checks |
| --- | --- |
| [verify_trefoil.py](verify_trefoil.py) | Reconstructs both augmented parity templates, the connected-sum decomposition, the terminal unlink and the marked exterior maps. Checks the signs of the full-twist fillings and replays the filled `m = 2` sequence. |
| [verify_seed.py](verify_seed.py) | Independently reconstructs the filled `m = 2` example from the three rational tangle replacements in the paper. Checks the summands and their relative chirality, the intervening identifications and the final unknot. |
| [verify_trefoil_lower.py](verify_trefoil_lower.py) | Replays the determinant-245 correction-term obstruction using exact rational arithmetic and the Python standard library. See Section 3 of the [paper](../paper/trefoil-partners.pdf) for the general lattice argument. |

[trefoil_geometry.json](trefoil_geometry.json) records one geometry replay, including the planar diagram codes and marked peripheral data. Run `python verify_trefoil.py --json replay.json` to save a new replay. Diagram relabelings and choices of combinatorial isomorphism may vary.

[seed_pd.json](seed_pd.json) contains the signed planar diagram codes for the six panels of the crossing-change sequence.

## Regenerate the vector drawings

The three knot drawings have editable SVGs and compiled PDFs in [paper/source/figs](../paper/source/figs). The other three figures have TikZ sources there. To regenerate the six-panel crossing sequence and the two augmented starts, install Inkscape and, in the same Python environment as above, Shapely. Run from this directory:

```sh
python -m pip install shapely
python ../paper/source/figs/make_movie.py seed_pd.json ../paper/source/figs
python ../paper/source/figs/draw_parities.py trefoil_geometry.json ../paper/source/figs/marked-parities
```

The orthogonal layout of the two augmented starts can vary between runs. The included SVG and PDF preserve the layout printed in the manuscript. To export the editable drawing of the summands separately:

```sh
inkscape ../paper/source/figs/split-seed.svg --export-text-to-path --export-filename=../paper/source/figs/split-seed.pdf
```
