# Section 2 witness data

The Lean files use fixed data from one recorded run. The files here identify
the diagrams and the two peripheral cycles on each exterior, with the
tetrahedron maps and the coefficients that witness the claimed changes of
peripheral homology classes.

- `replay/` contains the public Python verifiers at commit
  `c4025240770f7f459c1e6cb10c02f5ca3a8cc9e8`, their pinned requirements and
  a replay produced using those requirements. The public repository is
  [dtubbenhauer/unknot-trefoil](https://github.com/dtubbenhauer/unknot-trefoil).
- `exteriors/witnesses.json` contains the six augmented maps and four filled
  maps at `m=2`. The tetrahedron permutations satisfy all face equations.
  The signed potentials store the coefficients of dual cusp two-cells whose
  boundaries are the differences of the compared peripheral cycles.
- `diagrams/export.py` records the local diagram moves and matches the
  resulting marked diagrams against the signed PD inputs to the exteriors.
- `retriangulation/moves.json` records the labelled bipyramids for each
  two-three or three-two replacement along each of the twelve augmented
  marked triangulation paths. The canonical-end markings in
  `exteriors/witnesses.json` are those at the end of these paths.

## Replay the paper's check

Run from this directory with Python assertions enabled.

```bash
python -m pip install -r replay/requirements.txt
python replay/verify_trefoil.py --json /tmp/trefoil-replay.json
python replay/verify_seed.py
```

Different valid simplicial relabelings and simplification paths can occur in
a fresh replay. The two parity cases give the exterior maps used in the
argument for all filling slopes in Section 2 of the paper.

## Recreate the Lean exterior data from the fixed snapshot

Run from `code/Lean`.

```bash
python section2-certificates/exteriors/render_section2_triangulations.py \
  section2-certificates/exteriors/witnesses.json \
  Trefoil/Section2TriangulationData.lean --named
```

The renderer writes one module per map so each kernel process releases its memory
before the next check. Generated imports put the checks into two chains so a
fresh Lake build can run at most two at a time. Lean checks the face equations,
cycle equations and chain boundaries in those arrays. The assumptions
audit documents the geometric hypotheses identifying the diagram
exteriors with the input triangulations.

## Collect a fresh retriangulation trace

The optional trace exporter uses SnapPy's native kernel on Linux. With
`SNAPPY_SOURCE` pointing to the checkout of SnapPy at tag
`3.3.2_as_released`, run from `retriangulation/`.

```bash
gcc -O2 -fPIC -shared -I"$SNAPPY_SOURCE/kernel/headers" \
  -I"$SNAPPY_SOURCE/kernel/real_type" trace.c -ldl -o trace.so
SNAPPY_TRACE_MODULE=$(python -c 'import snappy.SnapPy as m; print(m.__file__)') \
  SNAPPY_TRACE_FILE=matched.jsonl LD_PRELOAD="$PWD/trace.so" \
  PYTHONPATH=../replay python export_with_traces.py matched.json
PYTHONPATH=../replay:../exteriors python check_initial_exterior.py matched.jsonl matched.json
PYTHONPATH=../replay:../exteriors python verify_traces.py matched.jsonl matched.json new-moves.json
```

This records the tetrahedron data used by the exporter and checks the local
bipyramid replacements. The marked triangulation tables are aligned with
the pre-tidy curve representatives. The initial signed PD-to-octahedra
computation can also be replayed. The assumptions audit records its
connection to the ideal starting triangulation through finite-vertex
elimination.

## Re-export diagram move witnesses

Run from `code/Lean` with the packages pinned in `replay/requirements.txt`.
Choose a new path to compare a fresh witness with the checked-in file.

```bash
python section2-certificates/diagrams/export.py \
  section2-certificates/replay/verify_trefoil.py /tmp/Section2DiagramData.lean \
  --exteriors section2-certificates/exteriors/witnesses.json --split
```

Given those diagram modules, regenerate the crossing-switch witness file from
`code/Lean` with:

```bash
python scripts/render_section2_switches.py \
  Trefoil/Section2DiagramData.lean Trefoil/Section2SwitchData.lean
```
