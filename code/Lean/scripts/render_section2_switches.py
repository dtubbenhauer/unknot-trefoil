#!/usr/bin/env python3
"""Render fixed switch witnesses for the Lean planar diagram checker."""
from argparse import ArgumentParser
from ast import literal_eval
from pathlib import Path
import re


def read_diagram(source, name):
    # These generated declarations have one sparse row array per line.
    match = re.search(rf"^def {name} : Diagram :=\n  ⟨(.*), (\d+)⟩$", source, re.M)
    if not match:
        raise ValueError(f"Missing diagram {name}")
    return literal_eval(match[1].replace("some ", "").replace("none", "None")), int(match[2])


def witness(source, target, changed):
    src = [i for i, row in enumerate(source) if row is not None]
    dst = [i for i, row in enumerate(target) if row is not None]
    if len(src) != len(dst):
        raise ValueError("Diagrams have different counts")
    if src != dst:
        raise ValueError("The stages must keep their crossing indices")
    for parity_seed in range(2):
        rotations = {}
        queue = [(src[0], 2 * parity_seed + int(src[0] == changed))]
        while queue:
            i, rot = queue.pop()
            if i in rotations:
                if rotations[i] != rot:
                    break
                continue
            if rot % 2 != (i == changed):
                break
            rotations[i] = rot
            for p, dart in enumerate(source[i]):
                v, q = divmod(dart, 4)
                w, r = divmod(target[i][(p + rot) % 4], 4)
                if w != v:
                    break
                queue.append((v, (r - q) % 4))
            else:
                continue
            break
        else:
            if len(rotations) == len(src):
                return [(4 * v + p, 4 * v + (p + rotations[v]) % 4)
                        for v in src for p in range(4) if rotations[v] != 0]
    raise ValueError("No permitted relabeling")


def render(source):
    yield "import Trefoil.Section2Switches"
    yield "import Trefoil.Section2DiagramData"
    yield ""
    yield "/-! Finite crossing-switch witnesses for the three replays. -/"
    yield ""
    yield "namespace Trefoil.Section2SwitchData"
    yield "open Section2DiagramMoves Section2DiagramData Section2Switches"
    yield ""
    for parity in ("even", "odd", "seed"):
        for stage, start, finish, crossing in (
            ("AB", "Start", "B", 9), ("CD", "C", "D", 8), ("EF", "E", "End", 4),
        ):
            d, dc = read_diagram(source, parity + start)
            e, ec = read_diagram(source, parity + finish)
            assert dc == ec
            name = parity + stage
            relation = repr(witness(d, e, crossing))
            marks = "(none) (none)" if parity == "seed" else (
                f"(some {parity}{stage[0]}Axis) (some {parity}{stage[1]}Axis)"
            )
            yield f"def {name} : List (Dart × Dart) := {relation}"
            yield f"theorem {name}_checked : checkSwitch {parity}{start} {parity}{finish} {crossing}"
            yield f"    {marks} {name} = true := by decide"
            yield ""
    yield "end Trefoil.Section2SwitchData"


def main():
    parser = ArgumentParser(description=__doc__)
    parser.add_argument("source", type=Path)
    parser.add_argument("output", type=Path)
    args = parser.parse_args()
    source = args.source.read_text()
    for case in ("Even", "Odd", "Seed"):
        shard = args.source.with_name(f"{args.source.stem}{case}.lean")
        if shard.exists():
            source += "\n" + shard.read_text()
    args.output.write_text("\n".join(render(source)) + "\n")


if __name__ == "__main__":
    main()
