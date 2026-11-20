#!/usr/bin/env python3
"""Render the verified six-panel witness in chronological order.

Usage: python make_movie.py seed_pd.json out_directory
Requires SnapPy, Spherogram and Inkscape.
"""

import json
from pathlib import Path
import subprocess
import sys

import snappy  # Supplies Spherogram's link exterior interface.
from spherogram import Link
from spherogram.links.orthogonal import OrthogonalLinkDiagram

INK = "#191919"
RED = "#9d3339"
BLUE = "#225489"
WIDTH, HEIGHT = 470, 269
STAGES = (("A", "B"), ("C", "D"), ("E-mirror", "F-mirror"))
CENTERS = {"A": 70, "B": 235, "C": 400, "D": 400,
           "E-mirror": 235, "F-mirror": 70}
TOP = {"A", "B", "C"}


def point(coordinates):
    return "{:.3f},{:.3f}".format(*coordinates)


def toward(start, end, distance):
    length = sum(abs(a - b) for a, b in zip(start, end))
    return tuple(a + (b - a) * distance / length for a, b in zip(start, end))


def rounded_wire(positions, edges):
    successors = dict(edges)
    pieces = []
    while successors:
        start_index = next(iter(successors))
        index = start_index
        cycle = []
        while True:
            cycle.append(positions[index])
            index = successors.pop(index)
            if index == start_index:
                break
        corners = [
            (toward(p, cycle[i - 1], 2.1), p,
             toward(p, cycle[(i + 1) % len(cycle)], 2.1))
            for i, p in enumerate(cycle)
        ]
        pieces.append("M" + point(corners[-1][2]))
        for before, pivot, after in corners:
            pieces.extend(("L" + point(before), "Q" + point(pivot), point(after)))
        pieces.append("Z")
    return " ".join(pieces)


def crossing_center(positions, edges, under, over):
    u1, u2 = (positions[i] for i in edges[under])
    o1, o2 = (positions[i] for i in edges[over])
    over_vertical = o1[0] == o2[0]
    assert over_vertical != (u1[0] == u2[0])
    if over_vertical:
        center = o1[0], u1[1]
    else:
        center = u1[0], o1[1]
    for p, q in ((u1, u2), (o1, o2)):
        assert all(min(a,b) <= v <= max(a,b) for a,b,v in zip(p,q,center))
    return center, over_vertical


def draw_link(layout, x, y, marked, *, flipped=False):
    positions, edges, crossings = layout
    xmin, xmax = min(a for a, _ in positions), max(a for a, _ in positions)
    ymin, ymax = min(b for _, b in positions), max(b for _, b in positions)
    scale = min(121 / (xmax - xmin), 99 / (ymax - ymin))
    positions = [(x + (a - (xmin + xmax) / 2) * scale,
                  y + (b - (ymin + ymax) / 2) * scale) for a, b in positions]
    output = [f'<path d="{rounded_wire(positions, edges)}" fill="none" '
              f'stroke="{INK}" stroke-width="1.14"/>']
    for under, over, _, label in crossings:
        if flipped and label == marked:
            under, over = over, under
        (cx, cy), vertical = crossing_center(positions, edges, under, over)
        gap = 2.65
        end = (f"M{cx:.3f},{cy-gap:.3f}v{2*gap}" if vertical
               else f"M{cx-gap:.3f},{cy:.3f}h{2*gap}")
        output.append(f'<rect x="{cx-gap:.3f}" y="{cy-gap:.3f}" '
                      f'width="{2*gap}" height="{2*gap}" fill="white"/>')
        output.append(f'<path d="{end}" fill="none" stroke="{INK}" stroke-width="1.14"/>')
        if label == marked:
            half = 4.15
            output.append(f'<rect x="{cx-half:.3f}" y="{cy-half:.3f}" width="{2*half}" '
                          f'height="{2*half}" fill="none" stroke="{RED}" stroke-width="0.90"/>')
    return output


def diagram_label(name, x, y):
    mirror_bar = "" if name in {"A", "B", "C", "D"} else (
        f'<path d="M{x-6.5},{y-9.2}h9.2" stroke="{INK}" stroke-width=".55"/>'
    )
    return (f'<text x="{x}" y="{y}" text-anchor="middle" font-size="11.5">'
            f'<tspan font-style="italic">{name[0]}</tspan>'
            f'<tspan dy="2.8" font-size="8">2</tspan></text>{mirror_bar}')


def note(label, x, y, color=INK, anchor="middle"):
    return (f'<text x="{x}" y="{y}" fill="{color}" '
            f'text-anchor="{anchor}" font-size="9.2">{label}</text>')


def arrow(x1, y1, x2, y2, label, switch, *, vertical=False):
    color = RED if switch else BLUE
    dash = "" if switch else ' stroke-dasharray="2.2 1.65"'
    line = (f'<path d="M{x1},{y1}L{x2},{y2}" fill="none" stroke="{color}" '
            f'stroke-width=".9"{dash} marker-end="url(#{"change" if switch else "identify"})"/>')
    if vertical:
        return line + note(label, x1 + 6.5, (y1 + y2) / 2 + 3.2, color, "start")
    return line + note(label, (x1 + x2) / 2, y1 - 5.5, color)


def verify_indexed_switch(before, after, marked):
    """Match the signed indexed PD to the retained after-diagram."""
    before = before.copy()
    before.crossings[marked].rotate_by_90()
    # Recompute crossing signs and arc orientation after the local switch.
    for cross in before.crossings:
        cross._clear()
    before = Link(before.crossings)
    assert [c.sign for c in before.crossings] == [c.sign for c in after.crossings]
    indices = {c: i for i, c in enumerate(before.crossings)}
    targets = {c: i for i, c in enumerate(after.crossings)}
    # A half-turn of the ports preserves which strand is over.
    for first_shift in (0, 2):
        shifts = {0: first_shift}
        remaining = [0]
        valid = True
        while remaining and valid:
            i = remaining.pop()
            a, b = before.crossings[i], after.crossings[i]
            for j in range(4):
                aj, ap = a.adjacent[(j + shifts[i]) % 4]
                bj, bp = b.adjacent[j]
                k = indices[aj]
                shift = (ap - bp) % 4
                if k != targets[bj] or shift % 2 or shifts.get(k, shift) != shift:
                    valid = False
                    break
                if k not in shifts:
                    shifts[k] = shift
                    remaining.append(k)
        if valid and len(shifts) == len(indices):
            return
    raise AssertionError("Saved PD does not follow by the marked crossing switch")


def main():
    source, out = Path(sys.argv[1]), Path(sys.argv[2])
    out.mkdir(parents=True, exist_ok=True)
    record = json.loads(source.read_text())
    panels = {}
    for before, after in STAGES:
        a, b = Link(record[before]["pd_code"]), Link(record[after]["pd_code"])
        assert [c.sign for c in a.crossings] == record[before]["signs"]
        assert [c.sign for c in b.crossings] == record[after]["signs"]
        marked = record[before]["switched_crossing"]
        verify_indexed_switch(a, b, marked)
        for i, cross in enumerate(a.crossings):
            cross.label = i
        layout = OrthogonalLinkDiagram(a).plink_data()
        panels[before] = (layout, marked, False)
        panels[after] = (layout, marked, True)
    elements = [
        arrow(134, 67, 169, 67, "switch 1", True),
        arrow(299, 67, 334, 67, "identify", False),
        arrow(400, 123, 400, 150, "switch 2", True, vertical=True),
        arrow(335, 204, 300, 204, "identify", False),
        arrow(170, 204, 135, 204, "switch 3", True),
    ]
    for diagram, (layout, marked, flipped) in panels.items():
        x = CENTERS[diagram]
        y = 68 if diagram in TOP else 203
        elements.extend(draw_link(layout, x, y, marked, flipped=flipped))
        elements.append(diagram_label(diagram, x, 12 if diagram in TOP else 265))
    marker = lambda name, color: (
        f'<marker id="{name}" markerWidth="7" markerHeight="6" refX="6.1" '
        f'refY="3" orient="auto" markerUnits="userSpaceOnUse">'
        f'<path d="M0,0L7,3L0,6L1.6,3Z" fill="{color}"/></marker>'
    )
    svg = (f'<svg xmlns="http://www.w3.org/2000/svg" width="{WIDTH}pt" height="{HEIGHT}pt" '
           f'viewBox="0 0 {WIDTH} {HEIGHT}"><title>Three crossing changes</title>'
           f'<defs>{marker("change", RED)}{marker("identify", BLUE)}</defs>'
           f'<g font-family="Latin Modern Roman, serif" fill="{INK}">\n'
           + "\n".join(elements) + "\n</g></svg>\n")
    path = out / "trefoil-movie.svg"
    path.write_text(svg, encoding="utf-8")
    subprocess.run(["inkscape", str(path), "--export-text-to-path",
                    f"--export-filename={path.with_suffix('.pdf')}"], check=True)


if __name__ == "__main__":
    main()
