#!/usr/bin/env python3
"""Draw the two verified augmented starts, including their summing curves."""
import argparse
import json
from pathlib import Path
import random
import subprocess

from shapely.geometry import LineString, Point, Polygon
from shapely.ops import substring, unary_union
from spherogram import Link
from spherogram.links.links_base import Strand
from spherogram.links.orthogonal import OrthogonalLinkDiagram


INK = "#20252b"
AXIS = "#68429b"
CUT = "#157968"


def pp(xy):
    return f"{xy[0]:.3f},{xy[1]:.3f}"


def toward(a, b, distance):
    length = abs(a[0] - b[0]) + abs(a[1] - b[1])
    assert length
    distance = min(distance, 0.37 * length)
    return tuple(p + (q - p) * distance / length for p, q in zip(a, b))


def rounded_projection(cycle, radius=1.8):
    corners = [(toward(p, cycle[i - 1], radius),
                p, toward(p, cycle[(i + 1) % len(cycle)], radius))
               for i, p in enumerate(cycle)]
    path = ["M", pp(corners[-1][2])]
    for a, pivot, b in corners:
        path.extend(("L", pp(a), "Q", pp(pivot), pp(b)))
    path.append("Z")
    return " ".join(path)


def line_axis(a, b):
    if a[0] == b[0]:
        return 1, a[0], sorted((a[1], b[1]))
    assert a[1] == b[1]
    return 0, a[1], sorted((a[0], b[0]))


def layout_projection(certificate):
    diagram = certificate["simplified_start"]
    link = Link(diagram["pd"])
    for i, crossing in enumerate(link.crossings):
        crossing.label = i
    random.seed(42)
    drawing = OrthogonalLinkDiagram(link)
    positions, arrows, crossings = drawing.plink_data()
    point_at_vertex = dict(zip(drawing.strand_CEPs, positions))
    vertical_over = {}
    point_at_crossing = {}
    over_segments = {}
    for under, over, _, label in crossings:
        ui, uk, u_bounds = line_axis(*(positions[i] for i in arrows[under]))
        oi, ok, o_bounds = line_axis(*(positions[i] for i in arrows[over]))
        assert ui != oi and u_bounds[0] < ok < u_bounds[1] and o_bounds[0] < uk < o_bounds[1]
        point_at_crossing[label] = (uk, ok) if ui else (ok, uk)
        vertical_over[label] = oi
        over_segments[label] = over

    axis = None
    trefoil_parts, outside_parts, paths = [], [], []
    interface_parts = []
    labels = diagram["crossing_labels"]
    wanted = set(certificate["trefoil"]["crossing_labels"])
    interfacial_arcs = set(certificate["sum_arc_labels"])
    witnessed_interfaces = set()

    def point(cep):
        if isinstance(cep.crossing, Strand):
            return point_at_vertex[cep]
        return point_at_crossing[cep.crossing.label]

    for component, cycle in enumerate(drawing.link.link_components):
        crossing_indices = [i for i, cep in enumerate(cycle)
                            if not isinstance(cep.crossing, Strand)]
        component_labels = {labels[cycle[i].crossing.label] for i in crossing_indices}
        if component_labels == {"axis-lt", "axis-lb", "axis-rt", "axis-rb"}:
            assert axis is None
            axis = component
            paths.append([point(cep) for cep in cycle if cep in point_at_vertex])
            axis_path = LineString([point(cep) for cep in cycle] + [point(cycle[0])])
            continue
        paths.append([point(cep) for cep in cycle if cep in point_at_vertex])
        for i, j in zip(crossing_indices, crossing_indices[1:] + [crossing_indices[0]]):
            steps = cycle[i : j + 1] if i < j else cycle[i:] + cycle[: j + 1]
            line = LineString([point(cep) for cep in steps])
            x, y = (labels[cycle[k].crossing.label] in wanted for k in (i, j))
            if x and y:
                trefoil_parts.append(line)
            elif x or y:
                fraction = min(0.26, 6 / line.length)
                taken = (substring(line, 0, fraction, normalized=True) if x
                         else substring(line, 1 - fraction, 1, normalized=True))
                outside = (substring(line, fraction, 1, normalized=True) if x
                           else substring(line, 0, 1 - fraction, normalized=True))
                trefoil_parts.append(taken)
                interface_parts.append(outside)
                outside_parts.append(outside)
                witnessed_interfaces.add(cycle[j].strand_label())
            else:
                outside_parts.append(line)

    assert axis is not None and len(trefoil_parts) == 7
    assert witnessed_interfaces == interfacial_arcs
    trefoil_ink = unary_union(trefoil_parts)
    outside_ink = unary_union(outside_parts)

    def is_summing_curve(candidate):
        boundary = candidate.exterior
        cuts = boundary.intersection(outside_ink)
        return (cuts.geom_type == "MultiPoint" and len(cuts.geoms) == 2
                and all(boundary.intersection(segment).geom_type == "Point"
                        and not boundary.intersection(segment).is_empty
                        for segment in interface_parts)
                and not boundary.intersects(axis_path)
                and not candidate.contains(axis_path)
                and all(candidate.contains(Point(point_at_crossing[i])) == (label in wanted)
                        for i, label in enumerate(labels)))

    inset = 3.0
    smooth = trefoil_ink.convex_hull.buffer(inset, quad_segs=6)
    narrow = trefoil_ink.buffer(inset, quad_segs=6)
    chosen = next((shape for shape in (smooth, narrow)
                   if shape.geom_type == "Polygon" and is_summing_curve(shape)), None)
    assert chosen is not None
    curve = chosen.exterior
    dots = list(curve.intersection(outside_ink).geoms)
    over_component = {
        label: drawing.strand_CEP_to_component[drawing.strand_CEPs[arrows[over][0]]]
        for label, over in over_segments.items()
    }
    return positions, paths, point_at_crossing, over_component, vertical_over, axis, list(curve.coords), dots


def panel(cert, x, y, width, height, rotate=False):
    points, paths, centers, over_component, vertical_over, axis, curve, dots = layout_projection(cert)
    all_points = points + curve
    x_min, y_min = (min(point[i] for point in all_points) for i in range(2))
    x_max, y_max = (max(point[i] for point in all_points) for i in range(2))
    scale = min(width / (x_max - x_min), height / (y_max - y_min))
    scale *= -1 if rotate else 1
    x0 = x - scale * (x_max + x_min) / 2
    y0 = y - scale * (y_max + y_min) / 2
    def t(xy):
        return (x0 + scale * xy[0], y0 + scale * xy[1])

    c = [t(p) for p in curve]
    out = [
        f'<path d="M{pp(c[0])} L{" ".join(map(pp, c[1:]))} Z" fill="#eef8f5" />'
    ]
    for component, vertices in enumerate(paths):
        color = AXIS if component == axis else INK
        weight = 1.45 if component == axis else 1.05
        out.append(f'<path d="{rounded_projection(list(map(t, vertices)))}" fill="none" '
                   f'stroke="{color}" stroke-width="{weight}"/>')
    for i, point in centers.items():
        cx, cy = t(point)
        fill = "#eef8f5" if Polygon(curve).contains(Point(point)) else "white"
        gap = 2.25
        ends = f"M{cx},{cy-gap}v{2*gap}" if vertical_over[i] else f"M{cx-gap},{cy}h{2*gap}"
        color = AXIS if over_component[i] == axis else INK
        weight = 1.45 if over_component[i] == axis else 1.05
        out.append(f'<rect x="{cx-gap}" y="{cy-gap}" width="{2*gap}" height="{2*gap}" fill="{fill}"/>')
        out.append(f'<path d="{ends}" fill="none" stroke="{color}" stroke-width="{weight}"/>')
    out.append(f'<path d="M{pp(c[0])} L{" ".join(map(pp, c[1:]))} Z" fill="none" '
               f'stroke="{CUT}" stroke-width=".95" stroke-dasharray="3.1 2.2"/>')
    for dot in dots:
        dx, dy = t((dot.x, dot.y))
        out.append(f'<circle cx="{dx}" cy="{dy}" r="2" fill="{CUT}" stroke="white" stroke-width=".62"/>')
    return out


def build(source, output):
    data = json.loads(source.read_text())["augmented"]
    with output.with_suffix(".svg").open("w") as f:
        f.write('<svg xmlns="http://www.w3.org/2000/svg" width="444pt" height="171pt" viewBox="0 0 444 171">\n')
        f.write('<g font-family="Latin Modern Roman, serif" fill="#20252b" stroke-linejoin="round">\n')
        for i, cert in enumerate(data):
            x = 110 + 224*i
            f.write("\n".join(panel(cert, x, 71, 207, 126, rotate=(i == 1))))
            f.write(f'<text x="{x}" y="148" text-anchor="middle" font-size="11"><tspan font-style="italic">b</tspan> = {i}</text>\n')
        f.write(f'<path d="M114,163h15" stroke="{AXIS}" stroke-width="1.45"/>'
                f'<text x="134" y="166" font-size="9.5">crossing circle <tspan font-style="italic">c</tspan></text>'
                f'<path d="M234,163h15" stroke="{CUT}" stroke-width=".95" stroke-dasharray="3.1 2.2"/>'
                '<text x="254" y="166" font-size="9.5">summing curve</text>\n')
        f.write('</g></svg>\n')
    subprocess.run(["inkscape", str(output.with_suffix(".svg")), "--export-text-to-path",
                    f"--export-filename={output.with_suffix('.pdf')}"], check=True)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("source", type=Path)
    parser.add_argument("output", type=Path)
    args = parser.parse_args()
    build(args.source, args.output)
