#!/usr/bin/env python3
"""Replay the three-change trefoil family certificate.

Dependencies: SnapPy 3.3.2 and Spherogram 2.4.1.
Run: python verify_trefoil.py [--json OUTPUT]
"""
from argparse import ArgumentParser
from fractions import Fraction
import json
import random
from pathlib import Path

import snappy
from spherogram import Crossing, Link
from spherogram.links.links_base import CrossingStrand
from spherogram.links.tangles import IntegerTangle, RationalTangle, Tangle

DT_CODES = (
    (4, 14, 20, -24, -26, -28, 16, 2, -22, -12, -30, -18, -8, -10, -6),
    (4, 14, 20, 22, 24, 16, -26, 2, -28, 10, 6, 8, -30, -12, -18),
    (-16, -14, -24, -18, -22, -20, -2, -4, -6, -8, -10, -12),
)
LOCATIONS = ((7, 10), (5, 9), (6, 4))
CF_PREFIXES = ((0, 1, 2), (0, 1, 2), (1, 2))
AXIS_LABELS = ("axis-lt", "axis-lb", "axis-rt", "axis-rb")


def axis_tangle():
    """Zero tangle augmented by a circle encircling both strands."""
    lt, lb, rt, rb = [Crossing(label) for label in AXIS_LABELS]
    lt[1] = lb[3]
    rt[0] = rb[2]
    lt[3] = rt[2]
    lb[1] = rb[0]
    lt[2] = rt[3]
    lb[2] = rb[3]
    return Tangle(2, [lt, lb, rt, rb], [lb[0], rb[1], lt[0], rt[1]])


def inner_box(m, augmented):
    twists = IntegerTangle(m)
    if augmented:
        return axis_tangle() + twists
    return twists


def reference(m, augmented):
    outside = RationalTangle(37, 104)
    return (inner_box(m, augmented) + outside).numerator_closure()


def stage(i, m, switch, augmented):
    parent = Link("DT: " + repr([DT_CODES[i]]))
    replace_at, switch_at = LOCATIONS[i]
    if switch:
        parent.crossings[switch_at].rotate_by_90()
    discarded = parent.crossings[replace_at]
    insert = inner_box(m, augmented)
    for entry in reversed(CF_PREFIXES[i]):
        insert = IntegerTangle(entry) + insert.invert()
    for new_port, old_port in enumerate((0, 1, 3, 2)):
        neighbor, neighbor_port = discarded.adjacent[old_port]
        neighbor[neighbor_port] = insert.adjacent[new_port]
    crossings = [c for c in parent.crossings if c != discarded] + insert.crossings
    for crossing in crossings:
        if isinstance(crossing, Crossing):
            crossing._clear()
    return Link(crossings)


def stages(m, augmented):
    return [stage(i, m, switch, augmented) for i in range(3) for switch in (False, True)]


def axis_cusp(diagram):
    expected = set(AXIS_LABELS)
    candidates = []
    for i, component in enumerate(diagram.link_components):
        labels = {entry.crossing.label for entry in component}
        if labels == expected and len(component) == len(expected):
            candidates.append(i)
    assert len(candidates) == 1, (expected, diagram.link_components)
    return candidates[0]


def matrix_rows(matrix):
    return [[int(matrix[i, j]) for j in range(2)] for i in range(2)]


def peripheral_map(source, target, sign, axis_indices=None):
    """Find a genuine combinatorial isomorphism after retriangulation.

    The canonical cell calculation may use floating point to choose a
    triangulation. The test on the resulting face pairings and the
    peripheral homology matrices is combinatorial and integral.
    """
    source_canon = source.canonical_retriangulation()
    target_canon = target.canonical_retriangulation()
    for witness in source_canon.isomorphisms_to(target_canon):
        destinations = [int(i) for i in witness.cusp_images()]
        cusp_maps = [matrix_rows(m) for m in witness.cusp_maps()]
        if axis_indices is not None and destinations[axis_indices[0]] != axis_indices[1]:
            continue
        if all(m[0][1] == m[1][0] == 0
               and m[0][0] in (-1, 1) and m[1][1] == sign * m[0][0]
               for m in cusp_maps):
            assert witness.extends_to_link()
            return {
                "source_axis": axis_indices[0] if axis_indices is not None else None,
                "target_axis": axis_indices[1] if axis_indices is not None else None,
                "cusp_images": destinations,
                "cusp_maps": cusp_maps,
                "source_triangulation": source_canon.triangulation_isosig(decorated=True),
                "target_triangulation": target_canon.triangulation_isosig(decorated=True),
            }
    raise AssertionError("Required peripheral-preserving combinatorial isomorphism was not found")


def signature_matrix(matrix):
    """Signature by exact symmetric elimination."""
    A = [[Fraction(entry) for entry in row] for row in matrix]
    answer = 0
    while A:
        i = next((i for i in range(len(A)) if A[i][i]), None)
        if i is None:
            off_diagonal = next(((i, j) for i in range(len(A)) for j in range(i + 1, len(A))
                                 if A[i][j]), None)
            if off_diagonal is None:
                break
            i, j = off_diagonal
            A[i] = [a + b for a, b in zip(A[i], A[j])]
            for row in A:
                row[i] += row[j]
        A[0], A[i] = A[i], A[0]
        for row in A:
            row[0], row[i] = row[i], row[0]
        pivot = A[0][0]
        answer += 1 if pivot > 0 else -1
        A = [[A[i][j] - A[i][0] * A[0][j] / pivot for j in range(1, len(A))]
             for i in range(1, len(A))]
    return answer


def knot_signature(diagram):
    """Gordon–Litherland signature in Spherogram's default convention."""
    face_of = {corner: i for i, face in enumerate(diagram.faces()) for corner in face}
    edges = [(face_of[CrossingStrand(c, p)], face_of[CrossingStrand(c, p + 2)], w, c)
             for c in diagram.crossings for p, w in ((0, 1), (1, -1))]
    vertices = {0}
    while True:
        neighbors = {a for a, b, _, _ in edges if b in vertices}
        neighbors.update(b for a, b, _, _ in edges if a in vertices)
        if neighbors <= vertices:
            break
        vertices.update(neighbors)
    ordered = sorted(vertices)
    position = {v: i for i, v in enumerate(ordered)}
    goeritz = [[0 for _ in ordered] for _ in ordered]
    correction = 0
    for a, b, weight, crossing in edges:
        if a not in vertices or b not in vertices:
            continue
        i, j = position[a], position[b]
        goeritz[i][i] -= weight
        goeritz[j][j] -= weight
        goeritz[i][j] += weight
        goeritz[j][i] += weight
        if weight == crossing.sign:
            correction += weight
    return -signature_matrix([row[1:] for row in goeritz[1:]]) - correction


def simplified(diagram, seed):
    result = diagram.copy()
    random.seed(seed)
    result.simplify("global")
    return result


def split_start(diagram, seed, augmented):
    reduced = simplified(diagram, seed)
    pieces = reduced.deconnect_sum()
    assert len(pieces) == 2, [len(piece.crossings) for piece in pieces]
    trefoils = [piece for piece in pieces
                if len(piece.link_components) == 1 and len(piece.crossings) == 3]
    assert len(trefoils) == 1
    trefoil = trefoils[0]
    partner = next(piece for piece in pieces if piece is not trefoil)
    assert len(partner.link_components) == 1 + bool(augmented)
    assert knot_signature(trefoil) == 2
    trefoil_labels = {c.label for c in trefoil.crossings}
    trefoil_crossings = {c for c in reduced.crossings if c.label in trefoil_labels}
    assert len(trefoil_crossings) == 3
    interface = [(c, port) for c in trefoil_crossings
                 for port, (other, _) in enumerate(c.adjacent)
                 if other not in trefoil_crossings]
    assert len(interface) == 2
    if augmented:
        axis_cusp(partner)
        axis = axis_cusp(reduced)
        assert all(c.strand_components[port] != axis for c, port in interface)
    arc_labels = sorted(int(c.strand_labels[port]) for c, port in interface)
    return reduced, trefoil, partner, arc_labels


def terminal(diagram, seed, augmented):
    result = simplified(diagram, seed)
    assert not result.crossings and not result.link_components
    assert result.unlinked_unknot_components == 1 + bool(augmented)


def diagram_data(diagram):
    return {"pd": [list(c) for c in diagram.PD_code()],
            "dt": [list(c) for c in diagram.DT_code()],
            "crossing_signs": [int(c.sign) for c in diagram.crossings],
            "crossing_labels": [c.label for c in diagram.crossings]}


def compare(source, target, sign, augmented):
    axes = (axis_cusp(source), axis_cusp(target)) if augmented else None
    return peripheral_map(source.exterior(), target.exterior(), sign, axes)


def filled_map(source, target, slope_sign):
    exterior = source.exterior()
    exterior.dehn_fill((1, slope_sign), axis_cusp(source))
    filled = exterior.filled_triangulation().with_hyperbolic_structure()
    return peripheral_map(filled, target.exterior(), 1)


def parity_certificate(b):
    A, B, C, D, E, F = stages(b, augmented=True)
    W = reference(b, augmented=True)
    for source in (A, B, C, D, E, F, W):
        axis_cusp(source)
    terminal(F, seed=0, augmented=True)
    reduced, trefoil, partner, sum_arc_labels = split_start(A, seed=0, augmented=True)
    certificate = {
        "seed": b,
        "stages": {label: diagram_data(diagram)
                   for label, diagram in zip("ABCDEF", (A, B, C, D, E, F))},
        "simplified_start": diagram_data(reduced),
        "sum_arc_labels": sum_arc_labels,
        "trefoil": diagram_data(trefoil),
        "trefoil_signature": knot_signature(trefoil),
        "partner": diagram_data(partner),
        "reference": diagram_data(W),
        "peripheral_checks": {
            "partner_to_reference": compare(partner, W, -1, augmented=True),
            "B_to_C": compare(B, C, 1, augmented=True),
            "D_to_E": compare(D, E, -1, augmented=True),
        },
        "terminal_unlinked_components": 2,
    }
    checks = {
        "W": (W, reference(b + 2, augmented=False), -1),
        "B": (B, stage(0, b + 2, True, augmented=False), 1),
        "C": (C, stage(1, b + 2, False, augmented=False), 1),
        "D": (D, stage(1, b + 2, True, augmented=False), 1),
        "E": (E, stage(2, b + 2, False, augmented=False), -1),
    }
    certificate["one_full_twist_checks"] = {
        label: {"slope": [1, sign], **filled_map(source, target, sign)}
        for label, (source, target, sign) in checks.items()
    }
    return certificate


def named_example():
    A, B, C, D, E, F = stages(2, augmented=False)
    W = reference(2, augmented=False)
    table = Link("K14a7385")
    reduced, trefoil, partner, sum_arc_labels = split_start(A, seed=0, augmented=False)
    terminal(F, seed=0, augmented=False)
    trefoil_signature = knot_signature(trefoil)
    partner_signature = knot_signature(partner)
    assert (trefoil_signature, partner_signature) == (2, -4)
    return {
        "stages": {label: diagram_data(diagram)
                   for label, diagram in zip("ABCDEF", (A, B, C, D, E, F))},
        "simplified_start": diagram_data(reduced),
        "sum_arc_labels": sum_arc_labels,
        "trefoil": diagram_data(trefoil),
        "partner": diagram_data(partner),
        "reference": diagram_data(W),
        "table_knot": diagram_data(table),
        "trefoil_signature": trefoil_signature,
        "partner_signature": partner_signature,
        "reference_signature": knot_signature(W),
        "table_signature": knot_signature(table),
        "peripheral_checks": {
            "partner_to_reference": compare(partner, W, -1, augmented=False),
            "partner_to_table": compare(partner, table, -1, augmented=False),
            "B_to_C": compare(B, C, 1, augmented=False),
            "D_to_E": compare(D, E, -1, augmented=False),
        },
        "terminal_unlinked_components": 1,
    }


def main():
    parser = ArgumentParser(description=__doc__)
    parser.add_argument("--json", type=Path, help="write the reconstructed certificate and PD codes here")
    args = parser.parse_args()
    certificate = {
        "augmented": [parity_certificate(b) for b in (0, 1)],
        "named_example": named_example(),
        "zero_twist_partner": compare(reference(0, False), Link("10_6"), 1, False),
    }
    for parity in certificate["augmented"]:
        print(f'parity {parity["seed"]}: trefoil signature {parity["trefoil_signature"]}, '
              f'endpoint unlink of {parity["terminal_unlinked_components"]} components')
        for label, check in parity["peripheral_checks"].items():
            print(f'  {label}: axis {check["source_axis"]} -> {check["target_axis"]}, '
                  f'maps {check["cusp_maps"]}')
    print("Zero-twist partner: meridian-preserving identification with 10_6 verified")
    example = certificate["named_example"]
    print(f'14a7385: trefoil signature {example["trefoil_signature"]}, '
          f'partner signature {example["partner_signature"]}, three ordinary changes verified')
    if args.json is not None:
        args.json.write_text(json.dumps(certificate, indent=2) + "\n")


if __name__ == "__main__":
    main()
