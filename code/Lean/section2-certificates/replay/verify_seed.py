"""Verify the ordinary three-change witness for the trefoil and B(245,104).

Requires SnapPy 3.3.2 and Spherogram 2.4.1. In a Python environment with
these packages, run Python on this file with assertions enabled.
"""
from fractions import Fraction
from itertools import combinations

import snappy  # supplies the SnapPy implementation of Link.exterior
from spherogram import Link, RationalTangle


# Each row lists a parent DT code, insertion index, switched index,
# and the fraction of the inserted rational tangle.
STAGES = (
    ((4,14,20,-24,-26,-28,16,2,-22,-12,-30,-18,-8,-10,-6), 7, 10, (5,7)),
    ((4,14,20,22,24,16,-26,2,-28,10,6,8,-30,-12,-18), 5, 9, (5,7)),
    ((-16,-14,-24,-18,-22,-20,-2,-4,-6,-8,-10,-12), 6, 4, (7,5)),
)


def stage_link(stage, switched=False):
    """Insert a tangle into the marked diagram, optionally switching one crossing."""
    dt, insert, switch, fraction = stage
    crossings = Link("DT: " + repr([dt])).crossings
    if switched:
        crossings[switch].rotate_by_90()
    tangle = RationalTangle(*fraction)
    replaced = crossings[insert]
    outside = tuple(replaced.adjacent)
    for new_port, old_port in enumerate((0,1,3,2)):
        neighbor, neighbor_port = outside[old_port]
        neighbor[neighbor_port] = tangle.adjacent[new_port]
    crossings = [c for c in crossings if c != replaced] + tangle.crossings
    for crossing in crossings:
        if hasattr(crossing, "_clear"):
            crossing._clear()
    return Link(crossings)


def exact_peripheral_map(source, target, degree):
    """Return a combinatorial isomorphism preserving the meridian up to sign."""
    left = source.exterior().canonical_retriangulation()
    right = target.exterior().canonical_retriangulation()
    for isometry in left.isomorphisms_to(right):
        matrix, = isometry.cusp_maps()
        determinant = matrix[0,0]*matrix[1,1] - matrix[0,1]*matrix[1,0]
        if abs(matrix[0,0]) == 1 and matrix[1,0] == 0 and determinant == degree:
            return isometry
    raise AssertionError("Required meridian-preserving isomorphism was not found.")


def inertia(rows):
    """Compute inertia by exact rational congruences."""
    matrix = [[Fraction(x) for x in row] for row in rows]
    positive, negative = 0, 0
    while matrix:
        dimension = len(matrix)
        pivot = next((i for i in range(dimension) if matrix[i][i]), None)
        if pivot is None:
            pair = next(((i,j) for i,j in combinations(range(dimension),2) if matrix[i][j]), None)
            if pair is None:
                break
            i, j = pair
            for r in range(dimension):
                matrix[r][i] += matrix[r][j]
            for c in range(dimension):
                matrix[i][c] += matrix[j][c]
            pivot = i
        scalar = matrix[pivot][pivot]
        positive += scalar > 0
        negative += scalar < 0
        keep = [j for j in range(dimension) if j != pivot]
        matrix = [[matrix[i][j] - matrix[i][pivot]*matrix[pivot][j]/scalar for j in keep]
                  for i in keep]
    return positive, negative


def signature(link):
    """Use the Gordon–Litherland formula with exact Goeritz inertia."""
    face_of = {tuple(c): i for i, face in enumerate(link.faces()) for c in face}
    edges = [(face_of[c[k]], face_of[c[k+2]], (-1)**k, c.sign)
             for c in link.crossings for k in (0,1)]
    face_class = {0}
    while True:
        expanded = face_class | {i for i,j,_,_ in edges if j in face_class} | {
            j for i,j,_,_ in edges if i in face_class}
        if expanded == face_class:
            break
        face_class = expanded
    vertex = {face: i for i, face in enumerate(sorted(face_class))}
    matrix = [[0 for _ in face_class] for _ in face_class]
    correction = 0
    for a,b,eps,sign in edges:
        if a not in face_class:
            continue
        i,j = vertex[a],vertex[b]
        if i != j:
            matrix[i][i] -= eps
            matrix[j][j] -= eps
            matrix[i][j] += eps
            matrix[j][i] += eps
        if eps == sign:
            correction += eps
    positive, negative = inertia([row[1:] for row in matrix[1:]])
    return negative - positive - correction


def verify():
    a,b,c,d,e,f = (stage_link(stage, switch) for stage in STAGES for switch in (False,True))
    for diagram in (a,b,c,d,e,f):
        assert len(diagram.link_components) == 1 and not diagram.unlinked_unknot_components
    print("B to C (preserving):", exact_peripheral_map(b,c,1))
    print("D to E (reversing):", exact_peripheral_map(d,e,-1))

    # Pickup is a strand isotopy plus Reidemeister simplification. The
    # decomposition cuts the simplified projection along a two-point circle.
    a.simplify("pickup")
    trefoil, partner = sorted(a.deconnect_sum(), key=lambda knot: len(knot.crossings))
    assert len(trefoil.crossings) == 3
    assert len(trefoil.link_components) == 1
    assert len(partner.crossings) == 14
    assert signature(trefoil) == 2 and signature(partner) == -4
    print("A splits as trefoil and partner, with signatures +2 and -4.")

    rational = RationalTangle(245,104).numerator_closure()
    tabular = Link("K14a7385")
    assert signature(rational) == signature(tabular) == 4
    print("Partner to B(245,104) (reversing):", exact_peripheral_map(partner,rational,-1))
    print("Partner to K14a7385 (reversing):", exact_peripheral_map(partner,tabular,-1))

    f.simplify("pickup")
    assert f.unlinked_unknot_components == 1 and not f.crossings
    print("F simplifies to a crossing-free unknot.")


if __name__ == "__main__":
    verify()
