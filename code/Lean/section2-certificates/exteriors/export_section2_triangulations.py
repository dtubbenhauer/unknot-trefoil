#!/usr/bin/env python3
"""Export explicit tetrahedral maps and integral cusp-chain witnesses."""
from collections import deque
from itertools import permutations
from pathlib import Path
from argparse import ArgumentParser
import json

import verify_trefoil as replay
from spherogram import Link
import snappy


VERTICES = range(4)
PERMUTATIONS = list(permutations(VERTICES))


def parity(permutation):
    return sum(permutation[i] > permutation[j] for i in VERTICES for j in range(i+1, 4)) % 2


def side_orientation(v, face):
    i, j = (u for u in VERTICES if u != v and u != face)
    return (j, i) if (v + face - int(v < face)) % 2 else (i, j)


def triangulation_data(manifold):
    """Tetrahedron pairings and outward signed normal-arc counts."""
    pairings = manifold._get_tetrahedra_gluing_data()
    cusps, data = manifold._get_cusp_indices_and_peripheral_curve_data()
    assert all(c >= 0 for tet_cusps in cusps for c in tet_cusps)
    assert all(not any(data[4*t+sheet]) for t in range(len(pairings)) for sheet in (1, 3))
    return {
        'faces': [list(zip(neighbors, perms)) for neighbors, perms in pairings],
        'cusp_indices': cusps,
        'curves': [[[[data[4*t+2*g][4*v+f] for f in VERTICES] for v in VERTICES]
                    for t in range(len(pairings))] for g in range(2)],
    }


def propagate(source, target, t0, p0, cusp_map):
    """Extend a tetrahedron/vertex map by the face pairing identity."""
    maps = {0: (t0, p0)}
    queue = deque([0])
    while queue:
        s = queue.popleft()
        t, p = maps[s]
        if any(target['cusp_indices'][t][p[v]] != cusp_map[source['cusp_indices'][s][v]]
               for v in VERTICES):
            return None
        for f, (s1, g) in enumerate(source['faces'][s]):
            t1, h = target['faces'][t][p[f]]
            q = [None] * 4
            for v in VERTICES:
                q[g[v]] = h[p[v]]
            candidate = (t1, tuple(q))
            if s1 in maps:
                if maps[s1] != candidate:
                    return None
            else:
                maps[s1] = candidate
                queue.append(s1)
    count = len(source['faces'])
    if len(maps) != count or len({t for t, _ in maps.values()}) != count:
        return None
    return [maps[i] for i in range(count)]


def cusp_potential(source, target, maps, cusp_matrices, generator):
    """Find a dual-2-chain bounded by the difference of the two curves.

    A coefficient attaches to a vertex of the *primal* cusp triangulation.
    Its contribution to the dual of a directed primal edge is the
    coefficient at the edge's terminal vertex minus that at its initial
    vertex. Corner representatives are matched across glued sides.
    """
    graph = {}
    properties = target['faces']
    count = len(properties)

    def constrain(a, b, difference):
        graph.setdefault(a, []).append((b, difference))
        graph.setdefault(b, []).append((a, -difference))

    for s, (t, p) in enumerate(maps):
        for v in VERTICES:
            first = cusp_matrices[source['cusp_indices'][s][v]][0][generator]
            second = cusp_matrices[source['cusp_indices'][s][v]][1][generator]
            tv = p[v]
            for sf in VERTICES:
                if sf == v:
                    assert source['curves'][generator][s][v][sf] == 0
                    continue
                tf = p[sf]
                tt, g = properties[t][tf]
                i, j = side_orientation(tv, tf)
                constrain((t, tv, i), (tt, g[tv], g[i]), 0)
                constrain((t, tv, j), (tt, g[tv], g[j]), 0)
                difference = source['curves'][generator][s][v][sf] - (
                    first * target['curves'][0][t][tv][tf] +
                    second * target['curves'][1][t][tv][tf]
                )
                constrain((t, tv, i), (t, tv, j), difference)

    potential = {}
    for start in graph:
        if start in potential:
            continue
        potential[start] = 0
        queue = deque([start])
        while queue:
            corner = queue.popleft()
            for neighbor, shift in graph[corner]:
                proposed = potential[corner] + shift
                if neighbor in potential:
                    if potential[neighbor] != proposed:
                        return None
                else:
                    potential[neighbor] = proposed
                    queue.append(neighbor)
    return [[[potential.get((t, v, w), 0) for w in VERTICES] for v in VERTICES]
            for t in range(count)]


def check_curves(triangulation):
    """Check that the exported fluxes are cycles on the dual cellulation."""
    for curve in triangulation['curves']:
        for t, faces in enumerate(triangulation['faces']):
            for v in VERTICES:
                assert curve[t][v][v] == 0
                assert sum(curve[t][v]) == 0
                for f, (u, p) in enumerate(faces):
                    if f != v:
                        assert curve[t][v][f] == -curve[u][p[v]][p[f]]


def match_data(label, source, target, sign, axes=None, seed=None):
    source_diagram = replay.diagram_data(source) if hasattr(source, 'PD_code') else None
    target_diagram = replay.diagram_data(target) if hasattr(target, 'PD_code') else None
    if hasattr(source, 'exterior'):
        source = source.exterior()
    if hasattr(target, 'exterior'):
        target = target.exterior()
    cs = source.canonical_retriangulation()
    ct = target.canonical_retriangulation()
    left, right = triangulation_data(cs), triangulation_data(ct)
    check_curves(left)
    check_curves(right)
    n = len(left['faces'])
    assert n == len(right['faces'])
    for witness in cs.isomorphisms_to(ct):
        cusp_images = [int(i) for i in witness.cusp_images()]
        cusp_maps = [replay.matrix_rows(m) for m in witness.cusp_maps()]
        if axes is not None and cusp_images[axes[0]] != axes[1]:
            continue
        if not all(m[0][1] == m[1][0] == 0 and m[0][0] in (-1, 1)
                   and m[1][1] == sign * m[0][0] for m in cusp_maps):
            continue
        assert witness.extends_to_link()
        for target_tet in range(n):
            for perm in PERMUTATIONS:
                if parity(perm) != (sign == -1):
                    continue
                mapping = propagate(left, right, target_tet, perm, cusp_images)
                if mapping is None:
                    continue
                potentials = [cusp_potential(left, right, mapping, cusp_maps, g)
                              for g in range(2)]
                if any(p is None for p in potentials):
                    continue
                return {
                    'label': label, 'seed': seed, 'sign': sign,
                    'source_axis': axes[0] if axes is not None else None,
                    'target_axis': axes[1] if axes is not None else None,
                    'source_raw_isosig': source.triangulation_isosig(decorated=True),
                    'target_raw_isosig': target.triangulation_isosig(decorated=True),
                    'source_canonical_isosig': cs.triangulation_isosig(decorated=True),
                    'target_canonical_isosig': ct.triangulation_isosig(decorated=True),
                    'source_diagram': source_diagram,
                    'target_diagram': target_diagram,
                    'source': left, 'target': right, 'tet_map': mapping,
                    'cusp_images': cusp_images, 'cusp_maps': cusp_maps,
                    'potential': potentials,
                }
    raise RuntimeError(f'cannot match {label} at {seed}')


def parity_matches(seed):
    a, b, c, d, e, _ = replay.stages(seed, True)
    _, _, v, _ = replay.split_start(a, 0, True)
    w = replay.reference(seed, True)
    for label, source, target, sign in [('partner_to_reference', v, w, -1),
                                        ('B_to_C', b, c, 1), ('D_to_E', d, e, -1)]:
        axes = replay.axis_cusp(source), replay.axis_cusp(target)
        yield match_data(label, source, target, sign, axes, seed)


def named_matches():
    a, b, c, d, e, _ = replay.stages(2, False)
    _, _, v, _ = replay.split_start(a, 0, False)
    for label, source, target, sign in [
        ('partner_to_reference', v, replay.reference(2, False), -1),
        ('partner_to_table', v, Link('K14a7385'), -1),
        ('B_to_C', b, c, 1),
        ('D_to_E', d, e, -1),
    ]:
        yield match_data(label, source, target, sign, seed=2)


def main():
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('output_path', type=Path)
    parser.add_argument('--named', action='store_true', help='also export the four m=2 matches')
    args = parser.parse_args()
    snappy.set_rand_seed(0)
    result = {'parity_matches': [m for seed in (0, 1) for m in parity_matches(seed)]}
    print([(m['seed'], m['label'], len(m['tet_map']), m['cusp_maps'])
           for m in result['parity_matches']])
    if args.named:
        result['named_matches'] = list(named_matches())
    args.output_path.write_text(json.dumps(result, separators=(',', ':')) + '\n')


if __name__ == '__main__':
    main()
