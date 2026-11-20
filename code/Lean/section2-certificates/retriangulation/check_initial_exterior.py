#!/usr/bin/env python3
"""Check initial marked octahedral exterior arrays directly from signed PD."""

import argparse
from collections import defaultdict
from itertools import groupby
import json
from pathlib import Path

V = tuple(range(4))
DIRS = ("Yb", "Xf", "Yf", "Xb")


def signed_projection(data):
    codes, signs = data["pd"], data["crossing_signs"]
    assert len(codes) == len(signs) and all(s in (-1, 1) for s in signs)
    occurrence = defaultdict(list)
    graph = defaultdict(set)
    for c, ports in enumerate(codes):
        assert len(ports) == 4
        for v, a in enumerate(ports):
            occurrence[a].append((c,v))
            graph[a].add(ports[(v+2)%4])
    assert all(len(xs) == 2 for xs in occurrence.values())
    components = {}
    num_components = 0
    for first in sorted(graph):
        if first in components:
            continue
        todo = [first]
        while todo:
            a = todo.pop()
            if a not in components:
                components[a] = num_components
                todo.extend(graph[a])
        num_components += 1
    neighbors = []
    component_labels = []
    for c, ports in enumerate(codes):
        a = {}
        b = {}
        for v, label in enumerate(ports):
            d, w = next(x for x in occurrence[label] if x != (c,v))
            direction = DIRS[(v - int(signs[c] < 0))%4]
            target = DIRS[(w - int(signs[d] < 0))%4][0]
            a[direction] = (d, target)
            b[direction[0]] = components[label]
        neighbors.append(a)
        component_labels.append(b)
    return signs, neighbors, component_labels, num_components


def octahedral_exterior(data):
    signs, neighbors, component, count = signed_projection(data)
    tets = []
    forward_longitude = []
    for c, (sign, xys) in enumerate(zip(signs, component)):
        n = [[None] * 4 for _ in V]
        mus = [[0] * 16 for _ in V]
        lambdas = [[0] * 16 for _ in V]

        # All tetrahedra at this crossing have the two suspension poles
        # and one vertex on each link strand.
        if sign == 1:
            inside = ((1,3), (0,2), (3,1), (2,0))
        else:
            inside = ((3,1), (2,0), (1,3), (0,2))
        for i, (a, b) in enumerate(inside):
            n[i][0], n[i][1] = 4*c + a, 4*c + b
        # Each pair consists of (tet, face, adjacent tet type for X, type for Y).
        table = (("Xb", ((2,3,3,0), (1,2,0,1))),
                 ("Xf", ((0,3,1,2), (3,2,2,3))),
                 ("Yb", ((3,3,3,0), (2,2,0,1))),
                 ("Yf", ((1,3,1,2), (0,2,2,3))))
        for d, entries in table:
            other, strand = neighbors[c][d]
            for tet, f, j, k in entries:
                n[tet][f] = 4*other + (j if strand == "X" else k)
        for i, ns in enumerate(n):
            cusp = [-2, -1, xys["X"], xys["Y"]]
            if i % 2 == 1:
                cusp[2], cusp[3] = cusp[3], cusp[2]
            tets.append({"neighbor": ns, "gluing": [[0,1,3,2]]*4,
                         "cusp": cusp, "curve": [0]*64})

        xs, ys = (0,1) if sign == 1 else (1,0)
        loops = ((2,2,3,1), (3,3,2,-1), (2,2,xs,-1), (3,3,xs,1),
                 (3,2,3,1), (0,3,2,-1), (3,2,ys,-1), (0,3,ys,1))
        for j, v, f, n in loops:
            tets[4*c+j]["curve"][32+4*v+f] = n

    def over(c, xy):
        return (signs[c] == 1) == (xy == "X")

    # Place one meridian at the first over-under transition encountered
    # from the first X strand of this component.
    done = set()
    for initial_c in range(len(signs)):
        cusp = component[initial_c]["X"]
        if cusp in done:
            continue
        cur, xy = initial_c, "X"
        for _ in range(2*len(signs)):
            after, following = neighbors[cur][xy+"f"]
            if over(cur, xy) and not over(after, following):
                break
            cur, xy = after, following
        else:
            raise ValueError("component lacks an over-under transition")
        at_over = ((3,3,1,-1), (3,3,2,1), (0,2,1,1), (0,2,3,-1)) if xy == "X" else (
                   (0,3,1,-1), (0,3,2,1), (1,2,1,1), (1,2,3,-1))
        at_under = ((1,3,0,-1), (1,3,2,1), (2,2,0,1), (2,2,3,-1)) if following == "X" else (
                    (2,3,0,-1), (2,3,2,1), (3,2,0,1), (3,2,3,-1))
        for crossing, meridian in ((cur, at_over), (after, at_under)):
            for j,v,f,n in meridian:
                tets[4*crossing+j]["curve"][4*v+f] = n
        done.add(cusp)
    assert len(done) == count

    self_writhe = [0]*count
    for sign, xys in zip(signs, component):
        if xys["X"] == xys["Y"]:
            self_writhe[xys["X"]] += sign
    for tet in tets:
        for v in (2,3):
            for f in V:
                tet["curve"][32+4*v+f] -= self_writhe[tet["cusp"][v]]*tet["curve"][4*v+f]
    return tets


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("trace", type=Path)
    parser.add_argument("data", type=Path)
    args = parser.parse_args()
    with args.trace.open() as source:
        initial = {name: next(group) for name, group in
                   groupby(map(json.loads, source), key=lambda x: x["label"])}
    for match in json.loads(args.data.read_text())["parity_matches"]:
        for side in ("source", "target"):
            label = f'{match["seed"]}:{match["label"]}:{side}'
            state = initial[label]
            assert state["event"] == "finite_removal_begin"
            wanted = octahedral_exterior(match[side+"_diagram"])
            assert wanted == state["tets"], label
            print(f"{label}: {len(wanted)} tetrahedra, exact incidence and marked peripheral curves")


if __name__ == "__main__":
    main()
