#!/usr/bin/env python3
"""Check each ideal Pachner replacement as a labelled bipyramid.

Tet and vertex identifiers are exact. At each ideal vertex of the bipyramid
the truncated patch is a disk. Relative normal curves with the same oriented
outer boundary crossings represent the same peripheral class on this patch.
"""

import argparse
from collections import Counter
from itertools import groupby, permutations
import json
from pathlib import Path
from export_section2_triangulations import cusp_potential, check_curves

TIPS = {3, 4}
V = range(4)
BIPYRAMID3 = [TIPS | {i, (i + 1) % 3} for i in range(3)]


def face_key(chart, face):
    return frozenset(chart[i] for i in V if i != face)


def face(tet, f):
    return tet["neighbor"][f], tet["gluing"][f]


def invert(mapping, n):
    inverse = [-1] * n
    for i, j in enumerate(mapping):
        if j >= 0:
            assert inverse[j] == -1
            inverse[j] = i
    return inverse


def small_charts(tets, retained, tet, f):
    neighbor, p = face(tets[tet], f)
    if neighbor == tet or retained[neighbor] >= 0:
        return None
    chart0, chart1 = [3] * 4, [4] * 4
    for label, v in enumerate(v for v in V if v != f):
        chart0[v] = label
        chart1[p[v]] = label
    return {tet: chart0, neighbor: chart1}


def big_charts(tets, local_tets, first_chart):
    start = min(local_tets)
    result = {start: list(first_chart)}
    todo = [start]
    while todo:
        tet = todo.pop()
        chart = result[tet]
        for f in V:
            key = face_key(chart, f)
            if not TIPS <= key:
                continue
            neighbor, p = face(tets[tet], f)
            if neighbor == tet or neighbor not in local_tets:
                return None
            two_sets = [vs for vs in BIPYRAMID3 if key < vs]
            assert len(two_sets) == 2
            missing_vertex = next(iter(next(vs for vs in two_sets if vs != set(chart)) - key))
            chart_next = [missing_vertex] * 4
            for i in V:
                if i != f:
                    chart_next[p[i]] = chart[i]
            if neighbor in result:
                if result[neighbor] != chart_next:
                    return None
            else:
                result[neighbor] = chart_next
                todo.append(neighbor)
    if len(result) != 3 or len({frozenset(c) for c in result.values()}) != 3:
        return None
    return result


def outer(chart, side, small):
    key = face_key(chart, side)
    return key != {0, 1, 2} if small else not TIPS <= key


def outside_faces(charts, small):
    return {face_key(chart, f): (i, f)
            for i, chart in charts.items() for f in V if outer(chart, f, small)}


def pruned_matches(old, new, retained, old_charts, new_charts):
    """Match every attaching face and every vertex identification on it."""
    old_f = outside_faces(old_charts, True)
    new_f = outside_faces(new_charts, False)
    assert len(old_f) == len(new_f) == 6 and set(old_f) == set(new_f)
    corner_cusps = {}
    for state, charts in [(old, old_charts), (new, new_charts)]:
        for i, chart in charts.items():
            for v, a in enumerate(chart):
                if a in corner_cusps and corner_cusps[a] != state[i]["cusp"][v]:
                    return False
                corner_cusps[a] = state[i]["cusp"][v]
    for key in old_f:
        i, f = old_f[key]
        ii, ff = new_f[key]
        j, p = face(old[i], f)
        jj, pp = face(new[ii], ff)
        if j in old_charts:
            j_key = face_key(old_charts[j], p[f])
            if (jj, pp[ff]) != new_f[j_key]:
                return False
            for v in key:
                vo, vn = old_charts[i].index(v), new_charts[ii].index(v)
                if old_charts[j][p[vo]] != new_charts[jj][pp[vn]]:
                    return False
        else:
            if jj != retained[j] or pp[ff] != p[f]:
                return False
            for v in key:
                if p[old_charts[i].index(v)] != pp[new_charts[ii].index(v)]:
                    return False
        # Matching fluxes on each boundary side of each truncated ideal vertex.
        for v in key:
            vo, vn = old_charts[i].index(v), new_charts[ii].index(v)
            for sheet_coord in range(4):
                if old[i]["curve"][16 * sheet_coord + 4 * vo + f] != new[ii]["curve"][16 * sheet_coord + 4 * vn + ff]:
                    return False
    for i, ii in enumerate(retained):
        if ii < 0:
            continue
        if old[i]["curve"] != new[ii]["curve"] or old[i]["cusp"] != new[ii]["cusp"]:
            return False
        for f in V:
            j, p = face(old[i], f)
            if j not in old_charts and face(new[ii], f) != (retained[j], p):
                return False
    return True


def witness(small, big, retained, candidates):
    local_tets = {i for i, value in enumerate(invert(retained, len(big))) if value < 0}
    assert len(local_tets) == 3
    for tet, f in candidates:
        small_labels = small_charts(small, retained, tet, f)
        if small_labels is None:
            continue
        for chart in (perm for label_set in BIPYRAMID3 for perm in permutations(sorted(label_set))):
            big_labels = big_charts(big, local_tets, chart)
            if big_labels is None:
                continue
            if pruned_matches(small, big, retained, small_labels, big_labels):
                return small_labels, big_labels
    return None


def check_step(before, after):
    event = after["event"]
    old, new, retained = before["tets"], after["tets"], after["oldToNew"]
    if event == "2-3":
        labels = witness(old, new, retained, [(after["removed"], after["side"])])
        assert labels is not None, (after["label"], event, len(old), after["removed"], after["side"])
        before_labels, after_labels = labels
    else:
        assert event == "3-2", event
        inverted = invert(retained, len(new))
        local_after = [i for i, value in enumerate(inverted) if value < 0]
        labels = witness(new, old, inverted, [(local_after[0], f) for f in V])
        assert labels is not None, (after["label"], event, len(old), after["removed"], after["side"])
        after_labels, before_labels = labels
    return {"beforeCharts": [before_labels.get(i, []) for i in range(len(old))],
            "afterCharts": [after_labels.get(i, []) for i in range(len(new))],
            "oldToNew": retained, "kind": event, "target": new}


def group_trace(items):
    start = items.index(next(x for x in items if x["event"] == "proto_begin"))
    items = items[start:]
    assert items[-1]["event"] == "proto_end"
    assert items[-2]["event"] == "tidy"
    assert items[-1]["tets"] == items[-2]["tets"]
    for u, v in zip(items[-3]["tets"], items[-1]["tets"]):
        assert all(u[x] == v[x] for x in ("neighbor", "gluing", "cusp"))
    return {"raw": items[0]["tets"],
            "moves": [check_step(x, y) for x, y in zip(items[:-3], items[1:-2])]}


def set_terminal_marking(trace, canon):
    terminal = trace["moves"][-1]["target"] if trace["moves"] else trace["raw"]
    assert len(terminal) == len(canon["faces"])
    for i, tet in enumerate(terminal):
        assert [list(face(tet, side)) for side in V] == canon["faces"][i]
        assert tet["cusp"] == canon["cusp_indices"][i]
        for generator in range(2):
            canon["curves"][generator][i] = [
                [tet["curve"][32*generator + 4*v + side] for side in V] for v in V
            ]
            assert not any(tet["curve"][32*generator + 16 : 32*generator + 32])
    check_curves(canon)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("trace", type=Path)
    parser.add_argument("canonical", type=Path)
    parser.add_argument("output", type=Path)
    args = parser.parse_args()
    with args.trace.open() as fh:
        data = {name: group_trace(list(group))
                for name, group in groupby(map(json.loads, fh), key=lambda x: x["label"])}
    matches = json.loads(args.canonical.read_text())
    for match in matches["parity_matches"]:
        for side in ("source", "target"):
            name = f'{match["seed"]}:{match["label"]}:{side}'
            set_terminal_marking(data[name], match[side])
        match["potential"] = [cusp_potential(match["source"], match["target"], match["tet_map"],
                                              match["cusp_maps"], g) for g in range(2)]
        assert all(p is not None for p in match["potential"])
    args.output.with_name('matched-pachner.json').write_text(json.dumps(matches, separators=(",", ":")) + "\n")
    for label, trace in data.items():
        print(label, dict(Counter(x["kind"] for x in trace["moves"])))
    args.output.write_text(json.dumps(data, separators=(",", ":")) + "\n")


if __name__ == "__main__":
    main()
