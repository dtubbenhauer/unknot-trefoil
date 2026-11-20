#!/usr/bin/env python3
"""Export local Section 2 move witnesses from the pinned Spherogram replay."""
from pathlib import Path
import argparse
import importlib.util
import random
import sys
from contextlib import ExitStack
from unittest.mock import patch
import json
import spherogram.links.simplify as simplify
from spherogram import Crossing, Link
from spherogram.links.links_base import CrossingStrand

def load_verifier(path):
    spec = importlib.util.spec_from_file_location("verify_trefoil", path)
    verifier = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(verifier)
    return verifier

def rotate(dart, offset):
    return 4 * (dart // 4) + (dart % 4 + offset) % 4

class Recorder:
    def __init__(self, diagram):
        self.link = diagram.copy()
        self.ids = {c: i for i, c in enumerate(self.link.crossings)}
        self.states = [self.snapshot()]
        self.moves = []
        self.pending_arc = None
        self.marking_rotations = None

    def dart(self, crossing, port):
        return 4 * self.ids[crossing] + port % 4

    def snapshot(self, link=None):
        if link is None:
            link = self.link
        for crossing in link.crossings:
            if crossing not in self.ids:
                self.ids[crossing] = len(self.ids)
        rows = [None] * len(self.ids)
        for cross in link.crossings:
            rows[self.ids[cross]] = tuple(self.dart(n, p) for n, p in cross.adjacent)
        while rows and rows[-1] is None:
            rows.pop()
        return tuple(rows), link.unlinked_unknot_components

    def record(self, move, post):
        if self.states[-1] == post:
            return
        if post in self.states:
            i = self.states.index(post)
            del self.states[i+1:]
            del self.moves[i:]
        else:
            self.moves.append(move)
            self.states.append(post)

    def run(self):
        reidemeister12 = simplify.reidemeister_I_and_II
        reidemeister3 = simplify.reidemeister_III
        rebuild = Link._rebuild
        rotate = Crossing.rotate
        remove_strand = simplify.remove_strand
        basic = simplify.basic_simplify

        def move12(link, a):
            before = self.snapshot()
            assert before == self.states[-1]
            removed, changed = reidemeister12(link, a)
            post = self.snapshot()
            if len(removed) == 1:
                cross = next(iter(removed))
                i = self.ids[cross]
                row = before[0][i]
                j = next(j for j, other in enumerate(row) if other == 4*i + (j+1)%4)
                self.record(("ri", 4*i+j), post)
            elif len(removed) == 2:
                i = self.ids[a]
                k = self.ids[next(c for c in removed if c is not a)]
                row = before[0][i]
                j = next(j for j, b in enumerate(row)
                         if b//4 == k and (j+b)%2 == 0 and row[(j+1)%4] == 4*k+(b+3)%4)
                self.record(("rii", 4*i+j, row[j]), post)
            else:
                assert post == before
            return removed, changed

        def move3(link, triple):
            assert self.snapshot() == self.states[-1]
            move = ("riii", *(self.dart(c, p) for c, p in triple))
            reidemeister3(link, triple)
            self.record(move, self.snapshot())

        def rebuilt(link, *args, **kwargs):
            if link is not self.link:
                return rebuild(link, *args, **kwargs)
            assert self.snapshot() == self.states[-1]
            self.marking_rotations = {}
            result = rebuild(link, *args, **kwargs)
            image = []
            for c, shift in self.marking_rotations.items():
                assert shift % 2 == 0
                image.extend((self.dart(c, p), self.dart(c, p-shift)) for p in range(4))
            self.marking_rotations = None
            self.record(("relabel", tuple(image)), self.snapshot())
            return result

        def rotated(crossing, shift):
            if self.marking_rotations is not None:
                self.marking_rotations[crossing] = (self.marking_rotations.get(crossing, 0) + shift) % 4
            return rotate(crossing, shift)

        def removed(link, strand):
            assert self.pending_arc is None and self.snapshot() == self.states[-1]
            old = tuple(self.dart(*cs) for cs in strand)
            over = strand[0].is_over_crossing()
            self.pending_arc = (over, old)
            return remove_strand(link, strand)

        def simplified(link, *args, **kwargs):
            if self.pending_arc is not None:
                over, old = self.pending_arc
                before = self.states[-1][0]
                post = self.snapshot()
                assert len(post[0]) == len(before) + 1
                k = len(before)
                before_left = before[old[0]//4][old[0]%4]
                i = next(i for i, a in enumerate(post[0][k]) if a == before_left)
                self.record(("arc", over, old, (4*k+i,)), post)
                self.pending_arc = None
            return basic(link, *args, **kwargs)

        with ExitStack() as patches:
            for owner, name, replacement in [
                (simplify, "reidemeister_I_and_II", move12),
                (simplify, "reidemeister_III", move3),
                (Link, "_rebuild", rebuilt),
                (Crossing, "rotate", rotated),
                (simplify, "remove_strand", removed),
                (simplify, "basic_simplify", simplified),
            ]:
                patches.enter_context(patch.object(owner, name, replacement))
            random.seed(0)
            self.link.simplify("global")
        assert self.snapshot() == self.states[-1]
        return self.link

    def axis_darts(self, verifier):
        component = self.link.link_components[verifier.axis_cusp(self.link)]
        return [self.dart(c, p) for c, p in component]

    def track_anchor(self, starts, verifier):
        entries = self.axis_darts(verifier)
        ends = set(entries + [rotate(x, 2) for x in entries])
        for anchor in starts:
            tracked = anchor
            for m in self.moves:
                kind, *data = m
                if kind == "relabel":
                    tracked = dict(data[0]).get(tracked, tracked)
                elif kind == "arc":
                    _, old, new = data
                    if tracked//4 in {i//4 for i in old+new}:
                        break
                elif kind == "riii":
                    a, b, c = data
                    if tracked//4 in {a//4, b//4, c//4}:
                        border = {
                            rotate(c, 3): a, rotate(c, 2): rotate(b, 1),
                            rotate(a, 3): b, rotate(a, 2): rotate(c, 1),
                            rotate(b, 3): c, rotate(b, 2): rotate(a, 1),
                        }
                        tracked = border.get(tracked, border.get(rotate(tracked, 2)))
                        assert tracked is not None
                elif tracked//4 in {i//4 for i in data}:
                    break
            else:
                if tracked in ends:
                    return anchor, tracked
        raise ValueError("no tracked anchor on the marked circle")

    def find_cut(self, marker, verifier):
        reduced = self.link
        for c in reduced.crossings:
            c.label = self.ids[c]
        pieces = reduced.deconnect_sum()
        trefoil = next(p for p in pieces if len(p.crossings) == 3 and len(p.link_components) == 1)
        partner = next(p for p in pieces if p is not trefoil)
        assert len(pieces) == 2 and verifier.knot_signature(trefoil) == 2
        left_labels = {c.label for c in trefoil.crossings}
        ids_by_label = {c.label: self.ids[c] for c in reduced.crossings}
        assert len(ids_by_label) == len(reduced.crossings)
        def by_label_snapshot(link):
            rows = [None] * len(self.ids)
            for c in link.crossings:
                rows[ids_by_label[c.label]] = tuple(4*ids_by_label[n.label] + p for n, p in c.adjacent)
            while rows and rows[-1] is None:
                rows.pop()
            return tuple(rows), link.unlinked_unknot_components
        target = (by_label_snapshot(trefoil), by_label_snapshot(partner))
        union = dict()
        for rows, _ in target:
            for i, row in enumerate(rows):
                if row is not None:
                    union[i] = row
        boundary = [CrossingStrand(c, p) for c in reduced.crossings if c.label in left_labels
                    for p, (n, _) in enumerate(c.adjacent) if n.label not in left_labels]
        assert len(boundary) == 2
        first, second = boundary
        face_of = {cs: i for i, f in enumerate(reduced.faces()) for cs in f}
        chosen = None
        for a in (first, first.opposite()):
            for b in (second, second.opposite()):
                x, y = a.opposite(), b.opposite()
                if face_of[a] != face_of[x] and face_of[a] == face_of[b] and face_of[x] == face_of[y]:
                    ri = {x:b,b:x,a:y,y:a}
                    if all(union[self.ids[c]][p] == self.dart(*ri.get(CrossingStrand(c,p),c.adjacent[p]))
                           for c in reduced.crossings for p in range(4)):
                        chosen = (self.dart(*a), self.dart(*b))
        assert chosen is not None
        return (*chosen, marker, *target)

def diagram_isomorphism(source, target):
    def adjacency(data):
        return {4*i+j: a for i, row in enumerate(data[0]) if row is not None
                for j, a in enumerate(row)}
    left = adjacency(source)
    right = adjacency(target)
    assert source[1] == target[1] and len(left) == len(right)
    base = min(left)
    for first in right:
        image = {}
        queue = [(base, first)]
        compatible = True
        while queue:
            a, b = queue.pop()
            if a in image:
                if image[a] != b:
                    compatible = False
                    break
                continue
            if a % 2 != b % 2:
                compatible = False
                break
            image[a] = b
            queue.extend([(rotate(a, 1), rotate(b, 1)), (left[a], right[b])])
        if compatible and len(set(image.values())) == len(left):
            return sorted(image.items())
    raise ValueError("no diagram relabeling")

def lean_list(xs):
    return "[" + ", ".join(str(x) for x in xs) + "]"

def lean_diagram(d):
    rows, circles = d
    strings = ["none" if row is None else "some " + lean_list(row) for row in rows]
    return "⟨" + lean_list(strings) + ", " + str(circles) + "⟩"

def lean_move(m):
    match m:
        case ("ri", a): return f".ri {a}"
        case ("rii", a, b): return f".rii {a} {b}"
        case ("riii", a, b, c): return f".riii {a} {b} {c}"
        case ("relabel", pairs):
            return ".relabel " + lean_list(f"({a}, {b})" for a, b in pairs if a != b)
        case ("arc", over, old, new):
            return f".arc {str(over).lower()} {lean_list(old)} {lean_list(new)}"
        case _: raise ValueError(m)

def pd_snapshot(pd):
    by_label = {}
    for i, row in enumerate(pd):
        assert len(row) == 4
        for j, label in enumerate(row):
            by_label.setdefault(label, []).append(4*i+j)
    assert all(len(ends) == 2 for ends in by_label.values())
    reverse = {}
    for a, b in by_label.values():
        reverse[a] = b
        reverse[b] = a
    return tuple(tuple(reverse[4*i+j] for j in range(4)) for i in range(len(pd))), 0

def emit_exterior_diagram_associations(lines, exteriors, templates, marks):
    families = ("even", "odd", "seed")
    matched_names = {
        "partner_to_reference": ("Partner", "Reference"),
        "partner_to_table": ("Partner", "Table"),
        "B_to_C": ("B", "C"),
        "D_to_E": ("D", "E"),
    }
    sources = {}
    for cases in exteriors.values():
        for cert in cases:
            family = families[cert["seed"]]
            endpoints = matched_names[cert["label"]]
            for which, name in zip(("source", "target"), endpoints):
                name = family + name
                data = cert[which + "_diagram"]
                record = (data["pd"], data["crossing_labels"], cert[which + "_axis"])
                assert name not in sources or record == sources[name], name
                sources[name] = record
    lines += ["/-! Raw diagram associations with the exterior replay. -/", ""]
    for name, (pd, labels, cusp) in sources.items():
        raw = pd_snapshot(pd)
        image = diagram_isomorphism(templates[name], raw)
        lines += [
            f"def {name}PlanarCode : List (List ℕ) :=",
            "  " + lean_list(lean_list(row) for row in pd),
            "",
            f"def {name}Raw : Diagram :=",
            "  " + lean_diagram(raw),
            "",
            f"theorem {name}PlanarCodeChecked : Diagram.ofPD {name}PlanarCode = {name}Raw := by decide +kernel",
            "",
            f"def {name}RawRelabel : Move :=",
            "  " + lean_move(("relabel", image)),
            "",
            f"theorem {name}RawChecked :",
            f"    CertifiedMoves {name} [({name}RawRelabel, {name}Raw)] := by decide +kernel",
            "",
        ]
        if cusp is not None:
            mark = dict(image)[marks[name]]
            next_dart = mark
            marked_vertices = []
            while True:
                marked_vertices.append(next_dart//4)
                crossed = rotate(next_dart, 2)
                next_dart = raw[0][crossed//4][crossed%4]
                if next_dart == mark:
                    break
                assert len(marked_vertices) <= len(labels)
            assert set(labels[v] for v in marked_vertices) == {
                "axis-lt", "axis-lb", "axis-rt", "axis-rb"
            } and len(marked_vertices) == 4, name
            lines += [
                f"def {name}RawAxis : Dart := {mark}",
                "",
                f"theorem {name}RawAnchorChecked :",
                f"    Trace.anchor {name} {name}Axis [({name}RawRelabel, {name}Raw)] = some {name}RawAxis := by decide +kernel",
                "",
            ]

def split_module(path, source, has_exteriors):
    """Write the same declarations across modules to bound kernel build memory."""
    pieces = ("Even", "Odd", "Seed")
    footer = "end Trefoil.Section2DiagramData"
    header = "namespace Trefoil.Section2DiagramData\n\nopen Section2DiagramMoves\n\n"
    header += "set_option maxHeartbeats 0\nset_option maxRecDepth 20000\n\n"

    def place(leaf, dependency, description, body):
        module = path.with_name(leaf + ".lean")
        module.write_text(
            f"import {dependency}\n\n/-! {description} -/\n\n"
            + header + body.strip() + "\n\n" + footer + "\n"
        )
        return "Trefoil." + leaf

    finish = source.index(footer)
    cut = source.index("/-! Raw diagram associations") if has_exteriors else finish
    starts = [source.index(f"def {tag.lower()}B : Diagram") for tag in pieces]
    model = source.index("/-- The closure of the three-crossing")
    dependency = place("Section2DiagramModelData", "Trefoil.Section2DiagramMoves",
                       "The standard three-crossing trefoil diagram.", source[model:starts[0]])
    if has_exteriors:
        begins = [source.index(f"def {tag.lower()}PartnerPlanarCode") for tag in pieces]
        extras = [source[a:b].strip() for a, b in zip(begins, begins[1:] + [finish])]
    else:
        extras = [""] * len(pieces)
    imports = []
    for tag, start, end, extra in zip(pieces, starts, starts[1:] + [cut], extras):
        dependency = place("Section2DiagramData" + tag, dependency,
                           f"{tag} endpoint and exterior-source diagram certificates.",
                           source[start:end].strip() + "\n\n" + extra)
        imports.append(f"import {dependency}\n")
    path.write_text("".join(imports) + "\n/-! The concrete Section 2 diagram certificates, by parity and seed. -/\n")


def emit(path, verifier, exteriors=None, split=False):
    lines = [
        "import Trefoil.Section2DiagramMoves",
        "",
        "/-! Explicit endpoint move certificates exported from the Section 2 replay. -/",
        "",
        "namespace Trefoil.Section2DiagramData",
        "",
        "open Section2DiagramMoves",
        "",
        "set_option maxHeartbeats 0",
        "set_option maxRecDepth 20000",
        "",
    ]
    templates, marks = {}, {}
    standard = Recorder(Link(braid_closure=[-1, -1, -1])).snapshot()
    lines += [
        "/-- The closure of the three-crossing two-strand braid with",
        "Spherogram generator −1, in the manuscript's trefoil chirality. -/",
        "def trefoilModel : Diagram := " + lean_diagram(standard),
        "",
    ]
    for b, aug, case in [(0,True,"even"),(1,True,"odd"),(2,False,"seed")]:
        for label, diagram in (
            *((c, verifier.stage(i,b,switch,aug)) for c,i,switch in
                [("B",0,True),("C",1,False),("D",1,True),("E",2,False)]),
            ("Reference", verifier.reference(b,aug))
        ):
            rec = Recorder(diagram)
            name = case + label
            templates[name] = rec.snapshot()
            lines += [f"def {name} : Diagram :=", "  " + lean_diagram(templates[name]), ""]
            if aug:
                marks[name] = rec.axis_darts(verifier)[0]
                lines += [f"def {name}Axis : Dart := {marks[name]}", ""]
        for initial, name, index, switch in [(True,"start",0,False),(False,"end",2,True)]:
            identifier = case + name.capitalize()
            probe = verifier.stage(index,b,switch,aug)
            rec = Recorder(probe)
            original_axis = rec.axis_darts(verifier) if aug else []
            endpoint = rec.run()
            assert len(rec.moves) + 1 == len(rec.states)
            print(identifier, len(rec.moves), len(endpoint.crossings))
            lines += [
                f"def {identifier} : Diagram :=",
                "  " + lean_diagram(rec.states[0]),
                "",
                f"def {identifier}Trace : Trace := [",
            ]
            lines += [
                f"  ({lean_move(m)}, {lean_diagram(d)})" + ("," if i+1 < len(rec.moves) else "]")
                for i, (m, d) in enumerate(zip(rec.moves, rec.states[1:]))
            ]
            lines += ["", f"theorem {identifier}Checked : CertifiedMoves {identifier} {identifier}Trace := by decide +kernel",
                      ""]
            if initial:
                if aug:
                    anchor, marker = rec.track_anchor(original_axis, verifier)
                    lines += [
                        f"def {case}AAxis : Dart := {anchor}",
                        f"def {case}PartnerAxis : Dart := {marker}",
                        "",
                        f"theorem {case}AnchorChecked :",
                        f"    Trace.anchor {identifier} {case}AAxis {identifier}Trace = some {case}PartnerAxis := by decide +kernel",
                        "",
                    ]
                else:
                    marker = None
                a,cut_b,marker,left,right = rec.find_cut(marker,verifier)
                templates[case + "Partner"] = right
                marks[case + "Partner"] = marker
                mark_lean = f"(some {case}PartnerAxis)" if marker is not None else "none"
                lines += [
                    f"def {case}Trefoil : Diagram :=",
                    "  " + lean_diagram(left),
                    "",
                    f"def {case}TrefoilRelabel : Move :=",
                    "  " + lean_move(("relabel", diagram_isomorphism(left, standard))),
                    "",
                    f"theorem {case}TrefoilChecked :",
                    f"    CertifiedMoves {case}Trefoil [({case}TrefoilRelabel, trefoilModel)] := by decide +kernel",
                    "",
                    f"def {case}Partner : Diagram :=",
                    "  " + lean_diagram(right),
                    "",
                    f"def {case}CutA : Dart := {a}",
                    f"def {case}CutB : Dart := {cut_b}",
                    "",
                    f"theorem {case}SplitChecked :",
                    f"    (Trace.endpoint {identifier} {identifier}Trace).checkSplit {case}CutA {case}CutB {mark_lean}",
                    f"      {case}Trefoil {case}Partner = true := by decide +kernel",
                    "",
                ]
            else:
                if aug:
                    lines += [f"def {case}FAxis : Dart := {original_axis[0]}", ""]
                assert not endpoint.crossings and endpoint.unlinked_unknot_components == (2 if aug else 1)
                lines += [
                    f"theorem {identifier}Unlink : Trace.endpoint {identifier} {identifier}Trace = ⟨[], {2 if aug else 1}⟩ := rfl",
                    "",
                ]
        lines += [
            f"abbrev {case}A : Diagram := {case}Start",
            f"abbrev {case}F : Diagram := {case}End",
            "",
        ]
    templates["seedTable"] = Recorder(Link("K14a7385")).snapshot()
    lines += [
        "/-- The diagram returned by the pinned table entry K14a7385. -/",
        "def seedTable : Diagram := " + lean_diagram(templates["seedTable"]),
        "",
    ]
    if exteriors is not None:
        emit_exterior_diagram_associations(lines, exteriors, templates, marks)
    lines += ["end Trefoil.Section2DiagramData", ""]
    source = "\n".join(lines)
    if split:
        split_module(path, source, exteriors is not None)
    else:
        path.write_text(source)

if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("verifier", type=Path)
    parser.add_argument("output", type=Path)
    parser.add_argument("--exteriors", type=Path)
    parser.add_argument("--split", action="store_true", help="write the parity modules and their import module")
    args = parser.parse_args()
    exteriors = json.loads(args.exteriors.read_text()) if args.exteriors else None
    emit(args.output, load_verifier(args.verifier), exteriors, args.split)
