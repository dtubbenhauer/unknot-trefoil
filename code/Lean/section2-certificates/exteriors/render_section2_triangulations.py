#!/usr/bin/env python3
"""Render the checked-in finite triangulation data as Lean literals."""
from argparse import ArgumentParser
from itertools import chain
from pathlib import Path
import json

MATCHES = {
    "partner_to_reference": "partnerReference",
    "B_to_C": "firstIntermediate",
    "D_to_E": "secondIntermediate",
    "partner_to_table": "partnerTable",
}


HEADER = """import Trefoil.Section2Triangulations

/-!
# The finite exterior witnesses for Section 2

The six rows are the three marked exterior maps for each of the two
parities. The additional rows give the filled first example. Generated
from the fixed JSON snapshot by `render_section2_triangulations.py`.

The tetrahedron and peripheral equations are checked by Lean, using
explicit signed coefficients of dual cusp two-cells. The source diagrams,
decorated triangulation signatures and the Python exporter record the
provenance of the arrays. The theorem realizing the marked exteriors of
those diagrams is a separate topological input.
-/

namespace Trefoil.Section2TriangulationData

open Trefoil.Section2Triangulations

set_option maxRecDepth 100000
set_option maxHeartbeats 0

inductive Match
  | partnerReference
  | firstIntermediate
  | secondIntermediate
  deriving DecidableEq

def Match.reverses : Match → Bool
  | .partnerReference | .secondIntermediate => true
  | .firstIntermediate => false

structure Certificate where
  source : Triangulation
  target : Triangulation
  tetMap : Array TetImage
  sourceMarking : CuspMarking
  targetMarking : CuspMarking
  peripheral : PeripheralWitness
  sourceAxis : Nat
  targetAxis : Nat
  reverse : Bool

structure Checked (c : Certificate) : Prop where
  sourceValid : checkTriangulation c.source = true
  targetValid : checkTriangulation c.target = true
  faces : checkIso c.source c.target c.tetMap c.reverse = true
  sourceCurves : checkCuspMarking c.source c.sourceMarking = true
  targetCurves : checkCuspMarking c.target c.targetMarking = true
  peripheralMaps : checkPeripheral c.source c.target c.tetMap
    c.sourceMarking c.targetMarking c.peripheral = true

def hasMarkedSlope (c : Certificate) : Prop :=
  c.sourceAxis < c.sourceMarking.cuspCount ∧
  c.targetAxis < c.targetMarking.cuspCount ∧
  (peripheralImage c.peripheral c.sourceAxis).cusp = c.targetAxis ∧
  ∀ i : Fin c.sourceMarking.cuspCount,
    let m := peripheralImage c.peripheral i
    (m.mm = 1 ∨ m.mm = -1) ∧ m.ml = 0 ∧ m.lm = 0 ∧
      m.ll = if c.reverse then -m.mm else m.mm

instance (c : Certificate) : Decidable (hasMarkedSlope c) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- The axis matrix preserves the prescribed slope up to the sign of its
meridian coefficient, which does not change an unoriented primitive slope. -/
theorem markedSlope_image {c : Certificate} (h : hasMarkedSlope c) (t : Int) :
    let m := peripheralImage c.peripheral c.sourceAxis
    (m.mm * 1 + m.ml * t, m.lm * 1 + m.ll * t) =
      (m.mm, m.mm * (if c.reverse then -t else t)) := by
  have hm := h.2.2.2 ⟨c.sourceAxis, h.1⟩
  dsimp only at hm ⊢
  rcases hm with ⟨_, hml, hlm, hll⟩
  cases hd : c.reverse <;> simp [hml, hlm, hll, hd, Int.neg_mul, Int.mul_neg]

noncomputable def Checked.markedIso {c : Certificate} (h : Checked c) :
    MarkedIsomorphism c.source c.target c.tetMap c.reverse
      c.sourceMarking c.targetMarking c.peripheral :=
  checkMarkedIso_sound h.sourceValid h.targetValid h.faces
    h.sourceCurves h.targetCurves h.peripheralMaps
"""


def fmt_array(values):
    return "#[" + ", ".join(map(str, values)) + "]"


def flat(rows):
    return list(chain.from_iterable(rows))


def integer_rows_literal(values, indent=4):
    return "#[\n" + ",\n".join(
        " " * indent + ", ".join(map(str, values[i:i+20]))
        for i in range(0, len(values), 20)
    ) + "]"


def signed_table(values):
    digits = [2 * value if value >= 0 else -2 * value - 1 for value in values]
    width = max(1, max(digits, default=0).bit_length())
    word = sum(digit << (width * i) for i, digit in enumerate(digits))
    return f"SignedTable.packed {len(values)} {width} {word}"


def tet_image(image):
    number, permutation = image
    return f"⟨{number}, {fmt_array(permutation)}⟩"


def triang_literal(faces):
    return "#[\n" + ",\n".join(
        "    #[" + ", ".join(map(tet_image, row)) + "]" for row in faces
    ) + "]"


def map_literal(maps):
    return "#[\n" + ",\n".join(
        "    " + ", ".join(map(tet_image, maps[i:i+4])) for i in range(0, len(maps), 4)
    ) + "]"


def marking_literal(triangulation):
    indices = flat(triangulation["cusp_indices"])
    mu, lon = [flat(flat(rows)) for rows in triangulation["curves"]]
    return f"""⟨{max(indices)+1},
    {integer_rows_literal(indices)},
    {signed_table(mu)},
    {signed_table(lon)}⟩"""


def peripheral_literal(m):
    maps = []
    for cusp_index, matrix in zip(m["cusp_images"], m["cusp_maps"]):
        maps.append("⟨" + ", ".join(map(str, [cusp_index, *flat(matrix)])) + "⟩")
    mu, lon = [flat(flat(rows)) for rows in m["potential"]]
    return f"""⟨{fmt_array(maps)},
    {signed_table(mu)},
    {signed_table(lon)}⟩"""


def render_certificate(m):
    label = MATCHES[m["label"]]
    name = f"{label}{m['seed']}"
    source = m["source"]
    target = m["target"]
    reverse = str(m["sign"] == -1).lower()
    axis_src = 0 if m["source_axis"] is None else m["source_axis"]
    axis_dest = 0 if m["target_axis"] is None else m["target_axis"]
    return f"""
/-- {m['label']} for {'parity' if m['seed'] < 2 else 'the filled example at'} {m['seed']}. -/
def {name} : Certificate where
  source := {triang_literal(source['faces'])}
  target := {triang_literal(target['faces'])}
  tetMap := {map_literal(m['tet_map'])}
  sourceMarking := {marking_literal(source)}
  targetMarking := {marking_literal(target)}
  peripheral := {peripheral_literal(m)}
  sourceAxis := {axis_src}
  targetAxis := {axis_dest}
  reverse := {reverse}

theorem {name}_checked : Checked {name} where
  sourceValid := by decide +kernel
  targetValid := by decide +kernel
  faces := by decide +kernel
  sourceCurves := by decide +kernel
  targetCurves := by decide +kernel
  peripheralMaps := by decide +kernel

theorem {name}_slopes : hasMarkedSlope {name} := by decide +kernel
"""


FOOTER = """
/-- The three diagrams to compare, for either parity of the twist parameter. -/
def data (b : Fin 2) (k : Match) : Certificate :=
  if (b : Nat) = 0 then
    match k with
    | .partnerReference => partnerReference0
    | .firstIntermediate => firstIntermediate0
    | .secondIntermediate => secondIntermediate0
  else
    match k with
    | .partnerReference => partnerReference1
    | .firstIntermediate => firstIntermediate1
    | .secondIntermediate => secondIntermediate1

theorem data_reverses (b : Fin 2) (k : Match) :
    (data b k).reverse = k.reverses := by
  unfold data
  split <;> cases k <;> rfl

theorem data_checked (b : Fin 2) (k : Match) : Checked (data b k) := by
  unfold data
  split <;> cases k
  · exact partnerReference0_checked
  · exact firstIntermediate0_checked
  · exact secondIntermediate0_checked
  · exact partnerReference1_checked
  · exact firstIntermediate1_checked
  · exact secondIntermediate1_checked

theorem data_slopes (b : Fin 2) (k : Match) : hasMarkedSlope (data b k) := by
  unfold data
  split <;> cases k
  · exact partnerReference0_slopes
  · exact firstIntermediate0_slopes
  · exact secondIntermediate0_slopes
  · exact partnerReference1_slopes
  · exact firstIntermediate1_slopes
  · exact secondIntermediate1_slopes

noncomputable def markedIso (b : Fin 2) (m : Match) :
    let c := data b m
    MarkedIsomorphism c.source c.target c.tetMap c.reverse
      c.sourceMarking c.targetMarking c.peripheral :=
  (data_checked b m).markedIso

end Trefoil.Section2TriangulationData
"""


def main():
    p = ArgumentParser(description=__doc__)
    p.add_argument('json_path', type=Path)
    p.add_argument('lean_path', type=Path)
    p.add_argument('--named', action='store_true',
                   help='include the optionally recorded maps of the first filled example')
    args = p.parse_args()
    data = json.loads(args.json_path.read_text())
    cases = data['parity_matches']
    if args.named:
        cases += data['named_matches']
    folder = args.lean_path.with_suffix('')
    folder.mkdir(exist_ok=True)
    module = 'Trefoil.Section2TriangulationData'
    namespace = 'Trefoil.Section2TriangulationData'
    def write_if_changed(path, source):
        if not path.exists() or path.read_text() != source:
            path.write_text(source)

    write_if_changed(folder / 'Base.lean', HEADER + f"\nend {namespace}\n")
    shards = {}
    for case in cases:
        kind = MATCHES[case['label']]
        parity = ('Even', 'Odd', 'Named')[case['seed']]
        shards[parity + kind[:1].upper() + kind[1:]] = case

    # Independent witness checks. Keep two chains so fresh Lake builds
    # limit kernel memory by checking at most two of these at a time.
    chains = (
        ('EvenFirstIntermediate', 'NamedSecondIntermediate', 'EvenPartnerReference',
         'OddSecondIntermediate', 'NamedPartnerReference'),
        ('EvenSecondIntermediate', 'OddFirstIntermediate', 'OddPartnerReference',
         'NamedFirstIntermediate', 'NamedPartnerTable'),
    )
    imports = [f"import {module}.Base"]
    for chain_names in chains:
        predecessor = 'Base'
        for shard in chain_names:
            if shard not in shards:
                continue
            case = shards[shard]
            write_if_changed(folder / f'{shard}.lean', f"""import {module}.{predecessor}

namespace {namespace}

open Trefoil.Section2Triangulations

set_option maxRecDepth 100000
set_option maxHeartbeats 0
""" + render_certificate(case) + f"\nend {namespace}\n")
            predecessor = shard
        imports.append(f"import {module}.{predecessor}")
    write_if_changed(args.lean_path, '\n'.join(imports) + f"""
/-! The checked exterior data from the two parity cases and filled first example. -/

namespace {namespace}

open Trefoil.Section2Triangulations
""" + FOOTER)


if __name__ == '__main__':
    main()
