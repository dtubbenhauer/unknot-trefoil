#!/usr/bin/env python3
"""Build and audit the trefoil formalization against its exact pins.

Python orchestrates builds and records provenance. Lean's kernel checks the
proofs. The reports include the expanded reference interfaces for Sections
2, 3A and 3B, and the combined Section 3 endpoint.
"""
import argparse
import datetime
import hashlib
import json
from pathlib import Path
import re
import subprocess
import tempfile
import tomllib

ROOT = Path(__file__).resolve().parents[1]
REPORTS = ROOT / "reports"
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
FORBIDDEN = re.compile(
    r"\b(sorry|sorryAx|admit|axiom|constant|native_decide|ofReduceBool|ofReduceNat|"
    r"unsafe|implemented_by)\b|debug\.skipKernelTC"
)
TOOLCHAIN_PIN = "leanprover/lean4:v4.22.0-rc2"
LEAN_COMMIT = "6a60de2ac701d1a3f5dc88894b7822f17c3a980b"
MATHLIB_PIN = "49af9b7fd7e19db08a946b5bd08d1a5bc39dfd3d"
AUDIT_RUNNER = "SECTION3A_Project_Audit"
SECTION2_AUDIT = "SECTION2_Reference_Audit"
REFERENCE_AUDIT = "SECTION3A_Reference_Audit"
SECTION3B_AUDIT = "SECTION3B_Reference_Audit"
EXPERIMENTAL_MODULES = {
    "experimental.Section3ARelativeMVStandalone",
    "experimental.Section3ACanonicalTopology",
    "experimental.Section3AExplicitHomology",
}
SECTION2_ENDPOINTS = {
    "Trefoil.Section2Topology.partner_upper_bound",
    "Trefoil.Section2Certificate.family_upper_bound",
    "Trefoil.Section2Certificate.seed_movie",
    "Trefoil.Section2Certificate.seed_partner_is_table",
}
SECTION3A_ENDPOINTS = {
    "Trefoil.Section3ATopology.section3A_lower_bound",
    "Trefoil.Section3ATopology.section3A_oriented_lower_bound",
}
SECTION3B_ENDPOINTS = {
    "Trefoil.Section3BMinimum.surgeryMatrixZ_det",
    "Trefoil.Section3BMinimum.quadraticBound_translate_even",
    "Trefoil.Section3BMinimum.minimum_to_comparison",
    "Trefoil.Section3BMinimum.no_owens_minimum_245",
    "Trefoil.Section3BTopology.raw_spin_245",
    "Trefoil.Section3BTopology.oriented_correction_245",
    "Trefoil.Section3BTopology.section3B_oriented_lower_bound",
    "Trefoil.Section3BTopology.section3B_lower_bound",
    "Trefoil.Section3LowerBound.section3_lower_bound",
}
REQUIRED_MODULES = {
    "Trefoil.Arithmetic", "Trefoil.LatticeBasics", "Trefoil.LatticeArithmetic",
    "Trefoil.LatticePath",
    "Trefoil.LatticeSupports",
    "Trefoil.LatticeSigns", "Trefoil.LatticeEmbedding", "Trefoil.LatticeBlocks",
    "Trefoil.LatticeCoordinates", "Trefoil.LatticeShapes", "Trefoil.LatticeIsometry",
    "Trefoil.LatticeParity", "Trefoil.LatticeFrameParity", "Trefoil.LatticeExtraction",
    "Trefoil.LatticeOddBasis",
    "Trefoil.FiniteForms", "Trefoil.FiniteCorrectionTerms", "Trefoil.FiniteObstruction",
    "Trefoil.Consequences",
    "Trefoil.Section3ACoefficients", "Trefoil.Section3APlumbing",
    "Trefoil.Section3ASignature", "Trefoil.Section3ATopology",
    "Trefoil.Section3BMinimum", "Trefoil.Section3BTopology",
    "Trefoil.Section3LowerBound",
    "Trefoil.Section2Arithmetic", "Trefoil.Section2Certificate",
    "Trefoil.Section2DiagramData", "Trefoil.Section2DiagramMoves",
    "Trefoil.Section2DiagramDomainData", "Trefoil.Section2DiagramDomains",
    "Trefoil.Section2InitialExterior",
    "Trefoil.Section2Pachner", "Trefoil.Section2ReferenceTangle",
    "Trefoil.Section2SwitchData", "Trefoil.Section2Switches",
    "Trefoil.Section2Topology", "Trefoil.Section2TriangulationData",
    "Trefoil.Section2Triangulations",
}
REQUIRED_ENDPOINTS = {
    "Trefoil.LatticeOddBasis.selected_columns_independent_mod_two",
    "Trefoil.LatticeOddBasis.of_odd_basis",
    "Trefoil.LatticeOddBasis.no_odd_basis_embedding",
    "Trefoil.LatticeSigns.signed_chain",
    "Trefoil.LatticeBlocks.exists_frame",
    "Trefoil.LatticeShapes.extract_rowA",
    "Trefoil.LatticeShapes.extract_rowB",
    "Trefoil.LatticeShapes.extract_rowC",
    "Trefoil.LatticeParity.mem_blockRootSpan_iff",
    "Trefoil.LatticeFrameParity.frame_B_not_mem",
    "Trefoil.LatticeExtraction.configuration_of_frame",
    "Trefoil.LatticeExtraction.no_embedding",

    "Trefoil.Arithmetic.partner_fraction", "Trefoil.Arithmetic.three_changes_infinity",
    "Trefoil.Arithmetic.plumbing_pair", "Trefoil.Arithmetic.even_pivot_signature",
    "Trefoil.Arithmetic.odd_pivot_signature", "Trefoil.LatticeBasics.norm_two_support_card",
    "Trefoil.LatticeBasics.odd_det_columns_independent_mod_two",
    "Trefoil.LatticePath.supports_form_path",
    "Trefoil.LatticeSupports.norm_two_chain_support_path",
    "Trefoil.LatticeSupports.dot_zero_iff_disjoint",
    "Trefoil.no_lattice_configuration", "Trefoil.Finite.candidates_complete",
    "Trefoil.Finite.scaled_correction_spec", "Trefoil.Finite.single_vector_obstructions",
    "Trefoil.Finite.doubling_obstruction", "Trefoil.Finite.no_reduced_correction_comparison",
    "Trefoil.Consequences.lower_bound_245", "Trefoil.Consequences.lower_bound_lattice",
    "Trefoil.Consequences.strict_saving", "Trefoil.Consequences.plumbing_saving",
    "Trefoil.Consequences.family_injective",
}
REQUIRED_MODEL_GUARDS = {
    "embeddingInputs", "oddBasisObstructionInputs", "latticeConfigurationInputs", "reducedFormDefinition", "surgeryMatrixDefinition",
    "quadraticBoundDefinition", "correctionComparisonDefinition", "correctionRecurrence",
}


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def code_only(source):
    """Ignore nested comments and string literals in the source-policy scan."""
    out = []
    i = depth = 0
    while i < len(source):
        if depth:
            if source.startswith("/-", i):
                depth += 1
                i += 2
            elif source.startswith("-/", i):
                depth -= 1
                i += 2
            else:
                i += 1
        elif source.startswith("/-", i):
            out.append(" ")
            depth = 1
            i += 2
        elif source.startswith("--", i):
            end = source.find("\n", i)
            i = len(source) if end < 0 else end
        elif source[i] == '"':
            i += 1
            while i < len(source):
                if source[i] == "\\":
                    i += 2
                elif source[i] == '"':
                    i += 1
                    break
                else:
                    i += 1
            out.append(" ")
        else:
            out.append(source[i])
            i += 1
    if depth:
        raise RuntimeError("Unclosed Lean comment")
    return "".join(out)


def source_check(source):
    bad = FORBIDDEN.search(code_only(source))
    if bad:
        raise RuntimeError("Forbidden proof escape: " + bad.group())


def parse_axioms(text, expected=None):
    rows = {}
    pattern = r"'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)"
    for name, body in re.findall(pattern, text):
        axioms = {x.strip() for x in body.split(",") if x.strip()}
        unexpected = axioms - ALLOWED_AXIOMS
        if unexpected:
            raise RuntimeError(f"Unexpected axioms for {name}: {sorted(unexpected)}")
        if name in rows:
            raise RuntimeError(f"Duplicate axiom report: {name}")
        rows[name] = sorted(axioms)
    if expected is not None and set(rows) != set(expected):
        raise RuntimeError(f"Axiom audit coverage mismatch: {set(rows) ^ set(expected)}")
    return rows


def run(args, log, *, expect_success=True):
    proc = subprocess.run(args, cwd=ROOT, text=True, stdout=subprocess.PIPE,
                          stderr=subprocess.STDOUT)
    (REPORTS / log).write_text(proc.stdout)
    if expect_success and proc.returncode:
        print(proc.stdout)
        raise RuntimeError(f"Failed command {args}; see reports/{log}")
    return proc


def verify_toolchain():
    if (ROOT / "lean-toolchain").read_text().strip() != TOOLCHAIN_PIN:
        raise RuntimeError("Lean toolchain pin changed")
    lean = run(["lean", "--version"], "lean-version.txt").stdout
    if "version 4.22.0-rc2," not in lean or f"commit {LEAN_COMMIT}," not in lean:
        raise RuntimeError(f"Wrong Lean executable: {lean.strip()}")
    lake = run(["lake", "--version"], "lake-version.txt").stdout
    if "(Lean version 4.22.0-rc2)" not in lake:
        raise RuntimeError(f"Wrong Lake executable: {lake.strip()}")
    return {"lean": lean.strip(), "lake": lake.strip()}


def verify_dependencies():
    manifest = json.loads((ROOT / "lake-manifest.json").read_text())
    packages = manifest["packages"]
    if {p["name"]: p["rev"] for p in packages}.get("mathlib") != MATHLIB_PIN:
        raise RuntimeError("Mathlib dependency pin changed")
    revisions = {}
    for package in packages:
        checkout = ROOT / manifest["packagesDir"] / package["name"]
        revision = subprocess.check_output(
            ["git", "-C", checkout, "rev-parse", "HEAD"], text=True
        ).strip()
        if revision != package["rev"]:
            raise RuntimeError(f"Wrong revision for {package['name']}: {revision}")
        modified = subprocess.check_output(
            ["git", "-C", checkout, "status", "--porcelain", "--untracked-files=no"],
            text=True,
        )
        if modified:
            raise RuntimeError(f"Tracked dependency sources modified in {package['name']}")
        revisions[package["name"]] = revision
    (REPORTS / "dependency-revisions.txt").write_text(
        "".join(f"{name} {revision}\n" for name, revision in sorted(revisions.items()))
    )
    return revisions


def project_sources():
    return sorted([
        *ROOT.glob("*.lean"), *(ROOT / "Trefoil").rglob("*.lean"),
        *(ROOT / "experimental").rglob("*.lean"),
    ])


def module_name(path):
    return ".".join(path.relative_to(ROOT).with_suffix("").parts)


def check_project_audit(text, expected_modules):
    actual_modules = set(re.findall(r"(?m)^(?:.*: info: )?MODULE (\S+)$", text))
    if actual_modules != expected_modules:
        raise RuntimeError(f"Project audit coverage mismatch: {actual_modules ^ expected_modules}")
    declarations = {}
    theorem_pattern = r"(?m)^(?:.*: info: )?THEOREM (\S+)::(\S+)\nAXIOMS \[([^\]]*)\]\nTYPE "
    for module, name, body in re.findall(theorem_pattern, text):
        if module not in expected_modules:
            raise RuntimeError(f"Unknown declaration owner: {module}")
        if name in declarations:
            raise RuntimeError(f"Duplicate project theorem report: {name}")
        axioms = {x.strip() for x in body.split(",") if x.strip()}
        if axioms - ALLOWED_AXIOMS:
            raise RuntimeError(f"Unexpected axioms for {name}: {sorted(axioms - ALLOWED_AXIOMS)}")
        declarations[name] = {"module": module, "axioms": sorted(axioms)}
    theorem_count = re.findall(r"(?m)^(?:.*: info: )?THEOREM-COUNT (\d+)$", text)
    if theorem_count != [str(len(declarations))]:
        raise RuntimeError("Incomplete project theorem audit")
    missing = (SECTION2_ENDPOINTS | SECTION3A_ENDPOINTS | SECTION3B_ENDPOINTS) - declarations.keys()
    if missing:
        raise RuntimeError(f"Endpoint theorems missing from project audit: {sorted(missing)}")
    return declarations


def run_reference_audit(module, log, required):
    source = (ROOT / f"{module}.lean").read_text()
    expected = re.findall(r"^#print axioms (\S+)$", source, re.M)
    missing = required - set(expected)
    if missing:
        raise RuntimeError(f"Required endpoints missing from {module}: {sorted(missing)}")
    out = run(["lake", "env", "lean", "-j", "1", f"{module}.lean"], log)
    return parse_axioms(out.stdout, expected)


def audit_section3b():
    axioms = run_reference_audit(
        SECTION3B_AUDIT, "section3b-reference-axioms.txt", SECTION3B_ENDPOINTS,
    )
    run(["python3", "tools/check_section3b_bridge.py"], "section3b-numerical-checks.txt")
    return axioms


def build_triangulation_shards():
    # The kernel computations for these independent witnesses use substantial
    # memory. Check one witness at a time before the default Lake build.
    source_dir = ROOT / "Trefoil" / "Section2TriangulationData"
    shards = sorted(path for path in source_dir.glob("*.lean") if path.stem != "Base")
    if not shards:
        raise RuntimeError("No Section 2 triangulation certificate modules found")
    (REPORTS / "section2-shards").mkdir(exist_ok=True)
    print(f"Building the {len(shards)} Section 2 triangulation certificates sequentially.", flush=True)
    for path in shards:
        run(["lake", "build", module_name(path)], f"section2-shards/{path.stem}.txt")
    return [module_name(path) for path in shards]


def negative_controls():
    """Ensure the axiom checker and exact-interface guard fail when they should."""
    source_check("/- sorry /- axiom -/ native_decide -/\ndef good : Nat := 0")
    try:
        source_check("theorem bad : False := by sorry")
    except RuntimeError:
        pass
    else:
        raise RuntimeError("Source policy accepted a missing proof")
    with tempfile.TemporaryDirectory(prefix="trefoil-audit-") as tmp:
        path = Path(tmp) / "Unexpected.lean"
        path.write_text("axiom auditUnexpected : False\n"
                        "theorem auditBad : False := auditUnexpected\n"
                        "#print axioms auditBad\n")
        out = run(["lake", "env", "lean", "-j", "1", str(path)], "negative-unexpected-axiom.txt")
        try:
            parse_axioms(out.stdout, ["auditBad"])
        except RuntimeError:
            pass
        else:
            raise RuntimeError("Axiom checker accepted an injected axiom")
        path = Path(tmp) / "ExtraPremise.lean"
        path.write_text("import Trefoil\n"
            "def changedEndpoint (extra : False) {h a s : ℤ} "
            "(_hf : Trefoil.Finite.ReducedForm h a s) : "
            "¬ Trefoil.Finite.HasCorrectionComparison h a s := False.elim extra\n"
            "example : ∀ {h a s : ℤ}, Trefoil.Finite.ReducedForm h a s → "
            "¬ Trefoil.Finite.HasCorrectionComparison h a s := @changedEndpoint\n")
        out = run(["lake", "env", "lean", "-j", "1", str(path)], "negative-extra-premise.txt",
                  expect_success=False)
        if out.returncode == 0 or "type mismatch" not in out.stdout.lower():
            raise RuntimeError("Interface control did not reject the extra premise as expected")
    return {"missing_proof_rejected": True, "unexpected_axiom_rejected": True,
            "extra_endpoint_premise_rejected": True}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--get-cache", action="store_true",
                        help="download the pinned Mathlib cache before building")
    parser.add_argument("--clean", action="store_true",
                        help="rebuild all project modules without deleting dependency caches")
    parser.add_argument("--section3b-only", action="store_true",
                        help="verify Section 3B and the combined lower bound with their dependencies")
    opts = parser.parse_args()
    REPORTS.mkdir(exist_ok=True)
    result_path = REPORTS / (
        "section3b-verification.json" if opts.section3b_only else "verification.json"
    )
    result_path.unlink(missing_ok=True)
    sources = project_sources()
    pins = [ROOT / name for name in ("lean-toolchain", "lake-manifest.json", "lakefile.toml")]
    before = {str(p.relative_to(ROOT)): sha(p) for p in [*sources, *pins]}
    for path in sources:
        source_check(path.read_text())
    present = {module_name(p) for p in sources}
    expected_core_modules = {name for name in present if name.startswith("Trefoil.")}
    if not REQUIRED_MODULES <= expected_core_modules:
        raise RuntimeError(
            f"Required mathematical modules removed: {REQUIRED_MODULES - expected_core_modules}"
        )
    required_audits = {SECTION2_AUDIT, REFERENCE_AUDIT, SECTION3B_AUDIT, AUDIT_RUNNER}
    if not (EXPERIMENTAL_MODULES | required_audits) <= present:
        raise RuntimeError("Missing experimental module or proof audit")
    audit = (ROOT / "TrefoilAudit.lean").read_text()
    guard_names = set(re.findall(r"^(?:def|theorem) (\w+)", code_only(audit), re.M))
    if not REQUIRED_MODEL_GUARDS <= guard_names:
        raise RuntimeError(f"Model/interface guards removed: {REQUIRED_MODEL_GUARDS - guard_names}")
    expected_axioms = re.findall(r"^#print axioms (\S+)$", audit, re.M)
    if not REQUIRED_ENDPOINTS <= set(expected_axioms):
        raise RuntimeError(f"Required endpoint audits removed: {REQUIRED_ENDPOINTS - set(expected_axioms)}")
    if len(expected_axioms) != len(set(expected_axioms)):
        raise RuntimeError("Duplicate requested axiom checks")
    lakefile = tomllib.loads((ROOT / "lakefile.toml").read_text())
    if set(lakefile["defaultTargets"]) != {
        "Trefoil", "TrefoilAudit", "Section2Reference", "Section3AReference", "Section3BReference",
    }:
        raise RuntimeError("Default build must include core, experimental and audit targets")
    experimental_roots = next(
        lib["roots"] for lib in lakefile["lean_lib"] if lib["name"] == "Section3AReference"
    )
    if set(experimental_roots) != EXPERIMENTAL_MODULES | {REFERENCE_AUDIT}:
        raise RuntimeError("Default build must compile every original experimental module")
    section3b_roots = next(
        lib["roots"] for lib in lakefile["lean_lib"] if lib["name"] == "Section3BReference"
    )
    if set(section3b_roots) != {SECTION3B_AUDIT}:
        raise RuntimeError("Default build must compile the Section 3B reference audit")

    versions = verify_toolchain()
    if opts.get_cache:
        run(["lake", "exe", "cache", "get"], "mathlib-cache.txt")
    if opts.clean:
        run(["lake", "clean", lakefile["name"]], "lake-clean.txt")
    if opts.section3b_only:
        print("Building and auditing Section 3B and the combined lower bound.", flush=True)
        run(["lake", "build", "Section3BReference"], "section3b-lake-build.txt")
        revisions = verify_dependencies()
        section3b_axioms = audit_section3b()
        after = {str(p.relative_to(ROOT)): sha(p) for p in [*project_sources(), *pins]}
        if before != after:
            raise RuntimeError("Lean sources or pins changed during verification; rerun on a fixed snapshot")
        result = {
            "success": True,
            "scope": "Section 3B and the combined Section 3 lower bound",
            "checked_at_utc": datetime.datetime.now(datetime.timezone.utc).isoformat(),
            "clean_project_build": opts.clean,
            "tool_versions": versions,
            "dependency_revisions": revisions,
            "section3b_reference_axioms": section3b_axioms,
            "source_and_pin_sha256": before,
        }
        result_path.write_text(json.dumps(result, indent=2) + "\n")
        print(f"Checked {len(section3b_axioms)} axiom reports and the independent arithmetic.")
        return
    triangulation_shards = build_triangulation_shards()
    print("Building the Section 2 diagram domain certificates.", flush=True)
    run(["lake", "build", "Trefoil.Section2DiagramDomainData"], "section2-domain-data.txt")
    print("Building Sections 2 and 3, including all experimental modules and the audits.", flush=True)
    run(["lake", "build"], "lake-build.txt")
    revisions = verify_dependencies()
    out = run(["lake", "env", "lean", "-j", "1", "TrefoilAudit.lean"], "axioms-and-interfaces.txt")
    axioms = parse_axioms(out.stdout, expected_axioms)
    section2_axioms = run_reference_audit(
        SECTION2_AUDIT, "section2-reference-axioms.txt", SECTION2_ENDPOINTS,
    )
    section3a_axioms = run_reference_audit(
        REFERENCE_AUDIT, "section3a-reference-axioms.txt", SECTION3A_ENDPOINTS,
    )
    section3b_axioms = audit_section3b()
    print("Auditing theorem statements and transitive axioms from Lean's environment.", flush=True)
    project = run(
        ["lake", "env", "lean", "-j", "1", f"{AUDIT_RUNNER}.lean"],
        "project-theorems-and-axioms.txt",
    )
    all_declarations = check_project_audit(project.stdout, present - {AUDIT_RUNNER})
    # The explicit reports include some definitions and instances. Compare
    # every theorem they have in common with the full enumeration.
    endpoint_axioms = {**axioms, **section2_axioms, **section3a_axioms, **section3b_axioms}
    for name, dependencies in endpoint_axioms.items():
        if name not in all_declarations:
            continue
        if dependencies != all_declarations.get(name, {}).get("axioms"):
            raise RuntimeError(f"Axiom reports disagree for {name}")
    controls = negative_controls()
    run(["python3", "tools/check_endgame.py"], "section3a-numerical-checks.txt")
    after = {str(p.relative_to(ROOT)): sha(p) for p in [*project_sources(), *pins]}
    if before != after:
        raise RuntimeError("Lean sources or pins changed during verification; rerun on a fixed snapshot")
    reviewed = []
    review = ROOT / "certificates/manuscript-review.json"
    if review.exists():
        for item in json.loads(review.read_text())["files"]:
            path = ROOT / item["path"]
            actual = sha(path) if path.is_file() else None
            if actual is not None and actual != item["sha256"]:
                raise RuntimeError("Reviewed manuscript/source has changed: " + item["path"])
            reviewed.append({**item, "present": actual is not None})
    result = {
        "success": True,
        "scope": "Sections 2 and 3 relative to the stated geometry, topology, and correction-term inputs",
        "checked_at_utc": datetime.datetime.now(datetime.timezone.utc).isoformat(),
        "clean_project_build": opts.clean,
        "tool_versions": versions,
        "dependency_revisions": revisions,
        "section2_triangulation_build_order": triangulation_shards,
        "source_count": len(sources),
        "audited_endpoint_count": len(endpoint_axioms),
        "audited_project_theorem_count": len(all_declarations),
        "allowed_foundational_axioms": sorted(ALLOWED_AXIOMS),
        "axioms": axioms,
        "section2_reference_axioms": section2_axioms,
        "section3a_reference_axioms": section3a_axioms,
        "section3b_reference_axioms": section3b_axioms,
        "project_theorem_axioms": all_declarations,
        "negative_controls": controls,
        "reviewed_inputs": reviewed,
        "source_and_pin_sha256": before,
    }
    result_path.write_text(json.dumps(result, indent=2) + "\n")
    print(f"Verified {len(sources)} Lean source files and audited {len(all_declarations)} theorems.")
    print("All negative controls passed. The reference hypotheses are in the three section reports.")


if __name__ == "__main__":
    main()
