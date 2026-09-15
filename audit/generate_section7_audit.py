"""Generate and validate the dedicated Section 7 source/type/axiom audit."""
from pathlib import Path
import hashlib
import json
import re
import sys

ROOT = Path(__file__).resolve().parents[1]
AUDIT = ROOT / "audit"
MODULES = sorted((ROOT / "Luce").glob("Section7*.lean"))
DECL = re.compile(r"^(?:theorem|lemma|def|structure)\s+([\w.]+)", re.MULTILINE)


def names():
    return ["Luce.Section7." + name for path in MODULES
            for name in DECL.findall(path.read_text(encoding="utf-8-sig"))]


def generate():
    declarations = names()
    lines = ["import Luce", "", "set_option pp.explicit true",
             "set_option pp.universes true", "set_option pp.fullNames true",
             "set_option pp.proofs false", ""]
    for name in declarations:
        lines += [f"#print {name}", f"#print axioms {name}", ""]
    (AUDIT / "Section7.lean").write_text("\n".join(lines), encoding="utf-8")
    print(f"Generated type and transitive-axiom checks for {len(declarations)} declarations.")


def validate():
    declarations = names()
    output = (AUDIT / "section7-audit.log").read_text(encoding="utf-8-sig")
    reports = dict(re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", output))
    for name in re.findall(r"'([^']+)' does not depend on any axioms", output):
        reports[name] = ""
    allowed = {"propext", "Classical.choice", "Quot.sound"}
    # Pretty-printed universe arguments are not part of an axiom's name.
    reports = {name: re.sub(r"\.\{[^}]*\}", "", axioms) for name, axioms in reports.items()}
    forbidden_axioms = {name: sorted(set(filter(None, map(str.strip, axioms.split(",")))) - allowed)
                        for name, axioms in reports.items()}
    forbidden_axioms = {name: axioms for name, axioms in forbidden_axioms.items() if axioms}
    missing = sorted(set(declarations) - reports.keys())
    source_issues = {}
    for path in MODULES:
        text = path.read_text(encoding="utf-8-sig")
        hits = re.findall(r"\b(?:sorry|admit|axiom|unsafe)\b|set_option\s+\S+", text)
        if hits:
            source_issues[str(path.relative_to(ROOT))] = hits
    contract = json.loads((AUDIT / "section7-contract-freeze.json").read_text(encoding="utf-8-sig"))
    contract_checks = {row["Path"]: hashlib.sha256(Path(row["Path"]).read_bytes()).hexdigest().upper()
                       == row["Hash"] for row in contract}
    baseline = json.loads((AUDIT / "section7-input-hashes.json").read_text(encoding="utf-8-sig"))
    changed = [row["path"] for row in baseline
               if hashlib.sha256(Path(row["path"]).read_bytes()).hexdigest().upper() != row["sha256"]]
    unexpected_changes = [path for path in changed if Path(path) != ROOT / "Luce.lean"]
    original_entry = next(row["sha256"] for row in baseline if Path(row["path"]) == ROOT / "Luce.lean")
    entry = (ROOT / "Luce.lean").read_bytes()
    without_new_import = re.sub(rb"import Luce\.Section7\r?\n?", b"", entry)
    entry_only_adds_import = hashlib.sha256(without_new_import).hexdigest().upper() == original_entry
    build = (AUDIT / "section7-full-build.log").read_text(encoding="utf-8-sig")
    build_passed = "Build completed successfully" in build and "error: build failed" not in build
    audit_passed = "error:" not in output and not missing and not forbidden_axioms
    result = {
        "status": "passed" if all([build_passed, audit_passed, not source_issues,
                                     all(contract_checks.values()), not unexpected_changes,
                                     entry_only_adds_import]) else "failed",
        "source_modules": len(MODULES), "declarations": len(declarations),
        "axiom_reports": len(reports), "full_build_passed": build_passed,
        "audit_passed": audit_passed, "missing_reports": missing,
        "forbidden_axioms": forbidden_axioms, "source_issues": source_issues,
        "contract_hashes_unchanged": contract_checks,
        "preexisting_files_checked": len(baseline),
        "unexpected_preexisting_changes": unexpected_changes,
        "library_entry_only_adds_section7_import": entry_only_adds_import,
        "source_sha256": {str(path.relative_to(ROOT)): hashlib.sha256(path.read_bytes()).hexdigest()
                          for path in MODULES},
    }
    (AUDIT / "section7-validation.json").write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({key: value for key, value in result.items() if key != "source_sha256"}, indent=2))
    return result["status"] == "passed"


if __name__ == "__main__":
    if "--validate" in sys.argv:
        sys.exit(0 if validate() else 1)
    generate()
