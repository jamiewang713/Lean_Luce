"""Validate the new closed Section 6.5 proofs without resetting old baselines."""
from pathlib import Path
import hashlib
import json
import re

root = Path(__file__).resolve().parents[1]
audit = root / "audit"
allowed = {"propext", "Classical.choice", "Quot.sound"}

def read(path):
    data = path.read_bytes()
    return data.decode("utf-16" if data.startswith((b"\xff\xfe", b"\xfe\xff")) else "utf-8-sig")

def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def inspect_log(path, names):
    text = read(path)
    found = {}
    for name, axioms in re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", text):
        axioms = re.sub(r"\.\{[^}]*\}", "", axioms)
        found[name] = [a.strip() for a in axioms.split(",") if a.strip()]
    for name in re.findall(r"'([^']+)' does not depend on any axioms", text):
        found[name] = []
    missing = sorted(set(names) - found.keys())
    unexpected = {n: sorted(set(a) - allowed) for n, a in found.items() if set(a) - allowed}
    errors = [line for line in text.splitlines() if re.search(r"\berror(?:\([^)]*\))?:", line)]
    return {"expected_declarations": len(names), "axiom_reports": len(found),
            "missing_reports": missing, "unexpected_axioms": unexpected, "lean_errors": errors,
            "passed": not (missing or unexpected or errors)}

manifest = json.loads(read(audit / "section65-audit-manifest.json"))
dedicated = inspect_log(audit / "section65-closed-audit.log", manifest["declarations"])
current_names = re.findall(r"^#print axioms (\S+)", read(audit / "Section6Current.lean"), re.M)
current = inspect_log(audit / "section65-current-audit.log", current_names)
current["new_missing_reports"] = sorted(set(current["missing_reports"]) & set(manifest["theorems"]))
current["outside_scope_missing_reports"] = sorted(set(current["missing_reports"]) - set(manifest["theorems"]))
build_text = read(audit / "section65-full-build.log")
build_match = re.search(r"Build completed successfully \((\d+) jobs\)", build_text)
build = {"passed": bool(build_match) and not re.search(r"\berror(?:\([^)]*\))?:", build_text),
         "jobs": int(build_match.group(1)) if build_match else None}
snapshots = {}
for name in ["section65-contract-freeze.json", "section6-proposition610-contract-freeze.json",
             "section6-lemma69-contract-freeze.json", "section6-proposition65-contract-freeze.json",
             "section6-contract-freeze.json"]:
    baseline = json.loads(read(audit / name))
    changes = {p: {"expected": h, "actual": digest(root / p) if (root / p).exists() else None}
               for p, h in baseline.items() if not (root / p).exists() or digest(root / p) != h}
    snapshots[name] = {"files": len(baseline), "changed": changes, "baseline_reset": False}
source_names = {}
for path in sorted((root / "Luce").glob("Section6*.lean")):
    for name in re.findall(r"^theorem\s+([^\s{(]+)", read(path), re.M):
        source_names.setdefault("Luce.Section6." + name, []).append(path.relative_to(root).as_posix())
current["outside_scope_missing_sources"] = {
    name: source_names.get(name, []) for name in current["outside_scope_missing_reports"]}
frozen_paths = set(json.loads(read(audit / "section65-contract-freeze.json")))
current["outside_scope_sources_absent_from_initial_snapshot"] = sorted({
    path for paths in current["outside_scope_missing_sources"].values()
    for path in paths if path not in frozen_paths})
supplement_names = re.findall(r"^#print axioms (\S+)", read(audit / "Section65HistoricalNamespaceSupplement.lean"), re.M)
supplement = inspect_log(audit / "section65-historical-namespace-supplement.log", supplement_names)
forbidden = {}
for path in manifest["modules"]:
    hits = re.findall(r"\bsorry\b|\badmit\b|^\s*axiom\b|\bunsafe\b|\bnative_decide\b", read(root / path), re.M)
    if hits:
        forbidden[path] = hits
passed = (dedicated["passed"] and build["passed"] and not forbidden
          and not snapshots["section65-contract-freeze.json"]["changed"]
          and not current["new_missing_reports"])
result = {"section65_complete": passed, "new_modules": len(manifest["modules"]),
          "new_theorems": len(manifest["theorems"]),
          "new_declarations": len(manifest["declarations"]), "full_build": build,
          "dedicated_audit": dedicated, "section6_audit": current,
          "historical_namespace_supplement": supplement,
          "allowed_axioms": sorted(allowed), "forbidden_source_constructs": forbidden,
          "snapshots": snapshots,
          "scope": ["SampledProfileContract.powerLaw: both grids",
                    "SampledProfileContract.spatial: both grids, including localization"],
          "critical_subsection_included": False,
          "sha256": {p: digest(root / p) for p in manifest["modules"]}}
(audit / "section65-validation.json").write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
print(json.dumps({k: result[k] for k in ["section65_complete", "new_modules", "new_theorems", "full_build", "dedicated_audit"]}, indent=2))
print("Whole Section 6 audit:", current["axiom_reports"], "/", current["expected_declarations"], "passed:", current["passed"])
print("Frozen mismatches:", {n: list(s["changed"]) for n, s in snapshots.items()})
if not passed:
    raise SystemExit(1)
