"""Validate Section 6.6 without altering any historical frozen baseline."""
from pathlib import Path
import hashlib
import json
import re

root = Path(__file__).resolve().parents[1]
audit = root / "audit"

def read(path):
    data = path.read_bytes()
    return data.decode("utf-16" if data.startswith((b"\xff\xfe", b"\xfe\xff")) else "utf-8-sig")

def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def without_comments(source):
    # Lean block comments nest; ordinary prose can contain words such as "admit".
    out, depth, i = [], 0, 0
    while i < len(source):
        if source.startswith("/-", i):
            depth += 1
            i += 2
        elif depth and source.startswith("-/", i):
            depth -= 1
            i += 2
            out.append(" ")
        elif not depth and source.startswith("--", i):
            i = source.find("\n", i)
            if i < 0:
                break
        else:
            if not depth:
                out.append(source[i])
            i += 1
    return "".join(out)

manifest = json.loads(read(audit / "section66-audit-manifest.json"))
log = read(audit / "section66-closed-audit.log")
allowed = {"propext", "Classical.choice", "Quot.sound"}
reports = {}
for name, axioms in re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", log):
    reports[name] = [s.strip() for s in re.sub(r"\.\{[^}]*\}", "", axioms).split(",") if s.strip()]
for name in re.findall(r"'([^']+)' does not depend on any axioms", log):
    reports[name] = []
missing = sorted(set(manifest["declarations"]) - reports.keys())
unexpected = {n: sorted(set(a) - allowed) for n, a in reports.items() if set(a) - allowed}
errors = re.findall(r"^.*\berror(?:\([^)]*\))?:.*$", log, re.M)
build = read(audit / "section66-full-build.log")
match = re.search(r"Build completed successfully \((\d+) jobs\)", build)
build_passed = bool(match) and not re.search(r"\berror(?:\([^)]*\))?:", build)
forbidden = {}
for module in manifest["modules"]:
    hits = re.findall(r"\bsorry\b|\badmit\b|^\s*axiom\b|\bunsafe\b|\bnative_decide\b",
                      without_comments(read(root / module)), re.M)
    if hits:
        forbidden[module] = hits
baseline = json.loads(read(audit / "section6-contract-freeze.json"))
contract_files = [p for p in baseline if p.startswith("Luce/Section6") and
                  ("Contract" in p or "Definitions" in p)]
changed_contracts = [p for p in contract_files if digest(root / p) != baseline[p]]
result = {
    "section66_complete": build_passed and not (missing or unexpected or errors or forbidden or changed_contracts),
    "modules": len(manifest["modules"]), "theorems": len(manifest["theorems"]),
    "declarations": len(manifest["declarations"]), "axiom_reports": len(reports),
    "missing_reports": missing, "unexpected_axioms": unexpected, "lean_errors": errors,
    "allowed_axioms": sorted(allowed), "forbidden_source_constructs": forbidden,
    "full_build": {"passed": build_passed, "jobs": int(match[1]) if match else None},
    "original_contract_files_checked": contract_files, "changed_contracts": changed_contracts,
    "baseline_reset": False,
    "scope": ["Fixed-point Gaussian limit", "Fixed-point mean asymptotic",
              "Uniform bounded means for every cycle length at least two",
              "Midpoint and interior grids; arbitrary probability spaces with full Luce masses"],
    "sha256": {p: digest(root / p) for p in manifest["modules"]},
}
(audit / "section66-validation.json").write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
print(json.dumps({k: v for k, v in result.items() if k != "sha256"}, indent=2))
if not result["section66_complete"]:
    raise SystemExit(1)
