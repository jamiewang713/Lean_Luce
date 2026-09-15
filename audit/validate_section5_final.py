"""Validate the concrete main theorem, closed check, and frozen meanings."""
from pathlib import Path
import hashlib
import json
import re

root = Path(__file__).resolve().parents[1]
data = (root / "audit/section5-final-audit.log").read_bytes()
output = data.decode("utf-16" if data.startswith((b"\xff\xfe", b"\xfe\xff")) else "utf-8-sig")
assert "error:" not in output, "Lean final audit failed"
reports = re.findall(r"'([^']+)' depends on axioms:\s*(\[[^]]*\])", output)
expected = {
    "Luce.section5_main_general", "section5_contractCheck",
    "Luce.EndpointShellAssumption.cycle_shell_tightness", "cycleShell_contractCheck",
    "Luce.EndpointShellAssumption.cycle_trace_integrable",
    "Luce.EndpointShellAssumption.bulk_intensity_tendsto",
    "Luce.bulk_joint_factorial_moments", "Luce.bulk_cycle_point_probability_limit",
    "Luce.EndpointShellAssumption.cycle_point_probability_limit",
    "Luce.CountableLaw.tendsto_probabilityTotalVariation_of_singletons",
    "Luce.CountableLaw.tendsto_bounded_integrals_of_totalVariation",
    "Luce.EndpointShellAssumption.cycle_vector_totalVariation",
    "Luce.EndpointShellAssumption.cycle_vector_weak",
    "Luce.cycleCountVector_raceDraw_eq_rank", "Luce.luce_cycle_vector_map_eq",
    "Luce.luce_cycle_test_integral_eq", "Luce.Shell.section4_main_poisson_general",
    "section4_contractCheck",
}
assert len(reports) == len(expected), (len(reports), len(expected))
assert {name for name, _ in reports} == expected
allowed = {"propext", "Classical.choice", "Quot.sound"}
for name, axioms in reports:
    names = {re.sub(r"\.\{[^}]*\}$", "", entry.strip()) for entry in axioms[1:-1].split(",")}
    assert names <= allowed, (name, names)
(root / "audit/section5-final-axioms.txt").write_text(
    "\n".join(f"'{name}' depends on axioms: {axioms}" for name, axioms in reports) + "\n", encoding="utf-8")
checks = {}
for name in ("shell-contract-freeze.json", "section5-contract-freeze.json",
             "section5-cycle-shell-contract-freeze.json"):
    frozen = json.loads((root / "audit" / name).read_text())
    changed = [path for path, digest in frozen.items()
               if hashlib.sha256((root / path).read_bytes()).hexdigest() != digest]
    checks[name] = {"count": len(frozen), "changed": changed}
    assert not changed, changed
root_module = (root / "Luce/Sections1To7.lean").read_text(encoding="utf-8-sig")
assert "import Luce.Section5ShellContractCheck" in root_module
assert "import Luce.Section4ShellContractCheck" in root_module
result = {"axiom_reports": len(reports), "freeze": checks, "contract_checks_in_build": True}
(root / "audit/section5-final-validation.json").write_text(json.dumps(result, indent=2))
(root / "audit/section5-freeze-check.json").write_text(json.dumps(checks, indent=2))
print(json.dumps(result))
