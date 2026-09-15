"""Validate actual factorial-moment reports and the frozen semantic inputs."""
from pathlib import Path
import hashlib
import json
import re

root = Path(__file__).resolve().parents[1]
data = (root / "audit/section5-factorial-moments-audit.log").read_bytes()
output = data.decode("utf-16" if data.startswith((b"\xff\xfe", b"\xfe\xff")) else "utf-8-sig")
assert "error:" not in output, "Lean audit failed"
reports = re.findall(r"'[^']+' depends on axioms:\s*\[[^]]*\]", output)
assert len(reports) == 9, len(reports)
allowed = {"propext", "Classical.choice", "Quot.sound"}
for report in reports:
    names = {re.sub(r"\.\{[^}]*\}$", "", name.strip())
             for name in report.split("[", 1)[1][:-1].split(",")}
    assert names <= allowed, report
(root / "audit/section5-factorial-moments-axioms.txt").write_text("\n".join(reports) + "\n", encoding="utf-8")
checks = {}
for name in ("shell-contract-freeze.json", "section5-contract-freeze.json",
             "section5-cycle-shell-contract-freeze.json"):
    frozen = json.loads((root / "audit" / name).read_text())
    changed = [path for path, digest in frozen.items()
               if hashlib.sha256((root / path).read_bytes()).hexdigest() != digest]
    checks[name] = {"count": len(frozen), "changed": changed}
    assert not changed, changed
(root / "audit/section5-freeze-check.json").write_text(json.dumps(checks, indent=2))
print(json.dumps({"axiom_reports": len(reports), "freeze": checks}))
