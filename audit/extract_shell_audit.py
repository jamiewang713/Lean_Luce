"""Extract actual Lean output without treating absent theorems as checked."""
from pathlib import Path
import re

root = Path(__file__).resolve().parents[1]
raw = (root / "audit/shell-statements-and-axioms.log").read_bytes()
output = raw.decode("utf-16" if raw.startswith((b"\xff\xfe", b"\xfe\xff")) else "utf-8-sig")
lines = [line for line in output.splitlines() if "depends on axioms:" in line]
assert len(lines) == 37, len(lines)
allowed = {"propext", "Classical.choice", "Quot.sound"}
for line in lines:
    names = set(re.search(r"\[([^]]*)\]", line).group(1).split(", "))
    assert names <= allowed, line
assert "error:" not in output
for required in ("Luce.Shell.section4_main_poisson_general", "section4_contractCheck",
                 "Luce.EndpointShellAssumption.expectation_tightness"):
    assert any(line.startswith("'" + required + "' depends on axioms:") for line in lines), required
(root / "audit/shell-axioms.txt").write_text("\n".join(lines) + "\n", encoding="utf-8")
contract = (root / "Luce/ShellMigrationContract.lean").read_text(encoding="utf-8")
report = root / "docs/shell-migration-report.md"
text = report.read_text(encoding="utf-8")
marker = "\n## Verbatim frozen contract source\n"
text = text.split(marker)[0]
text += marker + "\n```lean\n" + contract.rstrip() + "\n```\n"
text += "\n## Actual central axiom output\n\n```text\n" + "\n".join(lines) + "\n```\n"
report.write_text(text, encoding="utf-8")
print(f"Verified and extracted {len(lines)} actual axiom reports; no disallowed dependency.")
