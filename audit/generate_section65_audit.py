"""Generate the dedicated Section 6.5 audit, preserving all older audit generators."""
from pathlib import Path
import json
import re

root = Path(__file__).resolve().parents[1]
modules = sorted((root / "Luce").glob("Section65*.lean"))
names = []
declarations = []
for path in modules:
    entries = re.findall(
        r"^(?:@\[[^\]\n]*\]\s*)*(theorem|def|abbrev|instance)\s+([^\s{(]+)",
        path.read_text(encoding="utf-8"), re.M)
    names.extend("Luce.Section6." + name for kind, name in entries if kind == "theorem")
    declarations.extend("Luce.Section6." + name for _, name in entries)
assert len(names) == len(set(names)), "Duplicate theorem names in new modules"
assert len(declarations) == len(set(declarations)), "Duplicate declaration names in new modules"
lines = ["import Luce.Section65Audit", "", "set_option pp.explicit true",
         "set_option pp.universes true", "set_option pp.fullNames true",
         "set_option pp.proofs false", "", "#print SampledProfileContract.powerLaw",
         "#print SampledProfileContract.spatial", ""]
for name in sorted(declarations):
    lines.extend([f"#print {name}", f"#print axioms {name}"])
(root / "audit/Section65Closed.lean").write_text("\n".join(lines) + "\n", encoding="utf-8")
(root / "audit/section65-audit-manifest.json").write_text(json.dumps({
    "modules": [path.relative_to(root).as_posix() for path in modules],
    "theorems": sorted(names),
    "declarations": sorted(declarations),
}, indent=2) + "\n", encoding="utf-8")
print(f"Generated audit for {len(declarations)} declarations, including {len(names)} theorems, in {len(modules)} new modules.")
