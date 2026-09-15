"""Generate the Section 6.6 type and transitive-axiom audit."""
from pathlib import Path
import json
import re

root = Path(__file__).resolve().parents[1]
modules = sorted((root / "Luce").glob("Section6Critical*.lean"))
modules += [root / "Luce/Section6BernoulliReferenceApproximation.lean",
            root / "Luce/Section6BernoulliReferenceMean.lean"]
declarations = []
theorems = []
for path in modules:
    namespace = []
    for line in path.read_text(encoding="utf-8").splitlines():
        match = re.match(r"namespace\s+(\S+)", line)
        if match:
            namespace.append(match[1])
        elif re.match(r"end\s+\S+", line):
            namespace.pop()
        match = re.match(r"(?:@\[[^\]]*\]\s*)*(theorem|def|abbrev|instance)\s+([^\s{(]+)", line)
        if match:
            name = ".".join(namespace + [match[2]])
            declarations.append(name)
            if match[1] == "theorem":
                theorems.append(name)
assert len(declarations) == len(set(declarations))
lines = ["import Luce.Section6CriticalAudit", "", "set_option pp.explicit true",
         "set_option pp.universes true", "set_option pp.fullNames true",
         "set_option pp.proofs false", "", "#print SampledProfileContract.critical",
         "#print Luce.Section6.CriticalProfile", "#print Luce.Section6.SampledRates", ""]
for name in sorted(declarations):
    lines += [f"#print {name}", f"#print axioms {name}"]
(root / "audit/Section66Closed.lean").write_text("\n".join(lines) + "\n", encoding="utf-8")
(root / "audit/section66-audit-manifest.json").write_text(json.dumps({
    "modules": [p.relative_to(root).as_posix() for p in modules],
    "declarations": sorted(declarations), "theorems": sorted(theorems),
}, indent=2) + "\n", encoding="utf-8")
print(f"Generated audit for {len(declarations)} declarations, including {len(theorems)} theorems, in {len(modules)} modules.")
