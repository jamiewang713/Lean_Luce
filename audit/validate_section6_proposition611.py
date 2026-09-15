"""Build and audit the full Proposition 6.11 proof without changing its contract."""
from pathlib import Path
import hashlib
import json
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
MODULES = [
    "BernoulliCharacteristicEstimates", "BernoulliCharacteristic",
    "BernoulliCharacteristicDrift", "ComplexProbabilityConvergence",
    "BernoulliGaussianScale", "BernoulliCLTStopping", "BernoulliCLTCapped",
    "BernoulliCLT", "Section6Proposition611Contract", "Section6Proposition611",
    "Section6Proposition611Audit",
]
CONTRACT_SHA256 = "23bb19c0d7fafb6d43577eff3b1a96ad8b18a79b8b27988a7225d15004b8e713"
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}


def main():
    files = [ROOT / "Luce" / (name + ".lean") for name in MODULES]
    hashes = {p.relative_to(ROOT).as_posix(): hashlib.sha256(p.read_bytes()).hexdigest() for p in files}
    assert hashes["Luce/Section6Proposition611Contract.lean"] == CONTRACT_SHA256, "Contract changed"
    declarations = []
    for path in files:
        source = path.read_text(encoding="utf-8")
        assert not re.search(r"\b(sorry|admit|sorryAx|unsafe|implemented_by|native_decide)\b", source), path
        assert not re.search(r"^\s*axiom\b|set_option\s+(maxHeartbeats|maxRecDepth|debug\.)", source, re.M), path
        namespace = []
        for line in source.splitlines():
            match = re.match(r"namespace\s+(\S+)", line)
            if match:
                namespace.append(match.group(1))
            elif re.match(r"end\s+\S+", line):
                namespace.pop()
            else:
                match = re.match(r"theorem\s+(\S+)", line)
                if match:
                    declarations.append(".".join(namespace + [match.group(1)]))
    assert len(declarations) == len(set(declarations))
    audit = ROOT / "audit" / "Section6Proposition611.lean"
    lines = [
        "import Luce.Section6Proposition611Audit", "",
        "set_option pp.explicit true", "set_option pp.universes true",
        "set_option pp.fullNames true", "set_option pp.proofs false", "",
        "#print Luce.Section6.Proposition611Contract.proposition611", "",
    ]
    for name in declarations:
        lines.extend([f"#check {name}", f"#print axioms {name}"])
    audit.write_text("\n".join(lines) + "\n", encoding="utf-8")
    record = {"contract_sha256": CONTRACT_SHA256, "source_sha256": hashes,
              "declarations": declarations, "allowed_axioms": sorted(ALLOWED_AXIOMS)}
    commands = [
        ("build", ["lake", "build"]),
        ("axioms", ["lake", "env", "lean", "audit/Section6Proposition611.lean"]),
    ]
    for label, command in commands:
        log = ROOT / "audit" / f"section6-proposition611-{label}.log"
        with log.open("w", encoding="utf-8") as output:
            result = subprocess.run(command, cwd=ROOT, stdout=output, stderr=subprocess.STDOUT)
        record[label] = {"command": command, "exit_code": result.returncode,
                         "log": log.relative_to(ROOT).as_posix()}
        print(f"{label}: exit {result.returncode}", flush=True)
        if result.returncode:
            record["passed"] = False
            (ROOT / "audit/section6-proposition611-validation.json").write_text(
                json.dumps(record, indent=2) + "\n", encoding="utf-8")
            return result.returncode
    output = (ROOT / "audit/section6-proposition611-axioms.log").read_text(encoding="utf-8")
    reports = dict(re.findall(r"'([^']+)' depends on axioms:\s*\[(.*?)\]", output, re.S))
    reports.update({name: "" for name in re.findall(r"'([^']+)' does not depend on any axioms", output)})
    assert set(reports) == set(declarations), (set(declarations) - set(reports), set(reports) - set(declarations))
    for name, report in reports.items():
        axioms = {re.sub(r"\.\{[^}]*\}", "", x.strip()) for x in report.split(",") if x.strip()}
        assert axioms <= ALLOWED_AXIOMS, (name, axioms)
    record["passed"] = True
    record["theorem_count"] = len(declarations)
    (ROOT / "audit/section6-proposition611-validation.json").write_text(
        json.dumps(record, indent=2) + "\n", encoding="utf-8")
    print(f"PASS: {len(declarations)} theorem types and transitive axiom reports; contract unchanged", flush=True)
    return 0


if __name__ == "__main__":
    sys.exit(main())
