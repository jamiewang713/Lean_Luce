"""Freeze the independent Proposition 6.5 target without changing earlier baselines."""
from pathlib import Path
import hashlib
import json
import re
root = Path(__file__).resolve().parents[1]
target = root / 'audit/section6-proposition65-contract-freeze.json'
paths = set()
def visit(path):
    if path in paths:
        return
    paths.add(path)
    for module in re.findall(r'^import\s+(Luce(?:\.[\w]+)*)\s*$', path.read_text(encoding='utf-8-sig'), re.M):
        visit(root / (module.replace('.', '/') + '.lean'))
visit(root / 'Luce/Section6Proposition65Contract.lean')
paths.update(root / name for name in ('fixed_points_sampled_profile.tex', 'lean-toolchain', 'lakefile.toml', 'lake-manifest.json'))
snapshot = {p.relative_to(root).as_posix(): hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted(paths)}
if target.exists():
    old = json.loads(target.read_text())
    changed = [p for p, h in old.items() if not (root / p).exists() or hashlib.sha256((root / p).read_bytes()).hexdigest() != h]
    print(json.dumps({'frozen_files': len(old), 'changed': changed}))
    if changed:
        raise SystemExit(1)
else:
    target.write_text(json.dumps(snapshot, indent=2)+'\n', encoding='utf-8')
    print(f'Frozen {len(snapshot)} Proposition 6.5 files; earlier baselines unchanged.')
