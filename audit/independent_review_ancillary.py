"""Compile each existing audit/proposal source and preserve per-file evidence."""
from pathlib import Path
from concurrent.futures import ThreadPoolExecutor, as_completed
import json
import subprocess
import time

root = Path(__file__).resolve().parents[1]
out = root/'audit/independent-review-ancillary'
out.mkdir(exist_ok=True)
files = sorted((root/'proposals').glob('*.lean')) + sorted(
    p for p in (root/'audit').glob('*.lean') if not p.name.startswith('Sections1To7IndependentReview'))

def check(path):
    start = time.monotonic()
    rel = path.relative_to(root).as_posix()
    logfile = out/(path.parent.name+'-'+path.stem+'.log')
    try:
        with logfile.open('w', encoding='utf-8') as stream:
            proc = subprocess.run(['lake', 'env', 'lean', rel], cwd=root,
                                  stdout=stream, stderr=subprocess.STDOUT, timeout=300)
        status = proc.returncode
    except subprocess.TimeoutExpired:
        status = 'timeout'
    return {'file': rel, 'exit_code': status, 'seconds': round(time.monotonic()-start, 2),
            'log': logfile.relative_to(root).as_posix()}

results = []
with ThreadPoolExecutor(max_workers=2) as pool:
    for future in as_completed([pool.submit(check, path) for path in files]):
        result = future.result()
        results.append(result)
        print(json.dumps(result), flush=True)
        (out/'results.json').write_text(json.dumps(sorted(results, key=lambda r:r['file']), indent=2), encoding='utf-8')
print(json.dumps({'checked':len(results), 'passed':sum(r['exit_code']==0 for r in results),
                  'failed':[r for r in results if r['exit_code']!=0]}), flush=True)
