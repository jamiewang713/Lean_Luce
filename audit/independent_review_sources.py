"""Reproducible source inventory for the independent manuscript audit."""
from pathlib import Path
import hashlib
import json
import re

ROOT = Path(__file__).resolve().parents[1]

def strip_comments(text):
    out = []
    i = depth = 0
    string = False
    while i < len(text):
        pair = text[i:i+2]
        c = text[i]
        if depth:
            if pair == '/-':
                depth += 1
                out.extend('  ')
                i += 2
            elif pair == '-/':
                depth -= 1
                out.extend('  ')
                i += 2
            else:
                out.append('\n' if c == '\n' else ' ')
                i += 1
        elif string:
            out.append('\n' if c == '\n' else ' ')
            if c == '\\' and i + 1 < len(text):
                out.append(' ')
                i += 2
            else:
                if c == '"':
                    string = False
                i += 1
        elif pair == '/-':
            depth = 1
            out.extend('  ')
            i += 2
        elif pair == '--':
            j = text.find('\n', i)
            if j < 0:
                j = len(text)
            out.extend(' ' * (j-i))
            i = j
        elif c == '"':
            string = True
            out.append(' ')
            i += 1
        else:
            out.append(c)
            i += 1
    return ''.join(out)

files = [ROOT / 'Luce.lean']
for folder in ['Luce', 'audit', 'proposals']:
    files.extend(sorted((ROOT / folder).rglob('*.lean')))
records = []
imports = {}
for p in files:
    raw = p.read_text(encoding='utf-8-sig')
    clean = strip_comments(raw)
    rel = p.relative_to(ROOT).as_posix()
    mod = rel[:-5].replace('/', '.')
    deps = re.findall(r'^\s*(?:public\s+)?import\s+([\w.]+)', clean, re.M)
    imports[mod] = deps
    flags = []
    for match in re.finditer(r'\b(?:sorry|admit|axiom|opaque|unsafe|partial|native_decide|implemented_by|extern|run_elab|elab|macro|syntax)\b', clean):
        flags.append({'line': clean.count('\n', 0, match.start())+1, 'token': match.group()})
    records.append({'file': rel, 'module': mod, 'lines': len(raw.splitlines()),
                    'sha256': hashlib.sha256(p.read_bytes()).hexdigest(),
                    'imports': deps, 'flags': flags,
                    'theorems': len(re.findall(r'^\s*(?:(?:private|protected|noncomputable)\s+)*(?:theorem|lemma)\s+', clean, re.M)),
                    'definitions': len(re.findall(r'^\s*(?:(?:private|protected|noncomputable)\s+)*(?:def|abbrev)\s+', clean, re.M))})

def closure(start):
    visited = set()
    pending = list(start)
    while pending:
        mod = pending.pop()
        if mod in visited:
            continue
        visited.add(mod)
        pending.extend(imports.get(mod, []))
    return visited

default = closure(['Luce'])
production = {r['module'] for r in records if r['file'] == 'Luce.lean' or r['file'].startswith('Luce/')}
orphan = sorted(production-default)
summary = {
    'counts': {area: {'files': len(rs := [r for r in records if r['file'].split('/')[0] == area or (area == 'Luce' and r['file'] == 'Luce.lean')]),
                      'lines': sum(r['lines'] for r in rs),
                      'theorems': sum(r['theorems'] for r in rs),
                      'definitions': sum(r['definitions'] for r in rs)} for area in ['Luce','audit','proposals']},
    'production_not_reachable_from_Luce': orphan,
    'source_flags': [{'file': r['file'], **f} for r in records for f in r['flags']],
    'sources': records,
}
(ROOT/'audit/independent-review-source-inventory.json').write_text(json.dumps(summary, indent=2), encoding='utf-8')
print(json.dumps({k: v for k, v in summary.items() if k != 'sources'}, indent=2))
(ROOT/'audit/IndependentReviewImports.lean').write_text('\n'.join('import '+m for m in sorted(production))+'\n', encoding='utf-8')

paper = (ROOT/'fixed_points_sampled_profile.tex').read_text(encoding='utf-8-sig')
section = number = 0
claims = []
for match in re.finditer(r'\\section\{|\\begin\{(theorem|lemma|proposition|corollary|assumption|remark)\}', paper):
    if match.group(1) is None:
        section += 1
        number = 0
        continue
    kind = match.group(1)
    number += 1
    end = paper.find('\\end{'+kind+'}', match.end())
    statement = paper[match.end():end]
    labels = re.findall(r'\\label\{([^}]+)\}', statement)
    matches = []
    if labels:
        for rec in records:
            if rec['module'] not in production:
                continue
            raw = (ROOT/rec['file']).read_text(encoding='utf-8-sig')
            found = [lab for lab in labels if lab in raw]
            if found:
                matches.append({'file': rec['file'], 'labels': found})
    claims.append({'number':f'{section}.{number}', 'kind':kind, 'labels':labels,
                   'line':paper.count('\n',0,match.start())+1, 'statement':statement.strip(),
                   'source_label_mentions':matches})
(ROOT/'audit/independent-review-paper-claims.json').write_text(json.dumps(claims, indent=2), encoding='utf-8')
print('\nPAPER CLAIMS (label mentions indicate correspondence candidates, not proved coverage)')
for c in claims:
    print(c['number'], c['kind'], ','.join(c['labels'][:1]),
          '; '.join(m['file'] for m in c['source_label_mentions']) or 'NO LABEL MENTIONS')
