from pathlib import Path
import re
from collections import Counter

ROOT = Path(__file__).resolve().parents[1]

def mask_comments(s):
    out = list(s)
    i = 0
    depth = 0
    string = False
    while i < len(s):
        if depth:
            if s.startswith('/-', i):
                out[i:i+2] = '  '; depth += 1; i += 2
            elif s.startswith('-/', i):
                out[i:i+2] = '  '; depth -= 1; i += 2
            else:
                if s[i] != '\n': out[i] = ' '
                i += 1
        elif string:
            if s[i] == '\\': i += 2
            elif s[i] == '"': string = False; i += 1
            else: i += 1
        elif s.startswith('/-', i):
            out[i:i+2] = '  '; depth = 1; i += 2
        elif s.startswith('--', i):
            j = s.find('\n', i)
            if j < 0: j = len(s)
            out[i:j] = ' ' * (j-i); i = j
        elif s[i] == '"': string = True; i += 1
        else: i += 1
    return ''.join(out)

decl = re.compile(r'(?m)^[ \t]*(?:@\[[^\n]*?\][ \t]*)?(?:(?:private|protected|noncomputable|unsafe|partial)\s+)*(theorem|lemma|axiom|opaque|def|abbrev|structure|class|inductive|instance|example)\b')

def signature_end(s, start, end):
    depth = 0
    for i in range(start, end):
        c = s[i]
        if c in '([{⦃': depth += 1
        elif c in ')]}⦄': depth -= 1
        if depth == 0 and s.startswith(':=', i): return i
    return end

files = sorted((ROOT/'Luce').glob('*.lean')) + sorted((ROOT/'proposals').glob('*.lean')) + sorted(p for p in (ROOT/'audit').glob('*.lean') if p.name != 'Sections1To7CurrentInventory.lean')
records = []
for p in files:
    s = p.read_text(encoding='utf-8-sig')
    clean = mask_comments(s)
    matches = list(decl.finditer(clean))
    items = []
    for ix, m in enumerate(matches):
        kind = m.group(1)
        line = s.count('\n', 0, m.start()) + 1
        nextpos = matches[ix+1].start() if ix+1 < len(matches) else len(s)
        # Stop before following top-level commands, retaining structure fields.
        tail = re.search(r'(?m)^(?:end|namespace|section|noncomputable section|open|variable|attribute|set_option|#)\b', clean[m.end():nextpos])
        if tail: nextpos = m.end() + tail.start()
        end = signature_end(clean, m.end(), nextpos)
        header = clean[m.start():end].strip()
        name_match = re.match(r'\s+([^\s({:\[]+)', clean[m.end():])
        name = name_match.group(1) if name_match and kind not in ('example', 'instance') else f'{kind} at line {line}'
        # Definitions and structures are included in full, since Prop definitions can be proposals.
        if kind not in ('theorem', 'lemma', 'example'):
            header = clean[m.start():nextpos].strip()
        # Select only the immediately preceding documentation comment.
        preceding = s[:m.start()].rstrip()
        description = ''
        if preceding.endswith('-/'):
            j = preceding.rfind('/--')
            if j >= 0 and '-/' not in preceding[j+3:-2]:
                description = preceding[j+3:-2].strip()
        items.append((kind, name, line, header, description))
    records.append((p, clean, items))

out = ['# Current Lean statements and axioms', '', 'Snapshot: 2026-09-11. Project-owned Lean sources only; dependency libraries under `.lake` are excluded.', '',
       'This catalog lists every source theorem and lemma (including private helpers), anonymous example, definition, structure, class, inductive type, and instance. Theorem proofs are omitted; their source signatures and documentation are retained. Definitions are shown so that an unasserted `Prop` is not mistaken for a proved theorem. Namespace and shared-variable context is listed per file; source links are authoritative for scope. Compiler-generated declarations are excluded from these source counts.', '',
       '## Counts', '', '| Area | Files | Theorems/lemmas | Definitions/abbreviations | Structures/classes | Instances | Examples | Axioms/opaque |', '|---|---:|---:|---:|---:|---:|---:|---:|']
for area in ('Luce', 'proposals', 'audit'):
    rows = [(p, c, it) for p,c,it in records if p.relative_to(ROOT).parts[0] == area]
    c = Counter(k for _,_,it in rows for k,*_ in it)
    out.append(f'| {area} | {len(rows)} | {c["theorem"]+c["lemma"]} | {c["def"]+c["abbrev"]} | {c["structure"]+c["class"]} | {c["instance"]} | {c["example"]} | {c["axiom"]+c["opaque"]} |')
    print(area, len(rows), dict(c))
out += ['', '## Axioms and proof status', '',
        'The [fresh compiler inventory](../audit/all-proved-statements.log) prints the elaborated types and transitive axioms of imported project theorem constants, including private and generated auxiliaries and all three closed contract checks. Its final INVENTORY_TOTAL and INVENTORY_AXIOM_UNION lines record the actual totals and axiom dependencies. Source signatures below retain local variable names; consult the compiler inventory for the complete implicit and instance parameters.', '',
        'The [reproducible audit](../audit/Sections1To7AllProvedStatements.lean) imports the default Luce library. Mathematical hypotheses in theorem parameters and structure fields are distinct from global axioms. Source declarations in proposals and audit files below are explicitly separate from production results; a definition of Prop is not a proof.', '',
        'The mathematical standing assumptions are defined in `Luce/Section1Model.lean`, `Luce/Section1Assumptions.lean`, and `Luce/Section4EndpointShellDefinitions.lean`. ProfileAssumption, ProfileLimit, EndpointAssumption, and EndpointShellAssumption are predicates, not declarations asserting their truth. The final migration build passed with 3893 jobs; see [actual build output](../audit/section5-final-build.log).', '',
        'Both revised Section 4 and Section 5 main theorems and their independent closed contract checks are now proved. This includes the full joint factorial-moment argument, short-cycle Poisson limit, full intensity integrability, and joint total variation. Legacy uniform-endpoint estimates remain separate stronger-case theorems. See [final report](section5-final-report.md) and [completed obligation ledger](shell-obligation-ledger.md).', '', '## File index', '']
for p,_,items in records:
    rel = p.relative_to(ROOT).as_posix()
    anchor = rel.lower().replace('/', '').replace('.', '')
    out.append(f'- [{rel}](#{anchor}): {len(items)} declarations')
for p, clean, items in records:
    rel = p.relative_to(ROOT).as_posix()
    out += ['', f'## {rel}', '', f'[Source]({p.as_posix()})', '']
    context = []
    lines = clean.splitlines()
    for ix, line in enumerate(lines):
        if re.match(r'^(?:namespace|section|noncomputable section|open|universe|variable)\b', line):
            chunk = [line]
            if line.startswith('variable'):
                j = ix+1
                while j < len(lines) and lines[j].startswith('    '):
                    chunk.append(lines[j]); j += 1
            context.append('\n'.join(chunk))
    if context: out += ['Namespace / shared context (consult source for section boundaries):', '', '```lean', '\n'.join(context), '```', '']
    if not items: out += ['No declarations; imports or audit commands only.', '']
    for kind, name, line, header, description in items:
        out += [f'### {name}', '', f'{kind}; [source line {line}]({p.as_posix()}:{line})', '']
        if description: out += [description, '']
        out += ['```lean', header, '```', '']
(ROOT/'docs/current-statements-and-axioms.md').write_text('\n'.join(out), encoding='utf-8')
print('Catalog written.')
