"""Print all source theorem types and axioms without asserting any open CLT."""
from pathlib import Path
import re

root = Path(__file__).resolve().parents[1]
names = []
for path in sorted((root / 'Luce').glob('Section6*.lean')):
    names.extend('Luce.Section6.' + name for name in re.findall(
        r'^theorem\s+([^\s{(]+)', path.read_text(encoding='utf-8'), re.M))
lines = ['import Luce.Section6', '', 'set_option pp.explicit true',
         'set_option pp.universes true', 'set_option pp.fullNames true',
         'set_option pp.proofs false', '',
         '#print SampledProfileContract.powerLaw', '#print SampledProfileContract.spatial',
         '#print SampledProfileContract.critical', '#print SampledProfileContract.section6', '']
for definition in ['Luce.Weights', 'Luce.WeightArray',
                   'Luce.Section6.Proposition65Contract.localLaw',
                   'Luce.Section6.Proposition65Contract.proposition65',
                   'Luce.Section6.localCornerQ', 'Luce.Section6.localCornerExponent',
                   'Luce.Section6.localCornerRatio', 'Luce.Section6.localIdealKernel',
                   'Luce.Section6.localEnvelopeKernel',
                   'Luce.Section6.skeletonStart',
                   'Luce.Section6.laterSelectedRate', 'Luce.Section6.selectedFill',
                   'Luce.Section6.Lemma64Contract.matrix',
                   'Luce.Section6.Lemma64Contract.cycles',
                   'Luce.Section6.Lemma64Contract.lemma64',
                   'Luce.Section6.intervalDiscardedCycleCount',
                   'Luce.Section6.PowerProfile', 'Luce.Section6.LeftBehavior',
                   'Luce.Section6.RightBehavior', 'Luce.Section6.PowerExpansion',
                   'Luce.Section6.SampledRates', 'Luce.Section6.samplePoint',
                   'Luce.Section6.insertionChoices',
                   'Luce.Section6.insertionDominationENN',
                   'Luce.Section6.insertionDominationMatrix',
                   'Luce.Section6.exceptionalEnvelope',
                   'Luce.Section6.extremeTypicalEnvelope',
                   'Luce.Section6.restrictedKernelSums']:
    lines.append(f'#print {definition}')
for name in sorted(names):
    lines.extend([f'#print {name}', f'#print axioms {name}'])
(root / 'audit/Section6Current.lean').write_text('\n'.join(lines) + '\n', encoding='utf-8')
print(f'Generated type and axiom audit for {len(names)} named source theorems.')
