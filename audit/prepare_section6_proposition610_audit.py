"""Generate a dedicated type/axiom inventory; never replace a frozen baseline."""
from pathlib import Path
import json
import re

root = Path(__file__).resolve().parents[1]
suffixes = '''CoreCategoryDefinitions Proposition610Contract CategoryCycleDefinitions
CategoryCycleBlocks CategoryCycleEquivalence CategoryCycleCounting CategoryFactorialExpectation
CoreCategoryDisjoint CoreDepthEquivalence CoreIdealCategorySum FactorialCoreCutoffs
FactorialKernelRows FactorialIdealRows CornerPotential WeightedCycleEdges NonmoderateCycles
FactorialDominationData CollisionVaryingMatrices FiniteBadSetSum FactorialFamilyBounds
NonmoderateFamilies CoreFamilyBadSet FiniteRankReindex CoreFamilyDefinitions
CoreFamilyDomination CoreFamilyIdealBounds CoreFamilyLocalLaw CoreFamilyComparison
FactorialCommonConstants FiniteKernelBounds FactorialErrorAlgebra CoreFamilyQuantitative
CategoryCoreEnumeration RestrictedAssignmentSums CategoryCoreActualSum CategoryCoreIdealSum
Proposition610 Proposition610Audit'''.split()
files = [f'Luce/Section6{s}.lean' for s in suffixes]
names = []
for rel in files:
    text = (root / rel).read_text(encoding='utf-8-sig')
    names.extend('Luce.Section6.' + name for name in
                 re.findall(r'^theorem\s+([^\s{(]+)', text, re.M))
assert len(names) == len(set(names))
lines = ['import Luce.Section6Proposition610Audit', '',
         'set_option pp.explicit true', 'set_option pp.universes true',
         'set_option pp.fullNames true', 'set_option pp.proofs false', '',
         '#print Luce.Section6.Proposition610Contract.proposition610',
         '#print Luce.Section6.CoreCycleCategory',
         '#print Luce.Section6.CoreCategoriesDisjoint',
         '#print Luce.Section6.coreCategoryCount',
         '#print Luce.Section6.coreCategoryIdealMean', '']
for name in names:
    lines.extend([f'#print {name}', f'#print axioms {name}'])
lines.extend(['', 'example : Luce.Section6.Proposition610Contract.proposition610 :=',
              '  Luce.Section6.proposition610_contractCheck'])
(root / 'audit/Section6Proposition610.lean').write_text('\n'.join(lines)+'\n', encoding='utf-8')
(root / 'audit/section6-proposition610-manifest.json').write_text(
    json.dumps({'files': files, 'theorems': names}, indent=2)+'\n', encoding='utf-8')
print(f'{len(files)} modules; {len(names)} theorem declarations.')
