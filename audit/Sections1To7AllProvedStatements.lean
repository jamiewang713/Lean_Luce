import Luce.Sections1To7
import Lean.Util.CollectAxioms

set_option pp.explicit true
set_option pp.universes true
set_option pp.fullNames true
set_option pp.proofs false

set_option maxHeartbeats 0 in
run_elab do
  let env ← Lean.getEnv
  let mut roots : Array Lean.Name := #[]
  for (name, info) in env.constants.toList do
    if name.toString.startsWith "Luce." || name.toString.startsWith "_private.Luce." ||
        name == `section4_contractCheck || name == `section5_contractCheck ||
        name == `cycleShell_contractCheck then
      if info.isTheorem || info.isAxiom then
        roots := roots.push name
  let mut axioms : Lean.NameSet := {}
  for name in roots.qsort Lean.Name.lt do
    let info := env.constants.find! name
    Lean.logInfo m!"STATEMENT {name} : {info.type}"
    let deps ← Lean.collectAxioms name
    for ax in deps do
      axioms := axioms.insert ax
    Lean.logInfo m!"AXIOMS {name}: {deps}"
  Lean.logInfo m!"INVENTORY_TOTAL: {roots.size} theorem/axiom constants (includes generated auxiliaries)"
  Lean.logInfo m!"INVENTORY_AXIOM_UNION: {axioms.toArray.qsort Lean.Name.lt}"
