import Luce.Section5ExceptionalLow
import Lean.Util.CollectAxioms

/- Proof integrity audit: read-only traversal of actual checked theorem bodies. -/
#print axioms Luce.section5_proposition54
#print axioms Luce.ProfileLimit.low_rate_cycles_vanish
#print axioms Luce.ProfileLimit.bounded_cycle_probability_uniform
set_option pp.proofs true in
#print Luce.section5_proposition54
/- Walk actual checked types and bodies, independently of the source scan
and of the cached axiom lists printed above. Include constructors of
inductive types, following Lean's own axiom-collection convention. -/
set_option maxHeartbeats 0 in
run_elab do
  let env ← Lean.getEnv
  let roots : List Lean.Name := [``Luce.section5_proposition54,
    ``Luce.ProfileLimit.low_rate_cycles_vanish, ``Luce.ProfileLimit.bounded_cycle_probability_uniform]
  for root in roots do
    let some info := env.checked.get.find? root
      | throwError "Missing final declaration: {root}"
    unless info.isTheorem do
      throwError "Final declaration is not a theorem: {root}"
  let mut pending := roots
  let mut seen : Lean.NameSet := {}
  let mut localNames : Array Lean.Name := #[]
  let mut axiomNames : Lean.NameSet := {}
  while !pending.isEmpty do
    let name := pending.head!
    pending := pending.tail!
    if seen.contains name then continue
    seen := seen.insert name
    let some info := env.checked.get.find? name
      | throwError "Missing transitive checked declaration: {name}"
    if info.isUnsafe || info.isPartial then
      throwError "Unsafe or partial transitive declaration: {name}"
    if info.isAxiom then
      axiomNames := axiomNames.insert name
      unless [``propext, ``Classical.choice, ``Quot.sound].contains name do
        throwError "Additional transitive axiom: {name}"
    if name.toString.startsWith "Luce." || name.toString.startsWith "_private.Luce." then
      localNames := localNames.push name
    pending := info.type.getUsedConstants.toList ++ pending
    if let some value := info.value? true then
      pending := value.getUsedConstants.toList ++ pending
    if let .inductInfo value := info then
      pending := value.ctors ++ pending
  let localsSorted := localNames.qsort Lean.Name.lt
  Lean.logInfo m!"CHECKED_BODY_AUDIT: {seen.toArray.size} transitive declarations; {localsSorted.size} Luce declarations; no unsafe or partial declarations; no additional axioms."
  Lean.logInfo m!"CHECKED_BODY_AXIOMS: {axiomNames.toArray.qsort Lean.Name.lt}"
  for name in localsSorted do
    Lean.logInfo m!"CHECKED_LOCAL_DEPENDENCY: {name}"

