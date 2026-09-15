import Luce.Sections1To7
import Luce.Section4RankIntegralDependencyAudit
import Lean.Util.CollectAxioms

/- Independent audit of every declaration originating in a production module.
   Includes checked types and bodies, and traverses transitive definitions. -/
set_option pp.explicit true
set_option pp.universes true
set_option pp.fullNames true
set_option pp.proofs false

set_option maxHeartbeats 0 in
run_elab do
  let env ← Lean.getEnv
  let mut roots : Array Lean.Name := #[]
  let mut proofRoots : Array Lean.Name := #[]
  let mut executableOnly : Array Lean.Name := #[]
  for (name, info) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? name then
      let modName := env.header.moduleNames[idx]!
      if modName == `Luce || modName.toString.startsWith "Luce." then
        if info.isUnsafe || info.isPartial then
          executableOnly := executableOnly.push name
        else
          roots := roots.push name
        if info.isTheorem || info.isAxiom then
          proofRoots := proofRoots.push name
  -- Lean generates unsafe executable companions for some safe recursive
  -- definitions. They are not logical roots. The traversal below still rejects
  -- ANY unsafe/partial declaration reached from a safe definition or theorem.
  for name in executableOnly.qsort Lean.Name.lt do
    Lean.logInfo m!"REVIEW_EXECUTABLE_COMPANION: {name}"
  let mainNames : List Lean.Name := [``section4_contractCheck, ``section5_contractCheck,
    ``Luce.Section6.powerLaw65, ``Luce.Section6.spatial65, ``Luce.Section6.critical,
    ``Luce.Section6.section6, ``Luce.Section6.lemma612, ``Luce.Section7.proposition71]
  for name in mainNames do
    let some info := env.checked.get.find? name
      | throwError "Missing checked main theorem: {name}"
    unless info.isTheorem do
      throwError "Main result is not a theorem: {name}"
    Lean.logInfo m!"STATEMENT {name} : {info.type}"
    Lean.logInfo m!"AXIOMS {name}: {← Lean.collectAxioms name}"
  let mut pending := roots.toList
  let mut seen : Lean.NameSet := {}
  let mut axiomNames : Lean.NameSet := {}
  let mut visitedCount : Nat := 0
  while !pending.isEmpty do
    let name := pending.head!
    pending := pending.tail!
    if seen.contains name then continue
    seen := seen.insert name
    visitedCount := visitedCount + 1
    if visitedCount % 10000 == 0 then
      IO.println s!"REVIEW_PROGRESS: visited {visitedCount} declarations"
    let some info := env.checked.get.find? name
      | throwError "Missing checked transitive declaration: {name}"
    if info.isUnsafe || info.isPartial then
      throwError "Unsafe or partial dependency: {name}"
    if info.isAxiom then
      axiomNames := axiomNames.insert name
      unless [``propext, ``Classical.choice, ``Quot.sound].contains name do
        throwError "Nonstandard axiom: {name}"
    pending := info.type.getUsedConstants.toList ++ pending
    if let some value := info.value? true then
      pending := value.getUsedConstants.toList ++ pending
    if let .inductInfo value := info then
      pending := value.ctors ++ pending
  Lean.logInfo m!"REVIEW_PRODUCTION_DECLARATIONS: {roots.size + executableOnly.size}"
  Lean.logInfo m!"REVIEW_SAFE_PRODUCTION_ROOTS: {roots.size}"
  Lean.logInfo m!"REVIEW_EXECUTABLE_COMPANION_COUNT: {executableOnly.size}"
  Lean.logInfo m!"REVIEW_THEOREM_AXIOM_CONSTANTS: {proofRoots.size}"
  Lean.logInfo m!"REVIEW_TRANSITIVE_CHECKED_DECLARATIONS: {seen.toArray.size}"
  Lean.logInfo m!"REVIEW_AXIOM_UNION: {axiomNames.toArray.qsort Lean.Name.lt}"
  Lean.logInfo "REVIEW_PASSED: every safe production definition and theorem has checked dependencies; no nonstandard axiom, unsafe dependency, or partial dependency"
