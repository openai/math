import Lake
import Lake.Build.Library

open System Lake DSL

package OAI where
  version := v!"0.1.0"
  fixedToolchain := true
  leanOptions := #[⟨`autoImplicit, false⟩]

require «fixed-point-theorems» from git
  "https://github.com/harfe/fixed-point-theorems-lean4.git" @ "770940ddf9878cf61952ed53d910b92bca841838"
require Zeta3Irrational from git
  "https://github.com/ahhwuhu/zeta_3_irrational.git" @ "e8785315a01c8fbcddaa0fc03b3c8b29a61bc1f1"
require «rellich-kondrachov» from git
  "https://github.com/abenenson/rellich-kondrachov.git" @ "70f85d4c1bf99c6e7d61e8be4daa6f3664d08d23"
require carleson from git
  "https://github.com/fpvandoorn/carleson.git" @ "306ae5b29300771aece1aa39f0a939183cc59486"
require StrongPNT from git
  "https://github.com/math-inc/strongpnt.git" @ "2f5835c322314f55f1026ec2f139d704b7c45c69"
require AbsorptionCutoff from git
  "https://github.com/BennyAvelin/AbsorptionCutoff.git" @ "41c45c6d72e979419e46224bb7b4be5cee31f2b5"
require AINTLIB from git
  "https://github.com/CBirkbeck/AINTLIB.git" @ "160e446617a2168c34c95bbe7a76c4105b392434"
require ClassFieldTheory from git
  "https://github.com/n-yamaguchi-0729/ClassFieldTheory.git" @ "2eb22d6485af45f29c5219de6c49f196a61c4f49"
require «schoenflies-lean» from git
  "https://github.com/alonamaloh/schoenflies-lean" @ "05a43d29cde026618777db3d4e4316204ccca237"

require SphereEversion from git
  "https://github.com/leanprover-community/sphere-eversion.git" @ "9c53f91e2a281199163ecea04dc4976cb79e2076"

require TauCeti from git
  "https://github.com/TauCetiProject/TauCeti.git" @ "3bed7e37f3c504a99e8c07e9f309540812a7aa90"

require gromov from git
  "https://github.com/Aaron1011/gromov.git" @ "8db79f13cf211b570e3116301d91379fbc01cf3e"

require «iut» from git
  "https://github.com/lana-agents/iut.git" @ "d9465c111ec4073709f67e9fccec7e3eb374a816"

require «tate-curves-theta» from git
  "https://github.com/lana-agents/tate-curves-theta.git" @ "ca6c2279d3cea0690cdb01328e727118d5485d68"

require «genl» from git
  "https://github.com/lana-agents/genl.git" @ "ea2846c877d1e16d8f0b911a5fed07f5ee69eaaf"

require «heights» from git
  "https://github.com/lana-agents/heights.git" @ "721496ca4c158e511d25d8ccf6bfe8503eda73c1"

require «pi1» from git
  "https://github.com/lana-agents/pi1.git" @ "ca7def953193f861a462aa0831eec8f0a31ff69f"

require «orbicurve-cores» from git
  "https://github.com/lana-agents/orbicurve-cores.git" @ "61616dcd77fbe45c083a8ebfa7cc80728f86e841"

require «oka» from git
  "https://github.com/lana-agents/oka.git" @ "75dcdc3faadd10b986afb9283e89902bcdddecd4"

require «tempered-fundamental-groups» from git
  "https://github.com/lana-agents/tempered-fundamental-groups.git" @ "2006651f52b70ea2fe3388238c7d9db14d21748f"

require «elliptic-curves» from git
  "https://github.com/lana-agents/elliptic-curves.git" @ "bebec3fc9f2602e81c83e5236789572a541c85fb"

require «formal-schemes» from git
  "https://github.com/lana-agents/formal-schemes.git" @ "51aa935079537bf4dc580751a6e70727fb23ca93"

require «belyi» from git
  "https://github.com/lana-agents/belyi.git" @ "9ce4d3f793d3bc831f2fc7214b7dbad90ea012d8"

require complexitylib from git
  "https://github.com/cslib-community/complexitylib.git" @ "242879e6913ca3b29005f7c48536896983d2ad2f"
require cslib from git
  "https://github.com/leanprover/cslib" @ "254e30e6d4299c51323aaeaf5f51a4763b375d4a"
require lemmata from git
  "https://github.com/ZIB-IOL/lemmata.git" @ "a2dd430f283febd755a6ee6932d0b0fdabfb330c" / "lean"

require HexBareiss from git
  "https://github.com/leanprover/hex-bareiss.git" @ "fea7d537c14531b3a699530f5c7776f69f0ed9a9"

require HexLLLMathlib from git
  "https://github.com/leanprover/hex-lll-theory.git" @ "761108380d7bdae23181785d52703b4883388da1"

-- Declare shared dependencies last: Lake resolves later requirements first.
-- These pins override the older versions in the upstream packages' manifests.
require PrimeNumberTheoremAnd from git
  "https://github.com/AlexKontorovich/PrimeNumberTheoremAnd.git" @ "c39a751132c88b6e8080b74c74023fd95b3d8be0"
require leancert from git
  "https://github.com/alerad/leancert.git" @ "7f91b6eb3567437f6cfac03ed279706603ee22f4"
require LeanArchitect from git
  "https://github.com/hanwenzhu/LeanArchitect.git" @ "468e8f58fb4ad6e6ad672a08da6d0d0531e95a97"
require PrimeCert from git
  "https://github.com/b-mehta/PrimeCert.git" @ "0803c2f6bd289c09704c7d352bb8fcf770cbb9b2"
require «doc-gen4» from git
  "https://github.com/leanprover/doc-gen4.git" @ "953c8992d174b4e56955e01e101d46668c68f2bb"
require checkdecls from git
  "https://github.com/PatrickMassot/checkdecls.git" @ "3d425859e73fcfbef85b9638c2a91708ef4a22d4"
require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "d13f23b723b8a846827a245b89c10fc7d3f11612"

@[default_target] lean_lib OAI

lean_lib OAI.HyperbolicObstruction where globs := #[`OAI.HyperbolicObstruction.+]
lean_lib OAI.Hierarchy where globs := #[`OAI.Hierarchy.+]
lean_lib OAI.ThreeFlat where globs := #[`OAI.ThreeFlat.+]

lean_lib OAI.Analysis where
  roots := #[`OAI.Analysis]
  globs := #[`OAI.Analysis.+]
lean_lib OAI.Algebra where
  roots := #[`OAI.Algebra]
  globs := #[`OAI.Algebra.+]
lean_lib OAI.AlgebraicGeometry where
  roots := #[`OAI.AlgebraicGeometry]
  globs := #[`OAI.AlgebraicGeometry.+]
lean_lib OAI.AlgebraicTopology where
  roots := #[`OAI.AlgebraicTopology]
  globs := #[`OAI.AlgebraicTopology.+]
lean_lib OAI.Geometry where
  roots := #[`OAI.Geometry]
  globs := #[`OAI.Geometry.+]
lean_lib OAI.Probability where
  roots := #[`OAI.Probability]
  globs := #[`OAI.Probability.+]
lean_lib OAI.Combinatorics where
  roots := #[`OAI.Combinatorics]
  globs := #[`OAI.Combinatorics.+]
-- Keep the preserved challenge sources under their original HodgeConjecture module names.
lean_lib HodgeConjecture where
  srcDir := "ComparatorChallenges/HodgeConjectureCMAbelianVarieties"
  globs := #[.submodules `HodgeConjecture]

-- Preserve the helper modules' original names when enumerating ComparatorChallenges.
@[«library_facet»] def comparatorSourceModules : LibraryFacetDecl :=
  .mk LeanLib.modulesFacet <|
    mkFacetJobConfig (buildable := false) fun (lib : LeanLib) => do
      let some builtin := initLibraryFacetConfigs.get? LeanLib.modulesFacet
        | error "Missing built-in library module collector"
      if lib.pkg.baseName != `OAI || lib.name != `ComparatorChallenges then
        return ← builtin.run lib
      let modules ← lib.getModuleArray
      let globs := modules.filterMap fun mod =>
        if (`ComparatorChallenges.HodgeConjectureCMAbelianVarieties.HodgeConjecture).isPrefixOf mod.name then
          none
        else
          some (Glob.one mod.name)
      let ordinary : LeanLib := { lib with config := { lib.config with globs } }
      let ordinaryModules ← (← builtin.run ordinary).await
      let some helpers := lib.pkg.findLeanLib? `HodgeConjecture
        | error "Missing HodgeConjecture source-root configuration"
      let helperModules ← (← builtin.run helpers).await
      return Job.pure (ordinaryModules ++ helperModules)

lean_lib ComparatorChallenges where globs := #[`ComparatorChallenges.+]
lean_lib OAI.InformationTheory where
  roots := #[`OAI.InformationTheory]
  globs := #[`OAI.InformationTheory.+]
lean_lib OAI.ModelTheory where
  roots := #[`OAI.ModelTheory]
  globs := #[`OAI.ModelTheory.+]
lean_lib OAI.RepresentationTheory where
  roots := #[`OAI.RepresentationTheory]
  globs := #[`OAI.RepresentationTheory.+]
lean_lib OAI.NumberTheory where
  roots := #[`OAI.NumberTheory]
  globs := #[`OAI.NumberTheory.+]
lean_lib OAI.MeasureTheory where
  roots := #[`OAI.MeasureTheory]
  globs := #[`OAI.MeasureTheory.+]
lean_lib OAI.GroupTheory where
  roots := #[`OAI.GroupTheory]
  globs := #[`OAI.GroupTheory.+]
lean_lib OAI.LinearAlgebra where
  roots := #[`OAI.LinearAlgebra]
  globs := #[`OAI.LinearAlgebra.+]
lean_lib OAI.RingTheory where
  roots := #[`OAI.RingTheory]
  globs := #[`OAI.RingTheory.+]
lean_lib OAI.Computability where
  roots := #[`OAI.Computability]
  globs := #[`OAI.Computability.+]
lean_lib OAI.Dynamics where
  roots := #[`OAI.Dynamics]
  globs := #[`OAI.Dynamics.+]
lean_lib OAI.CategoryTheory where
  roots := #[`OAI.CategoryTheory]
  globs := #[`OAI.CategoryTheory.+]
lean_lib OAI.MathematicalPhysics where
  roots := #[`OAI.MathematicalPhysics]
  globs := #[`OAI.MathematicalPhysics.+]
lean_lib OAI.Topology where
  roots := #[`OAI.Topology]
  globs := #[`OAI.Topology.+]
lean_lib OAI.Optimization where
  roots := #[`OAI.Optimization]
  globs := #[`OAI.Optimization.+]
lean_lib OAI.GameTheory where
  roots := #[`OAI.GameTheory]
  globs := #[`OAI.GameTheory.+]
lean_lib OAI.SetTheory where
  roots := #[`OAI.SetTheory]
  globs := #[`OAI.SetTheory.+]

private def preResolutionPatchNames : Array Lean.Name := #[
  `iut, `«tate-curves-theta», `genl, `heights, `pi1, `«orbicurve-cores», `oka,
  `«tempered-fundamental-groups», `«elliptic-curves», `«formal-schemes», `belyi
]

private def patchGit (directory : FilePath) (args : Array String) : IO IO.Process.Output :=
  IO.Process.output { cmd := "git", args := #["-C", directory.toString] ++ args }

private def checkPatch (directory patch : FilePath) (args : Array String := #[]) :
    IO IO.Process.Output :=
  patchGit directory (#["apply", "--check"] ++ args ++ #[patch.toString])

private inductive PatchState where
  | absent
  | applied
  | needsApply

private structure PatchPlan where
  label : String
  directory : FilePath
  patch : FilePath
  url : String
  revision : String
  state : PatchState

private def planDependencyPatch (root : FilePath) (dependency : Dependency) : IO PatchPlan := do
  let label := dependency.dirName
  let some (.git url (some revision) none) := dependency.src?
    | throw <| IO.userError s!"{label}: compatibility patches require a Git dependency pinned to a commit."
  unless revision.length == 40 && revision.toList.all (fun c =>
      c.isDigit || ('a' <= c && c <= 'f')) do
    throw <| IO.userError s!"{label}: expected a full lowercase Git commit, got {revision}."
  let patch := root / "patches" / s!"{label}-lean4341.patch"
  unless ← patch.pathExists do
    throw <| IO.userError s!"Missing compatibility patch: {patch}"
  let directory := root / ".lake" / "packages" / label
  let plan := { label, directory, patch, url, revision, state := .absent : PatchPlan }
  unless ← directory.pathExists do
    return plan
  let head ← patchGit directory #["rev-parse", "HEAD"]
  unless head.exitCode == 0 && head.stdout.trimAscii.toString == revision do
    throw <| IO.userError s!"{label}: expected commit {revision}, got {head.stdout}\n{head.stderr}"
  let origin ← patchGit directory #["remote", "get-url", "origin"]
  unless origin.exitCode == 0 && origin.stdout.trimAscii.toString == url do
    throw <| IO.userError s!"{label}: expected origin {url}, got {origin.stdout}\n{origin.stderr}"
  let reverse ← checkPatch directory patch #["--reverse"]
  if reverse.exitCode == 0 then
    return {plan with state := .applied}
  let forward ← checkPatch directory patch
  if forward.exitCode == 0 then
    return {plan with state := .needsApply}
  throw <| IO.userError s!"{label}: compatibility patch conflicts with local changes.\n\
    Forward check:\n{forward.stderr}\nReverse check:\n{reverse.stderr}"

private def applyDependencyPatch (plan : PatchPlan) (directory : FilePath) : IO Unit := do
  let applied ← patchGit directory #["apply", plan.patch.toString]
  unless applied.exitCode == 0 do
    throw <| IO.userError s!"{plan.label}: failed to apply compatibility patch:\n{applied.stderr}"
  let verified ← checkPatch directory plan.patch #["--reverse"]
  unless verified.exitCode == 0 do
    throw <| IO.userError s!"{plan.label}: patch verification failed:\n{verified.stderr}"

/-- Prepare patched package configurations before Lake resolves their dependencies. -/
private def preparePatchedDependencies (root : FilePath) (dependencies : Array Dependency) :
    IO (Array String) := do
  -- Check all existing checkouts before changing any of them.
  let plans ← dependencies.mapM (planDependencyPatch root)
  let mut changed := #[]
  for plan in plans do
    match plan.state with
    | .applied => pure ()
    | .needsApply =>
      applyDependencyPatch plan plan.directory
      changed := changed.push plan.label
    | .absent =>
      let packages := root / ".lake" / "packages"
      IO.FS.createDirAll packages
      let pid ← IO.Process.getPID
      let stamp ← IO.monoNanosNow
      let staging := packages / s!".{plan.label}-bootstrap-{pid}-{stamp}"
      IO.FS.createDir staging
      try
        let cloned ← IO.Process.output {
          cmd := "git", args := #["clone", "--no-checkout", plan.url, staging.toString]
        }
        unless cloned.exitCode == 0 do
          throw <| IO.userError s!"{plan.label}: clone failed:\n{cloned.stderr}"
        let checkedOut ← patchGit staging #["checkout", "--detach", plan.revision]
        unless checkedOut.exitCode == 0 do
          throw <| IO.userError s!"{plan.label}: checkout failed:\n{checkedOut.stderr}"
        let head ← patchGit staging #["rev-parse", "HEAD"]
        unless head.exitCode == 0 && head.stdout.trimAscii.toString == plan.revision do
          throw <| IO.userError s!"{plan.label}: cloned checkout has the wrong commit."
        applyDependencyPatch plan staging
        IO.FS.rename staging plan.directory
        changed := changed.push plan.label
      finally
        if ← staging.pathExists then
          IO.FS.removeDirAll staging
  return changed

-- Configuration elaboration precedes dependency resolution, unlike `post_update`.
run_cmd do
  let env ← Lean.getEnv
  if let some root := Lake.dirExt.getState env then
    let options ← Lean.getOptions
    let changed ← Lean.Elab.Command.liftIO do
      let declarations ← IO.ofExcept <| Lake.packageDepAttr.getAllEntries env |>.mapM fun name =>
        unsafe env.evalConstCheck Dependency options ``Dependency name
      let mut dependencies := #[]
      for name in preResolutionPatchNames do
        let some dependency := declarations.find? (·.name == name)
          | throw <| IO.userError s!"Missing direct dependency declaration for {name}."
        dependencies := dependencies.push dependency
      preparePatchedDependencies root dependencies
    for label in changed do
      Lean.logInfo s!"{label}: applied compatibility patch before dependency resolution"

post_update pkg do
  for name in preResolutionPatchNames do
    let label := name.toString (escape := false)
    let some dependency ← findPackageByName? name
      | error s!"Missing dependency {label} after Lake update."
    let some declaration := pkg.depConfigs.find? (·.name == name)
      | error s!"Missing direct dependency declaration for {label}."
    let plan ← planDependencyPatch pkg.dir declaration
    unless plan.directory == dependency.dir do
      error s!"{label}: Lake resolved an unexpected checkout at {dependency.dir}."
    match plan.state with
    | .applied => logInfo s!"{label}: compatibility patch verified after dependency resolution"
    | _ => error s!"{label}: compatibility patch was lost during dependency resolution."

  -- Preflight every dependency before changing any of them.
  let mut plans := #[]
  for name in #[`complexitylib, `cslib, `lemmata, `HexBareiss, `«fixed-point-theorems»,
      `PrimeNumberTheoremAnd, `Zeta3Irrational,
      `«rellich-kondrachov», `carleson, `StrongPNT, `AbsorptionCutoff, `AINTLIB,
      `ClassFieldTheory, `«schoenflies-lean», `SphereEversion, `gromov] do
    let label := name.toString (escape := false)
    let some dep ← findPackageByName? name
      | error s!"Missing dependency {label}; run lake update from the project root."
    let some declaration := pkg.depConfigs.find? (·.name == name)
      | error s!"Missing direct dependency declaration for {label}."
    let some (.git _ (some revision) _) := declaration.src?
      | error s!"{label} must be pinned to a Git commit."
    let patchDirectory := if name == `lemmata then dep.dir / ".." else dep.dir
    let head ← patchGit patchDirectory #["rev-parse", "HEAD"]
    unless head.exitCode == 0 && head.stdout.trimAscii.toString == revision do
      error s!"{label}: expected commit {revision}, got {head.stdout}\n{head.stderr}"
    let patchNames := #[s!"{label}-lean4341.patch"]
    for patchName in patchNames do
      let patch := pkg.dir / "patches" / FilePath.mk patchName
      unless ← patch.pathExists do
        error s!"Missing compatibility patch: {patch}"
      let reverse ← checkPatch patchDirectory patch #["--reverse"]
      if reverse.exitCode == 0 then
        plans := plans.push (label, patchDirectory, patch, none)
        continue
      let forward ← checkPatch patchDirectory patch
      if forward.exitCode == 0 then
        plans := plans.push (label, patchDirectory, patch, some patch)
        continue
      error s!"{label}: compatibility patch {patch} conflicts with local changes.\n\
        Forward check:\n{forward.stderr}\nReverse check:\n{reverse.stderr}"
  for (label, directory, patch, action) in plans do
    let patchName := patch.fileName.getD patch.toString
    if let some toApply := action then
      let result ← patchGit directory #["apply", toApply.toString]
      unless result.exitCode == 0 do
        error s!"{label}: failed to apply {toApply}:\n{result.stderr}"
      let verified ← checkPatch directory patch #["--reverse"]
      unless verified.exitCode == 0 do
        error s!"{label}: patch verification failed:\n{verified.stderr}"
      logInfo s!"{label}: applied compatibility patch {patchName}"
    else
      logInfo s!"{label}: compatibility patch already applied: {patchName}"
