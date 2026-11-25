import OAI.Hierarchy.TaggedWideFundedLocalReturn
import OAI.Hierarchy.TaggedWideFundedPrivateCells
import OAI.Hierarchy.TaggedWideFundedPathCases
import OAI.Hierarchy.TaggedWideSelectedReturnRoom
import OAI.Hierarchy.TaggedWideParentFullCPUs

namespace OAI
/-! # The original paid CPU on a selected path of its installed zero-filled tape -/

noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage CoreBoard CoreRoute ReportSockets
open CatalystArchive StripChart CatalogueRows ColumnWires Tagged WireTelescope CalendarTape
open TaggedPrune TaggedShorterBudget TaggedShorterSupergroups Tagged.WideStack Filter
open ThreeFlat.RAM CoreBoard.PhysicalTerm
open scoped BigOperators Classical Fin.CommRing
set_option quotPrecheck false
set_option maxRecDepth 12288
set_option maxHeartbeats 6000000
set_option hygiene false
set_option cleanup.letToHave false
variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ κ A s : ℝ}
    (v : FixedProtocolFormat F k p q Q σ Λ) (m ell short : ℕ) (u : ℝ→ℝ) (δ ξ : ℝ) (unitCost : ℕ)

/-- The proposition furnished at a parent by a uniform cofinal estimate. -/
abbrev selectedParentFact {B : WideParent κ A → Prop} (_ : ∀ᶠ x in WideParent.large κ A,B x)
    (x : WideParent κ A) : Prop := B x

private def selectedFundingAt (rate : v.sharpPaidUnit ≤ unitCost) (x : WideParent κ A) : Prop :=
  selectedParentFact (v.cofinal_report_cut_rows (κ:=κ) (B:=A) unitCost rate) x

private def selectedPruningAt (rate : v.sharpPaidUnit ≤ unitCost) (x : WideParent κ A) : Prop :=
  selectedParentFact (v.wide_prune_prices (κ:=κ) (B:=A) unitCost rate) x

private def selectedPrivateRowsAt (rate : v.sharpPaidUnit ≤ unitCost) (x : WideParent κ A) : Prop :=
  selectedParentFact (v.cofinal_private_report_rows (κ:=κ) (B:=A) unitCost rate) x


structure SelectedReturnSupport (rate : v.sharpPaidUnit ≤ unitCost) (x : WideParent κ A) : Prop where
  size : v.SelectedReturnRoom x m ell short u δ ξ unitCost
  funding : selectedFundingAt v unitCost rate x
  pruning : selectedPruningAt v unitCost rate x
  privateRows : selectedPrivateRowsAt v unitCost rate x
  privateWord : v.widePrivateUnit unitCost*x.w<2^(Native.wordBits x.h (2^v.W) Native.copies)


private theorem collectSelectedSupport {α : Type} {l : Filter α} {size funded priced rows word support : α → Prop}
    (mkSupport : ∀ x, size x → funded x → priced x → rows x → word x → support x)
    (sizes : ∀ᶠ x in l, size x) (funds : ∀ᶠ x in l, funded x) (prices : ∀ᶠ x in l, priced x)
    (rowBounds : ∀ᶠ x in l, rows x) (wordBounds : ∀ᶠ x in l, word x) : ∀ᶠ x in l, support x := by
  filter_upwards [sizes,funds,prices,rowBounds,wordBounds] with x bounded paid quoted small fits
  exact mkSupport x bounded paid quoted small fits

section
attribute [local irreducible] Filter.Eventually

open Lean Meta Elab Tactic in
local elab "collectSelectedFacts " ids:ident,+ : tactic => do
  let goal ← getMainGoal
  goal.withContext do
    let target ← whnf (← goal.getType)
    unless target.isAppOf ``Filter.Eventually do throwError "expected cofinal support"
    let args := target.getAppArgs
    let space := args[0]!
    let family := args[1]!
    let pack ← withLocalDeclD `x space fun x => do
      let support ← whnf (mkApp family x)
      unless support.isAppOf ``SelectedReturnSupport do throwError "expected a selected return support record"
      let co := mkAppN (mkConst ``SelectedReturnSupport.mk support.getAppFn.constLevels!) support.getAppArgs
      mkLambdaFVars #[x] co
    let mut families := #[]
    let mut available := #[]
    for name in ids.getElems do
      let fact ← getFVarFromUserName name.getId
      let ty ← whnf (← inferType fact)
      unless ty.isAppOf ``Filter.Eventually do throwError "expected a cofinal parent estimate"
      families := families.push ty.getAppArgs[1]!
      available := available.push fact
    let proof := mkAppN (mkConst ``collectSelectedSupport) (#[space,args[2]!] ++ families ++ #[family,pack] ++ available)
    goal.assign proof
    replaceMainGoal []


theorem cofinal_selected_return_support (hu : TaggedWidthProfile.Admissible s u)
    (rate : v.sharpPaidUnit ≤ unitCost) :
    ∀ᶠ x : WideParent κ A in WideParent.large κ A,
      v.SelectedReturnSupport m ell short u δ ξ unitCost rate x := by
  let sized := v.cofinal_selected_return_room (κ:=κ) (A:=A) m ell short hu δ ξ unitCost
  let funded := v.cofinal_report_cut_rows (κ:=κ) (B:=A) unitCost rate
  let priced := v.wide_prune_prices (κ:=κ) (B:=A) unitCost rate
  let rowsBound := v.cofinal_private_report_rows (κ:=κ) (B:=A) unitCost rate
  let wordBound := v.cofinal_private_word_room (κ:=κ) (B:=A) unitCost
  collectSelectedFacts sized, funded, priced, rowsBound, wordBound


end

variable {N : ℕ} (x : WideParent κ A) (cpu : v.ParentFullCPUs m ell short u δ ξ unitCost N x)
    (rate : v.sharpPaidUnit≤unitCost) (support : v.SelectedReturnSupport m ell short u δ ξ unitCost rate x)
local notation "h" => x.h
local notation "width" => x.w
local notation "d" => 2^v.W
local notation "W" => Native.wordBits h d Native.copies
local notation "g" => v.wideDated h width ell unitCost
local notation "S" => v.wideInstalledSize x m ell unitCost g
local notation "Sfit" => (v.wide_installed_tape_bounds x m ell unitCost g).2.2
local notation "seed" => v.wideInstalledHeader x m ell short u δ ξ unitCost g
    (v.wide_dated_sites h width ell unitCost) (v.wide_dated_edges h width ell unitCost) (fun _=>0)
local notation "reader" => v.wideSelector h width cpu.age cpu.ready.credit cpu.ready.size_le
local notation "sl" => (reader).format.slot
local notation "es" => events v.mesh
local notation "menu" => (typeMenu κ A v.W m k v.wideJobs ell v.stage_positive (fun _=>short+ell)).menu u δ ξ
local notation "slots" => purchaseSlots h v.W k v.wideJobs ell
variable (prices : v.PhysicalCounts u A δ ξ m) {C : ℝ} (pricePos : 0≤κ)
    (buy : ∀t:Fin (m+1),Purchased F menu x t slots
      (purchaseCandidates h v.W k v.wideJobs slots ((menu).height t x) (purchaseModules v.W u δ ξ menu x t))
      (purchaseModules v.W u δ ξ menu x t) C)
    (groupsFit : GroupRoom v.W k v.wideJobs u δ ξ menu x)
    (metadata : ∀t:Fin (m+1),1+(menu).height t x+(menu).height t x≤(menu).payload t x)
    (lanesFit : v.wideInstalledCap unitCost≤2^ell)
variable {b : Fin k→ℕ} (external : OpenPins h width b → Bool) (π : Equiv.Perm (Tagged.Row h))
    (tag : (π : Tagged.Row h→Tagged.Row h)=Tagged.tag (fun i=>external (.inl i)))
local notation "base" => v.wideOrigin h width S seed π
variable (j : Path sl es base)
local notation "record" => CalendarTape.encode sl es base j
local notation "input" => (reader).format.windows.header es record seed
local notation "bill" => v.wide_reported_path_native h width S π seed cpu.age cpu.ready.credit cpu.ready.size_le
    Sfit support.size.late support.size.words j

local notation "cutAge" => Classical.choose bill
local notation "cutCost" => Classical.choose (Classical.choose_spec bill)
local notation "cutNames" => Classical.choose (Classical.choose_spec (Classical.choose_spec bill))
local notation "signedCut" => Classical.choose_spec (Classical.choose_spec (Classical.choose_spec bill))
open Lean Elab Term in
local elab "boundsNativeFrom " signed:term : term => do
  let proof ← elabTerm signed none
  let conj ← Meta.whnf (← Meta.inferType proof)
  let equality ← Meta.whnf conj.getAppArgs.back!
  let right := equality.getAppArgs.back!
  let payload := right.getAppArgs.back!
  unless right.isAppOf ``Sigma.mk do throwError "expected the packed report"
  let some entry := payload.find? (fun e => e.isAppOf ``signedPathNativeReport && !e.hasLooseBVars)
    | throwError "no closed signed report in packed payload {payload.getAppFn.constName?}"
  return Lean.mkAppN (Lean.mkConst ``wide_native_report entry.getAppFn.constLevels!) entry.getAppArgs

local notation "selectedNative" => boundsNativeFrom (signedCut)

/-- Every original ordinal fits the private plane in this very signed native
report, and the entire private plane fits one arithmetic word. -/
theorem wide_selected_private_bounds :
    (∀i,((selectedNative).rows i).width≤v.widePrivateUnit unitCost*width) ∧
      v.widePrivateUnit unitCost*width<2^W := by
  let boundedSource := selectedNative
  let signed := signedCut
  let accepted := signed.1
  run_tac
    let goal ← Lean.Elab.Tactic.getMainGoal
    goal.withContext do
      let target ← Lean.Meta.whnf (← Lean.instantiateMVars (← goal.getType))
      unless target.isAppOf ``And do throwError "expected a private width and word bound"
      let selected ← Lean.Meta.getFVarFromUserName `boundedSource
      let decl ← selected.fvarId!.getDecl
      let some entry := decl.value? true | throwError "the bounded source is not an issued report"
      unless entry.isAppOf ``wide_native_report && !entry.hasLooseBVars do
        throwError "expected a fully instantiated signed native report"
      let args := entry.getAppArgs
      let n := args.size
      let supportTerm ← Lean.Meta.getFVarFromUserName `support
      let supportType ← Lean.Meta.whnf (← Lean.Meta.inferType supportTerm)
      let supportArgs := supportType.getAppArgs.push supportTerm
      let capTerm := Lean.mkAppN (Lean.mkConst ``SelectedReturnSupport.privateRows supportType.getAppFn.constLevels!) supportArgs
      let wordTerm := Lean.mkAppN (Lean.mkConst ``SelectedReturnSupport.privateWord supportType.getAppFn.constLevels!) supportArgs
      let acceptedTerm ← Lean.Meta.getFVarFromUserName `accepted
      let proofTerm := Lean.mkAppN capTerm #[args[n-11]!,args[n-7]!,args[n-10]!,args[n-9]!,
        args[n-6]!,args[n-5]!,args[n-4]!,args[n-3]!,args[n-2]!,args[n-1]!,acceptedTerm]
      goal.assign (Lean.mkAppN (Lean.mkConst ``And.intro) (target.getAppArgs ++ #[proofTerm,wordTerm]))
      Lean.Elab.Tactic.replaceMainGoal []



run_cmd Lean.modifyEnv fun env => Lean.LibrarySuggestions.nameDenyListExt.addEntry env "wide_selected_private_bounds"

open Lean Elab Term in
local elab "selectedReportFrom " signed:ident : term => do
  let proof ← Meta.getFVarFromUserName signed.getId
  let conj ← Meta.whnf (← Meta.inferType proof)
  let equality ← Meta.whnf conj.getAppArgs.back!
  let right := equality.getAppArgs.back!
  let payload := right.getAppArgs.back!
  unless right.isAppOf ``Sigma.mk do throwError "expected the packed report"
  let some entry := payload.find? (fun e => e.isAppOf ``signedPathNativeReport && !e.hasLooseBVars)
    | throwError "no closed signed report in packed payload {payload.getAppFn.constName?}"
  return entry

open Lean Elab Term in
private def selectedReportArgs (native : TSyntax `ident) : TermElabM (Array Lean.Expr) := do
  let localReport ← Meta.getFVarFromUserName native.getId
  let some entry := (← Meta.getFVarLocalDecl localReport).value? true
    | throwError "expected a selected report let"
  unless entry.isAppOf ``signedPathNativeReport do
    throwError "unexpected report head {entry.getAppFn.constName?}"
  return entry.getAppArgs

open Lean Elab Term in
private def selectedSupportField (support : TSyntax `ident) (field : Name) : TermElabM Lean.Expr := do
  let supplied ← Meta.getFVarFromUserName support.getId
  let shape ← Meta.whnf (← Meta.inferType supplied)
  return mkAppN (mkConst field shape.getAppFn.constLevels!) (shape.getAppArgs.push supplied)

open Lean Elab Term in
local elab "selectedFundingProof " support:ident native:ident accepted:ident : term => do
  let a ← selectedReportArgs native
  let n := a.size
  let good ← Meta.getFVarFromUserName accepted.getId
  let fn ← selectedSupportField support ``SelectedReturnSupport.funding
  return mkAppN fn #[a[n-11]!,a[n-7]!,a[n-10]!,a[n-9]!,a[n-6]!,a[n-5]!,a[n-4]!,a[n-3]!,a[n-2]!,a[n-1]!,good]

open Lean Elab Term in
local elab "selectedPruningAtReport " native:ident : term => do
  let report ← Meta.getFVarFromUserName native.getId
  let typ ← Meta.whnf (← Meta.inferType report)
  unless typ.isAppOf ``CoreBoard.Report do throwError "expected report"
  let rows := mkAppN (Lean.mkConst ``CoreBoard.Report.rows typ.getAppFn.constLevels!) (typ.getAppArgs.push report)
  let a ← selectedReportArgs native
  return mkAppN (Lean.mkConst ``PrunePrices) ((a.extract 0 (a.size-11)).push rows)

open Lean Elab Term in
local elab "selectedPriceProof " support:ident native:ident accepted:ident cert:ident : term => do
  let a ← selectedReportArgs native
  let n := a.size
  let good ← Meta.getFVarFromUserName accepted.getId
  let receipt ← Meta.getFVarFromUserName cert.getId
  let actual ← Meta.whnf (← Meta.inferType receipt)
  unless actual.getAppFn.isConstOf ``Whole.Reconciliation do
    throwError "expected the funded run's reconciliation"
  let r := actual.getAppArgs
  let k := r.size
  let fn ← selectedSupportField support ``SelectedReturnSupport.pruning
  return mkAppN fn #[a[n-11]!,a[n-7]!,a[n-10]!,a[n-9]!,good,r[k-11]!,r[k-6]!,r[k-5]!,r[k-2]!,receipt]

open Lean Meta Elab Term in
local elab "genericFundedReconciliation" : term => do
  let fn ← mkConstWithFreshMVarLevels ``wide_funded_run_at
  forallTelescopeReducing (← inferType fn) fun xs body => do
    let ex ← whnf body
    unless ex.isAppOf ``Exists do throwError "expected an existential"
    let run := mkAppN fn xs
    let account := mkAppN (Lean.mkConst ``Classical.choose_spec ex.getAppFn.constLevels!) (ex.getAppArgs.push run)
    let both ← whnf (← inferType account)
    unless both.isAppOf ``And do throwError "expected reconciliation and execution"
    let receipt := mkAppN (Lean.mkConst ``And.left) (both.getAppArgs.push account)
    mkLambdaFVars xs receipt

private abbrev selectedLedgerReceipt := genericFundedReconciliation

open Lean Elab Term in
local elab "selectedReceipt " native:ident radius:term : term => do
  let a ← selectedReportArgs native
  let n := a.size
  let rad ← elabTerm radius (some (Lean.mkConst ``Nat))
  return mkAppN (Lean.mkConst ``selectedLedgerReceipt) ((a.extract 0 (n-11)) ++
    #[rad,a[n-10]!,a[n-9]!,a[n-8]!,a[n-11]!,a[n-7]!,a[n-6]!,a[n-5]!,a[n-4]!,a[n-2]!])

/- Use exactly the cost and the polymorphic name assignment recorded in the funded report. -/
open Lean Elab Term in
local elab "applyFundedSelection " operation:ident reportValue:ident fundingProof:ident : term => do
  let prefixFn ← Meta.getFVarFromUserName operation.getId
  let proof ← Meta.getFVarFromUserName fundingProof.getId
  let witnessType ← Meta.whnf (← Meta.inferType proof)
  unless witnessType.isAppOf ``Nonempty do throwError "expected funded cut rows"
  let actualCut := mkApp2 (Lean.mkConst ``Classical.choice witnessType.getAppFn.constLevels!) witnessType.appArg! proof
  let arguments ← selectedReportArgs reportValue
  return mkApp3 prefixFn arguments[arguments.size - 3]! arguments.back! actualCut

open Lean Elab Term in
local elab "pairFundedSelection " equality:ident observation:ident : term => do
  let equalFact ← Meta.getFVarFromUserName equality.getId
  let runFact ← Meta.getFVarFromUserName observation.getId
  return mkAppN (Lean.mkConst ``And.intro) #[← Meta.inferType equalFact, ← Meta.inferType runFact, equalFact, runFact]

/- The fixed-format parameters of the signed report and the two coefficients of its
wide parent are the original local machine parameters. Keep all remaining inputs
explicit, including the type of the external pins and the zero-filled memory. -/
open Lean Elab Term in
local elab "beginSelectedRun " reportValue:ident parentValue:ident " geometry " loss:ident scale:ident " using " exactInputs:term,+ : term => do
  let reportArgs ← selectedReportArgs reportValue
  let fixedArgs := reportArgs.extract 0 (reportArgs.size - 13)
  let parent ← Meta.getFVarFromUserName parentValue.getId
  let lossTerm ← Meta.getFVarFromUserName loss.getId
  let scaleTerm ← Meta.getFVarFromUserName scale.getId
  unless fixedArgs.size == 9 do throwError "expected the signed report's fixed format"
  let supplied ← exactInputs.getElems.mapM fun arg => elabTerm arg none
  unless supplied.size == 26 do throwError "expected the calendar, tape, dates and room through lanesFit"
  let fn ← Meta.mkConstWithFreshMVarLevels ``wide_funded_local_return
  return mkAppN fn (fixedArgs ++ #[lossTerm, scaleTerm, parent] ++ supplied)

/- Apply the remaining price, purchase and size proofs to the actual funded execution.
The full-gate room here is the same argument already stored in the execution prefix. -/
open Lean Elab Term in
local elab "completeSelectedRun " selected:ident prepared:ident support:ident "[" accounts:ident,* "]" : term => do
  let operation ← Meta.getFVarFromUserName selected.getId
  let prefixValue ← Meta.getFVarFromUserName prepared.getId
  let some earlier := (← Meta.getFVarLocalDecl prefixValue).value? true
    | throwError "expected the selected funded execution prefix"
  unless earlier.isAppOf ``wide_funded_local_return && earlier.getAppNumArgs == 38 do
    throwError "expected the mounted funded execution through its lane bound"
  let inputs ← accounts.getElems.mapM fun account => Meta.getFVarFromUserName account.getId
  unless inputs.size == 7 do throwError "expected prices, bound, purchase and pruning proofs"
  let limits ← selectedSupportField support ``SelectedReturnSupport.size
  let shape ← Meta.whnf (← Meta.inferType limits)
  unless shape.isAppOf ``SelectedReturnRoom do throwError "expected the selected return bounds"
  let field (name : Name) := mkAppN (Lean.mkConst name shape.getAppFn.constLevels!) (shape.getAppArgs.push limits)
  let spill := mkApp (field ``SelectedReturnRoom.spill) earlier.getAppArgs[31]!
  return mkAppN operation (inputs ++ #[spill, field ``SelectedReturnRoom.spillAge,
    field ``SelectedReturnRoom.paidAge, field ``SelectedReturnRoom.spillBallotAge,
    field ``SelectedReturnRoom.widthFloor])

open Lean Elab Term in
local elab "inferSelectedReturn% " body:term : term => elabTerm body none

set_option maxHeartbeats 36000000 in
/-- The returned proof pairs equality of the full path report with the native
counted archive, local sheet execution, retained fields, prune bit, and spill readouts. -/
abbrev wide_selected_local_return := inferSelectedReturn%
  let signed := signedCut
  let _native := selectedReportFrom signed
  let _accepted := signed.1
  let _funding := selectedFundingProof support _native _accepted
  let _certificate := selectedReceipt _native v.radius
  have _priced : selectedPruningAtReport _native := selectedPriceProof support _native _accepted _certificate
  have found : ∃! z : Path sl es base, CalendarTape.encode sl es base z=record :=
    ⟨j,rfl,fun _ eqn=>(CalendarTape.encode sl es base).injective eqn⟩
  have tagRead : ∀i,WordSlots.exposed (wideTagPin h width b) external i=π i :=
    fun i=>(congrFun tag i).symm
  let _preparedLocal := beginSelectedRun _native x geometry κ A using m, ell, short, u, δ, ξ, unitCost,
    (fun _ : ℕ => (0 : Word W)), cpu.age, cpu.ready.credit, cpu.ready.size_le, cpu.ready,
    (TaggedPrune.OpenPins h width b), (wideTagPin h width b), external, record, π, tagRead,
    found, cpu.room, cpu.scratch, support.size.operandAge, support.size.activeAge, support.size.ballotAge,
    support.size.large, lanesFit
  let _selectedLocal := applyFundedSelection _preparedLocal _native _funding
  let _resultLocal := completeSelectedRun _selectedLocal _preparedLocal support [prices, C, pricePos, buy, groupsFit, metadata, _priced]
  let _geometryAgreement := signed.2
  pairFundedSelection _geometryAgreement _resultLocal

run_cmd Lean.modifyEnv fun env => Lean.LibrarySuggestions.nameDenyListExt.addEntry env "wide_selected_local_return"

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
