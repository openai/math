import OAI.Hierarchy.TaggedWideFundedSelectedReturn
import OAI.Hierarchy.ProbeFixedWideSpillBallotObservation
import OAI.Hierarchy.WidthSelectedSpillRegisters

namespace OAI
/-! # The funded spill registers, original role bank and ROM on the selected return -/
noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage CoreBoard CoreRoute ReportSockets
open TaggedPrune CatalystArchive CatalogueRows Tagged WireTelescope CalendarTape TaggedShorterBudget TaggedShorterSupergroups
open Tagged.WideStack Filter ThreeFlat.RAM CoreBoard.PhysicalTerm
open scoped Classical BigOperators Fin.CommRing
set_option quotPrecheck false
set_option hygiene false
set_option maxRecDepth 12288
set_option maxHeartbeats 1600000
set_option cleanup.letToHave false
set_option Elab.async false
open CoreBoard.HistoryRoles ReportSockets in
private theorem moveLiteralRoleField {h W k jobs N native T : ℕ}
    (model : WideCPU.Dated T) (work : ℕ) (sampler : PurchaseSampler) (perm : Equiv.Perm (Fin (2^h)))
    (depth : ℕ) (marks : Marks h W k jobs) (exclusive : Exclusive marks) (names : Fin N ≃ Source sampler perm depth marks)
    (qty ids : Fin N → ℕ)
    (volume : model.roleWords = (siteLast h (2^W) k+1) * HistoryRoles.stride k sampler.degree jobs)
    (date : Fin (T+1)) (field : Fin 3) (earlier output : Memory native)
    (low : ∀ i, i < model.rolesEnd work → output i = earlier i)
    (archived : DatedRoleSheets.roleFact model.physical sampler perm depth marks exclusive names
      (model.roleStart work date) qty ids earlier field) :
    DatedRoleSheets.roleFact model.physical sampler perm depth marks exclusive names
      (model.roleStart work date) qty ids output field := by
  apply model.roleFact_local 0 work sampler perm depth marks exclusive names (fun _ => qty) ids volume
    date field earlier output _ archived
  intro i _ hi
  have upper := (WideCPU.role_order model 0 work).upper (finProdFinEquiv (date,field))
  simp only [Equiv.symm_apply_apply] at upper
  exact low i (hi.trans_le upper)

open CoreBoard.HistoryRoles in
open Lean Elab Term in
local elab "afterLiteralDateFields " archived:ident output:ident retained:ident : term => do
  let source ← Meta.getFVarFromUserName archived.getId
  let target ← Meta.getFVarFromUserName output.getId
  let low ← Meta.getFVarFromUserName retained.getId
  Meta.forallBoundedTelescope (← Meta.inferType source) (some 2) fun binders _ => do
    unless binders.size == 2 do throwError "expected the selected date and role field"
    let archivedField := mkAppN source binders
    let typ := (← instantiateMVars (← Meta.inferType archivedField)).consumeMData
    unless typ.isAppOfArity ``DatedRoleSheets.roleFact 18 do
      throwError "expected the original literal role field, found {typ.getAppFn} with {typ.getAppNumArgs} arguments"
    let args := typ.getAppArgs
    let start := args[13]!.consumeMData
    unless start.isAppOfArity ``WideCPU.Dated.roleStart 4 do
      throwError "expected the physical role bank of the source date"
    let bank := start.getAppArgs
    let words ← Meta.mkAppM ``WideCPU.Dated.roleWords #[bank[1]!]
    let volume ← Meta.mkEqRefl words
    let direct := args.extract 1 7 ++ #[bank[0]!, bank[1]!, bank[2]!] ++ args.extract 7 13 ++
      #[args[14]!, args[15]!, volume, binders[0]!, binders[1]!, args[16]!, target, low, archivedField]
    Meta.mkLambdaFVars binders (mkAppN (mkConst ``moveLiteralRoleField) direct)


variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ κ A : ℝ}
    (v : FixedProtocolFormat F k p q Q σ Λ) (m ell short : ℕ) (u : ℝ→ℝ) (δ ξ : ℝ) (unitCost : ℕ)
    {N : ℕ} (x : WideParent κ A) (cpu : v.ParentFullCPUs m ell short u δ ξ unitCost N x)
    (rate : v.sharpPaidUnit≤unitCost) (support : v.SelectedReturnSupport m ell short u δ ξ unitCost rate x)
local notation "h" => x.h
local notation "width" => x.w
local notation "d" => 2^v.W
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
variable {b : Fin k→ℕ} (e : OpenPins h width b→Bool) (perm : Equiv.Perm (Tagged.Row h))
    (tag : (perm : Tagged.Row h→Tagged.Row h)=Tagged.tag (fun i=>e (.inl i)))
local notation "base" => v.wideOrigin h width S seed perm
variable (j : Path sl es base)
local notation "report" => v.wide_reported_path h width S perm seed cpu.age cpu.ready.credit cpu.ready.size_le
    Sfit support.size.late support.size.words j

local notation "lay" => v.wideInstalledLayout x m ell short u δ ξ unitCost g
local notation "first" => (lay).pruneScratch+(lay).pruneRows+1
local notation "rootROM" => v.wideInstalledRoot x
local notation "top" => (v.privateArena (v.widePlacement h width) h width).endAddress v.mesh
local notation "rankEnd" => v.wideSpillRankEnd h width v.maxBits first

open Lean Elab Term in
local elab "exactPurchasedReturn%" : term => do
  let format ← Meta.getFVarFromUserName `v
  let formType := (← Meta.inferType format).consumeMData
  unless formType.isAppOfArity ``FixedProtocolFormat 8 do throwError "expected the original fixed protocol"
  let shape := formType.getAppArgs
  let decl ← getConstInfo ``wide_selected_local_return
  let mut tp := decl.type
  let mut actual := #[]
  while tp.isForall do
    let name := tp.bindingName!.eraseMacroScopes
    let localName := if name == `external then `e else if name == `π then `perm else name
    let arg ← if tp.bindingInfo! == .instImplicit then pure shape[1]! else Meta.getFVarFromUserName localName
    actual := actual.push arg
    tp := tp.bindingBody!
  return mkAppN (mkConst ``wide_selected_local_return (decl.levelParams.map Level.param)) actual


/- Carry the actual proposition of each chosen intermediate memory through the return. -/
open Lean Elab Term in
local elab "ballotReceipt " input:ident " along " "[" steps:ident,* "]" : term => do
  let mut fact ← Meta.getFVarFromUserName input.getId
  for step in steps.getElems do
    let key := step.getId
    if key == `left || key == `right then
      fact := .proj ``And (if key == `left then 0 else 1) fact
    else
      unless key == `memory || key == `evidence do throwErrorAt step "unknown receipt field"
      let shape ← Meta.whnf (← Meta.inferType fact)
      unless shape.isAppOfArity ``Exists 2 do throwErrorAt step "expected a returned existential"
      let next := if key == `memory then ``Exists.choose else ``Exists.choose_spec
      fact := mkAppN (mkConst next shape.getAppFn.constLevels!) (shape.getAppArgs.push fact)
  return fact


open Lean Elab Term in
local elab "selectedSpillResult% " body:term : term => elabTerm body none

open Lean Elab Term in
local elab "spillOperandProofs " "[" names:ident,* "]" : term => do
  let operands ← names.getElems.mapM fun u => Meta.getFVarFromUserName u.getId
  let mut proof := operands.back!
  let mut claim ← Meta.inferType proof
  for entry in operands.pop.reverse do
    let prop ← Meta.inferType entry
    proof := mkAppN (mkConst ``And.intro) #[prop, claim, entry, proof]
    claim := mkApp2 (mkConst ``And) prop claim
  return proof

section
local notation "wordBits₀" => Native.wordBits h d Native.copies
local notation "terminalFrame" => v.wideTerminalPreimage x g
  (v.wide_dated_sites h width ell unitCost) (v.wide_dated_edges h width ell unitCost) (fun _=>0)
variable (pruned prior ranked checked : Memory wordBits₀)
    (captured : ProcessingArchive top rootROM ((g).romEnd rootROM) checked terminalFrame pruned)
    (fromRank : ∀n, n < first → ranked n = pruned n)
    (fromPrune : ∀n, n < (lay).floor → pruned n = prior n)
private abbrev selected_spill_native_frame :=
  let duration:=support.size.spill cpu.room
  have cutoff : top ≤ first := (Nat.le_add_right ..).trans duration.archiveFloor
  have romFits : (g).romEnd rootROM ≤ first := by have gap:=duration.gap; have endOld:=duration.oldBefore; omega
  let frame:=captured.frame fromRank cutoff romFits
  let stride:=v.processing_stride x ell unitCost (fun _=>0) checked ranked frame
  let cells:=v.processing_sites x ell unitCost (fun _=>0) checked ranked frame
  have roleEnd : (g).rolesEnd S ≤ (g).workEnd S := by
    dsimp only [WideCPU.Dated.workEnd,WideCPU.Dated.slotStart,WideCPU.Dated.maskStart,
      WideCPU.Dated.controlStart,WideCPU.endOf]
    omega
  have workEnd : (g).workEnd S+2 ≤ (lay).floor := v.wide_window_after_terminal x _
  have floor : (lay).floor ≤ (lay).pruneScratch := Nat.le_add_right _ _
  have roleFloor : (g).rolesEnd S ≤ (lay).floor :=
    roleEnd.trans ((Nat.le_add_right _ 2).trans workEnd)
  have roleFirst : (g).rolesEnd S ≤ first :=
    roleFloor.trans (floor.trans ((Nat.le_add_right _ _).trans (Nat.le_add_right _ 1)))
  let low (n : ℕ) (hn : n<(g).rolesEnd S) :=
    (fromRank n (hn.trans_le roleFirst)).trans (fromPrune n (hn.trans_le roleFloor))
  And.intro frame (And.intro stride (And.intro cells low))


end

/-- The earlier tape has every genuine original role word and both immutable tables.
The accompanying native register record refers to precisely this ranked memory. -/
abbrev wide_selected_spill_operands := selectedSpillResult%
  let _selectedPaid := exactPurchasedReturn%
  let _issuedData := ballotReceipt _selectedPaid along [right, right, right, evidence, left]
  let _captures := ballotReceipt _issuedData along [evidence, evidence]
  let _stages := ballotReceipt _captures along [left]
  let _result := ballotReceipt _stages along [evidence, evidence, evidence, evidence]
  let regs := v.wide_selected_spill_registers m ell short u δ ξ unitCost x cpu rate support
    prices pricePos buy groupsFit metadata lanesFit e perm tag j
  let ranked := ballotReceipt _stages along [memory]
  let rankedImage := ballotReceipt _captures along [right, left]
  let rankBefore := ballotReceipt _result along [left]
  let pruneBefore := ballotReceipt _issuedData along [evidence, memory]
  let framed := v.selected_spill_native_frame m ell short u δ ξ unitCost x cpu rate support
    _ _ ranked _ rankedImage rankBefore pruneBefore
  let _frame := framed.1
  let _stride := framed.2.1
  let _cells := framed.2.2.1
  let _low := framed.2.2.2
  let _archivedFields := ballotReceipt _selectedPaid along [right, right, left, right, right, right, left]
  let _fields := afterLiteralDateFields _archivedFields ranked _low
  let _retainedRegisterFrame := regs.rankFrame
  let _retainedRegisterContents := regs.stored
  spillOperandProofs [_frame, _stride, _cells, _fields, _retainedRegisterFrame, _retainedRegisterContents]

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
