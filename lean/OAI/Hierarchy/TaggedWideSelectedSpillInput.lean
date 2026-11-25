import OAI.Hierarchy.TaggedWideSelectedPreclipArchive

namespace OAI
/-! # Stock and spill in the original selected preclip state -/
noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage CoreBoard CoreRoute ReportSockets
open CatalystArchive CatalogueRows Tagged WireTelescope CalendarTape TaggedShorterBudget TaggedShorterSupergroups
open Tagged.WideStack Filter ThreeFlat.RAM CoreBoard.PhysicalTerm
open scoped Classical BigOperators Fin.CommRing
set_option quotPrecheck false
set_option hygiene false
set_option maxRecDepth 12000
set_option cleanup.letToHave false
set_option maxHeartbeats 650000
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
variable {b : Fin k→ℕ} (e : TaggedPrune.OpenPins h width b→Bool) (perm : Equiv.Perm (Tagged.Row h))
    (tag : (perm : Tagged.Row h→Tagged.Row h)=Tagged.tag (fun i=>e (.inl i)))
local notation "base" => v.wideOrigin h width S seed perm
variable (j : Path sl es base)

local notation "lay" => v.wideInstalledLayout x m ell short u δ ξ unitCost g
local notation "first" => (lay).pruneScratch+(lay).pruneRows+1
local notation "top" => (v.privateArena (v.widePlacement h width) h width).endAddress v.mesh
variable (routeAge : v.routingHeight≤h) (height : v.BranchRoleHeight h width) (t : Fin (events v.mesh).length) (a : Attempt) (onDate : (events v.mesh).get t=.attempt a)

local notation "extent" => (v.wide_funded_extent h width v.maxBits).trans Sfit
local notation "chosen" => CalendarTape.Prefix.pathVisitAt j t onDate
local notation "date" => v.wide_funded_date_with h width S extent perm seed cpu.age cpu.ready.credit
  cpu.ready.size_le (chosen).prior (chosen).choice (chosen).future

open CoreBoard.HistoryRoles LinearAlgebra.SpectralBooks ChordGraph SiteTensor
local notation "old" => v.wide_funded_date h width S extent perm seed cpu.age cpu.ready.credit cpu.ready.size_le
  (chosen).prior (chosen).choice
local notation "scheduleAge" => (max_le_iff.mp routeAge).1
local notation "scheduleTail" => (max_le_iff.mp scheduleAge).2
local notation "feeAge" => (max_le_iff.mp ((max_le_iff.mp scheduleTail).2)).1

open Lean Elab Term in
local elab "paidCoordinate% " selectedName:ident " through " lastName:ident : term => do
  let actualFormat ← Meta.getFVarFromUserName `v
  let formatArgs := (← Meta.inferType actualFormat).consumeMData.getAppArgs
  let headName ← resolveGlobalConstNoOverload selectedName
  let decl ← getConstInfo headName
  let mut arguments := #[]
  let mut typ := decl.type
  let mut complete := false
  while typ.isForall do
    let binder := typ.bindingName!.eraseMacroScopes
    let localName := if binder == `external then `e else if binder == `π then `perm else binder
    let arg ← if typ.bindingInfo! == .instImplicit then pure formatArgs[1]! else Meta.getFVarFromUserName localName
    arguments := arguments.push arg
    if binder == lastName.getId then
      complete := true
      break
    typ := typ.bindingBody!
  unless complete do throwError "the issued physical operand has no binder {lastName.getId}"
  return mkAppN (mkConst headName (decl.levelParams.map Level.param)) arguments


local notation "chart" => v.wideSignedChart h width (v.fixedTerminalStock (v.widePlacement h width) h width)
local notation "atDate" => checkedOut chart top
  (v.wideOrigin h width S ((reader).format.windows.header es (date).code seed) perm)

private abbrev measuredSpillInputAt
    (bank : Fin (events v.mesh).length → Memory (Native.wordBits x.h (2^v.W) Native.copies))
    (initial : Memory (Native.wordBits x.h (2^v.W) Native.copies))
    (archive : ∀n,n<top → bank (date).index n=atDate n)
    (frame : ∀day n,n<first → bank day n=initial n) :=
  have covers : top ≤ first := (Nat.le_add_right ..).trans (support.size.spill cpu.room).archiveFloor
  let retained (n : ℕ) (low : n<top) :=
    (frame (date).index n (low.trans_le covers)).symm.trans (archive n low)
  (old).numbered_spill_only date Sfit height.measure height.report feeAge height.wordRoom first bank archive
    t onDate initial retained

/- The bank and the initial memory occur in the same purchased register
specification, with an input-frame equality on its original address interval. -/
open Lean Meta Elab Term in
local elab "selectedSpillFromRegister% " operator:term:max file:term:max bank:term:max archive:term:max : term => do
  let head ← elabTerm operator none
  let selected ← elabTerm file none
  let inputTape ← elabTerm bank none
  let retained ← elabTerm archive none
  let some record ← whnfUntil (← inferType selected) ``NativeSpillRegisters.Evidence
    | throwError "expected the purchased spill registers"
  let shared := record.getAppArgs.back!
  let some expanded ← unfoldDefinition? shared true
    | throwError "expected the selected native register specification"
  let spec := expanded.headBeta
  unless spec.getAppNumArgs == 39 && spec.getAppFn.constName?.any (fun n => n.getString! == "nativeRegisterFieldTypes") do
    throwError "unexpected physical register inputs"
  let initial := spec.getAppArgs[34]!
  let some frame := (← getEnv).getProjectionFnInfo? ``NativeSpillRegisters.Evidence.inputsFrame
    | throwError "expected the input bank frame witness"
  let witness := .proj ``NativeSpillRegisters.Evidence frame.i selected
  return mkAppN head #[inputTape, initial, retained, witness]

/-- The local step uses the commodity weights actually read on the selected
pre-pruning memory, including repeated uses of an original wire. -/
abbrev selected_spill_input_width :=
  selectedSpillFromRegister% (paidCoordinate% measuredSpillInputAt through onDate)
    (paidCoordinate% wide_selected_spill_registers through j)
    (paidCoordinate% selectedPreclipInputs through j)
    (paidCoordinate% selectedPreclipArchived through onDate)

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
