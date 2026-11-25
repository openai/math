import OAI.Hierarchy.TaggedWideFundedSelectedReturn
import OAI.Hierarchy.WidthSelectedSpillRegisters
import OAI.Hierarchy.TaggedWideFundedIndexedReplay
import OAI.Hierarchy.TaggedWireFundedPreclipWidth
import OAI.Hierarchy.TaggedWideBranchRoleHeight
import OAI.Hierarchy.ProbeFixedWideSpillFieldRoom

namespace OAI
/-! # Native input and output memories for the actual selected preclip chart -/

noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage CoreBoard CoreRoute ReportSockets
open CatalystArchive CatalogueRows Tagged WireTelescope CalendarTape TaggedShorterBudget TaggedShorterSupergroups
open Tagged.WideStack Filter ThreeFlat.RAM CoreBoard.PhysicalTerm
open scoped Classical BigOperators Fin.CommRing
set_option quotPrecheck false
set_option hygiene false
set_option maxRecDepth 12000
set_option maxHeartbeats 1800000
set_option cleanup.letToHave false
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
variable {b : Fin k→ℕ} (e : TaggedPrune.OpenPins x.h x.w b→Bool) (perm : Equiv.Perm (Tagged.Row x.h))
    (tag : (perm : Tagged.Row x.h→Tagged.Row x.h)=Tagged.tag (fun i=>e (.inl i)))
local notation "base" => v.wideOrigin h width S seed perm
variable (j : Path sl es base)
local notation "bought" => v.wide_selected_local_return m ell short u δ ξ unitCost x cpu rate support
  prices pricePos buy groupsFit metadata lanesFit e perm tag j

local notation "lay" => v.wideInstalledLayout x m ell short u δ ξ unitCost g
local notation "first" => (lay).pruneScratch+(lay).pruneRows+1
local notation "top" => (v.privateArena (v.widePlacement h width) h width).endAddress v.mesh
variable (side : Bool) (t : Fin (events v.mesh).length) (a : Attempt) (onDate : (events v.mesh).get t=.attempt a)

local notation "extent" => (v.wide_funded_extent h width v.maxBits).trans Sfit
local notation "chosen" => Prefix.pathVisitAt j t onDate
local notation "date" => v.wide_funded_date_with h width S extent perm seed cpu.age cpu.ready.credit
  cpu.ready.size_le (chosen).prior (chosen).choice (chosen).future
local notation "window" => (reader).format.windows
local notation "record" => CalendarTape.encode sl es base j
local notation "chart" => v.wideSignedChart h width (v.fixedTerminalStock (v.widePlacement h width) h width)


local notation "theRegisters" => v.wide_selected_spill_registers m ell short u δ ξ unitCost x cpu rate support
  prices pricePos buy groupsFit metadata lanesFit e perm tag j

/- The physical register carries its declared field specification. A primitive
projection avoids copying that specification into every field application. -/
open Lean Elab Term in
local elab "recordedSpillField% " fieldName:ident evidence:term : term => do
  let recordName := ``NativeSpillRegisters.Evidence
  let projectionName := recordName ++ fieldName.getId.eraseMacroScopes
  let some projection := (← getEnv).getProjectionFnInfo? projectionName
    | throwErrorAt fieldName "unknown field of the native spill-register evidence"
  return .proj recordName projection.i (← elabTerm evidence none)

/-- The source memory of each actual stable rank scan in the selected run. -/
def selectedPreclipInputs := v.wide_selected_spill_inputs m ell short u δ ξ unitCost x cpu rate support
  prices pricePos buy groupsFit metadata lanesFit e perm tag j

/-- These are the corrected sectors in the terminal memory of that same CPU run. -/
abbrev selectedPreclipContents := recordedSpillField% contents theRegisters

local notation "inputs" => v.selectedPreclipInputs m ell short u δ ξ unitCost x cpu rate support
  prices pricePos buy groupsFit metadata lanesFit e perm tag j

theorem selectedPreclipCode : (date).code=record ∧ (date).index=t := by
  have actual:=v.indexedFundedDate_at h width S extent perm seed cpu.age cpu.ready.credit cpu.ready.size_le j t onDate
  rw [Prefix.pathVisitAt_eq_cast j t onDate]
  exact ⟨actual.1,Fin.ext actual.2.1⟩

private theorem preclipAtRecordedDate {Code Day : Type} (recorded : Code → Day → Prop)
    {pathCode storedCode : Code} {pathDay storedDay : Day}
    (sameCode : pathCode = storedCode) (sameDay : pathDay = storedDay)
    (stored : recorded storedCode storedDay) : recorded pathCode pathDay := by
  cases sameCode
  cases sameDay
  exact stored

/-- The source used for the physical rank of the original day agrees with
the complete selected funded calendar on every archived word. -/
theorem selectedPreclipArchived :
    ∀n,n<top→inputs (date).index n=
      checkedOut chart top (v.wideOrigin h width S ((window).header es (date).code seed) perm) n := by
  have code:=v.selectedPreclipCode m ell short u δ ξ unitCost x cpu perm j t a onDate
  have low : top≤first := (Nat.le_add_right ..).trans (support.size.spill cpu.room).archiveFloor
  intro n hn
  let cellOf := fun encoded => checkedOut chart top
    (v.wideOrigin h width S ((window).header es encoded seed) perm) n
  have stored : inputs (date).index n = cellOf record :=
    ((recordedSpillField% inputsFrame theRegisters) (date).index n (hn.trans_le low)).trans
      ((recordedSpillField% stored theRegisters) n hn)
  exact stored.trans (congrArg cellOf code.1.symm)

local notation "rankAt" => v.wideSpillRankEnd h width v.maxBits first
local notation "sheet" => v.wideSpillDates h width ell unitCost v.maxBits first
local notation "qty" => (g).roleStart ((sheet).roleRoot rankAt 0) t.succ
local notation "terminal" => (bought).2.2.2.choose
variable (height : v.BranchRoleHeight h width)

/- The returned role field is indexed by the physical parameters of the
registered corrected sector. The record itself determines those parameters. -/
open Lean Elab Term in
local elab "selectedRoleAt% " receipt:ident " [" sectionNo:term "," slotNo:term "," readNo:term "]" : term => do
  let evidence ← Meta.getFVarFromUserName receipt.getId
  let some sectorType ← Meta.whnfUntil (← Meta.inferType evidence) ``correctedContents
    | throwError "expected the selected CPU's corrected spill sectors"
  let sector ← elabTerm sectionNo none
  let clock ← elabTerm slotNo none
  let roleField ← elabTerm readNo none
  let head ← Meta.mkConstWithFreshMVarLevels ``correctedContents.role
  return mkAppN head (sectorType.getAppArgs ++ #[evidence,sector,clock,roleField])

/-- The corrected width-field is read on the final tape of the same selected
CPU, with the original incidence identifiers and funded selector. -/
theorem selectedPreclipRole :
    (date).preclipRoleFact Sfit height.measure first inputs qty terminal := by
  have code:=v.selectedPreclipCode m ell short u δ ξ unitCost x cpu perm j t a onDate
  let storedSectors := v.selectedPreclipContents m ell short u δ ξ unitCost x cpu rate support
    prices pricePos buy groupsFit metadata lanesFit e perm tag j
  let calendarRole := selectedRoleAt% storedSectors [(0 : Fin 3), t.succ, (0 : Fin 3)]
  exact preclipAtRecordedDate
    (fun encoded day => FundedDate.preclipRoleFileAt («v» := v) («h» := h) («width» := width) («size» := S)
      («π» := perm) («seed» := seed) («age» := cpu.age) («budget» := cpu.ready.credit) («small» := cpu.ready.size_le)
      Sfit height.measure first inputs encoded day qty terminal)
    code.1 code.2 calendarRole

/-- The intermediate amounts use the whole local role word, including goods
that leave in the clipping pass on the same date. -/
theorem selectedPreclipWithin :
    v.wideHistoryUnit unitCost*width≤v.wideNeighborCap width unitCost := by
  have pos : 0<HistoryRoles.stride k v.sampler.degree v.wideJobs := by
    unfold HistoryRoles.stride
    positivity
  exact (Nat.le_mul_of_pos_left _ pos).trans (v.wide_neighbor_strict width unitCost).le

include support in
theorem selectedPreclipWord : v.wideHistoryUnit unitCost*width<2^(Native.wordBits h d Native.copies) := by
  have pos : 0<(1+publicStages v.W*(2*k))*(2*publicStages v.W+2) := Nat.mul_pos (by omega) (by omega)
  have scalar:=Nat.le_mul_of_pos_left (2*v.keepLimit+1) pos
  have cost : v.wideHistoryUnit unitCost≤v.widePrivateUnit unitCost := by
    unfold wideHistoryUnit widePrivateUnit
    omega
  exact (Nat.mul_le_mul_right width cost).trans_lt support.privateWord

-- The optional search index need not traverse the expanded native role signature.
run_cmd Lean.modifyEnv fun env => Lean.LibrarySuggestions.nameDenyListExt.addEntry env "selectedPreclipRole"
end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
