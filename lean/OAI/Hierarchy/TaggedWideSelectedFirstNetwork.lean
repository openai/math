import OAI.Hierarchy.TaggedWideCalendarEndpointFields
import OAI.Hierarchy.TaggedWireFundedRowSchedule

namespace OAI
/-! # The original first-state equality at the selected chronological rank -/
noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage CoreBoard CoreRoute ReportSockets
open CatalystArchive CatalogueRows Tagged WireTelescope CalendarTape TaggedShorterBudget TaggedShorterSupergroups
open Tagged.WideStack Filter ThreeFlat.RAM CoreBoard.PhysicalTerm
open TaggedPrune Tagged.WideControlJoin
open scoped Classical BigOperators Fin.CommRing
set_option quotPrecheck false
set_option hygiene false
set_option maxRecDepth 16384
set_option maxHeartbeats 1000000
variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ κ A C : ℝ}
    (v : FixedProtocolFormat F k p q Q σ Λ) (m ell short : ℕ) (u : ℝ→ℝ) (δ ξ : ℝ)
    {N : ℕ} (x : WideParent κ A)
local notation "unit" => v.calendarUnit
variable (cpu : v.ParentFullCPUs m ell short u δ ξ unit N x) (room : cpu.SiteRoom)
    (control : SignedSites.CalendarControlRoom (cpu:=cpu))
    (support : v.SelectedReturnSupport m ell short u δ ξ unit v.calendarUnit_rate x)
local notation "h" => x.h
local notation "width" => x.w
local notation "d" => 2^v.W
local notation "g" => v.wideDated h width ell unit
local notation "S" => v.wideInstalledSize x m ell unit g
local notation "Sfit" => (v.wide_installed_tape_bounds x m ell unit g).2.2
local notation "seed" => v.wideInstalledHeader x m ell short u δ ξ unit g
    (v.wide_dated_sites h width ell unit) (v.wide_dated_edges h width ell unit) (fun _=>0)
local notation "reader" => v.wideSelector h width cpu.age cpu.ready.credit cpu.ready.size_le
local notation "sl" => (reader).format.slot
local notation "es" => events v.mesh
local notation "D" => v.parentShared x m ell short unit ((es).length+1)
local notation "menu" => (typeMenu κ A v.W m k v.wideJobs ell v.stage_positive (fun _=>short+ell)).menu u δ ξ
local notation "slots" => purchaseSlots h v.W k v.wideJobs ell
local notation "base" => v.wideOrigin h width S seed

variable (late : v.rowScheduleHeight≤ h)
local notation "arenaRoom" => (v.wide_funded_extent h width v.maxBits).trans Sfit
local notation "tall" => (max_le_iff.mp late).1
local notation "floor" => support.size.widthFloor
variable (incoming : ∀(p : Equiv.Perm (Tagged.Row h)) {a tail state} (t : WireTelescope.CalendarTape.Prefix sl es (base p) (.attempt a::tail) state),
    v.sourceRows h width S arenaRoom p seed cpu.age cpu.ready.credit cpu.ready.size_le t tall floor)
  (outgoing : ∀(p : Equiv.Perm (Tagged.Row h)) {a tail state} (t : WireTelescope.CalendarTape.Prefix sl es (base p) (.attempt a::tail) state),
    v.targetRows h width S arenaRoom p seed cpu.age cpu.ready.credit cpu.ready.size_le t tall floor)
local notation "Z" => v.with_elected_rows h width S arenaRoom seed cpu.age cpu.ready.credit cpu.ready.size_le
  Sfit late floor support.size.words incoming outgoing
local notation "rout" => (Z).nativeRouting D
local notation "sites" => SignedSites.ofCalendar (cpu:=cpu) Z control v.calendarTerminalWidth
  (v.calendarTerminalPins x m ell short)
local notation "source" => fun _ : Fin (m+1)=>slots
local notation "count" => purchaseModules v.W u δ ξ menu x
local notation "target" => fun i=>purchaseCandidates h v.W k v.wideJobs slots ((menu).height i x) (count i)
local notation "Buy" => PurchaseList (F:=F) (C:=C) menu x source target count
local notation "Ex" => OpenPins h width (rout).catalyst
local notation "report" π j => v.wide_reported_path h width S π seed cpu.age cpu.ready.credit cpu.ready.size_le
  Sfit support.size.late support.size.words j
variable (prices : v.PhysicalCounts u A δ ξ m) (pricePos : 0≤κ)
    (groupsFit : GroupRoom v.W k v.wideJobs u δ ξ menu x)
    (metadata : ∀t:Fin (m+1),1+(menu).height t x+(menu).height t x≤(menu).payload t x)
    (lanesFit : v.wideInstalledCap unit≤2^ell)
variable (buy : Buy) (e : Ex→Bool) (perm : Equiv.Perm (Tagged.Row h)) (i : Fin ((rout).count perm))
    (tag : (perm : Tagged.Row h→Tagged.Row h)=Tagged.tag (fun n=>e (.inl n)))
local notation "path" => (Fintype.equivFin (Path sl es (base perm))).symm i
local notation "record" => CalendarTape.encode sl es (base perm) path

open CoreBoard.HistoryRoles Tagged.WideCalendarSites
open ThreeFlat Routing
variable (height : v.BranchRoleHeight h width)
local notation "G" => (v.wideFullGates x m ell short u δ ξ unit cpu.room).2
local notation "cap" => HistoryRoles.ceiling v.sampler («h»:=h) (W:=v.W) (k:=k) (attempts:=v.wideJobs)
  v.mesh unit v.keepLimit (fuel v.mesh) width
local notation "hist" => SignedSites.calendarHistory (v:=v) (x:=x) (m:=m) (ell:=ell)
  (short:=short) (unitCost:=unit)

private theorem value_at_time_pin {X Y B : Type} {active printed : X} {pins : Y} {value : B}
    (run : X→Y→B) (same : active=printed) (read : run active pins=value) :
    run printed pins=value := same ▸ read

/-- The funded entry observes all genuine site assignments on the common
party-bit placement of the selected branch. Original row numbering changes
only the private bank, and its transported time embedding is preserved at rank. -/
theorem wideCalendar_first_field :
    v.wideCalendarEndpointField (C:=C) m ell short u δ ξ x cpu room control support
      Z (fun _ _=>rfl) prices pricePos groupsFit metadata lanesFit buy e perm i tag height (fun _=>rfl) .first := by
  intro kept allocation states site
  change TypedWiring.value (EntryOrder.firstNetwork (Se:=Fin (rout).selectors)
    v.sampler cap es G hist routingPort F site) _ = _
  refine value_at_time_pin
    (fun t assignment=>TypedWiring.value (EntryOrder.firstNetwork (Se:=Fin (rout).selectors)
      v.sampler cap es G t routingPort F site) assignment) ?_
    (v.widePath_first_network h width S perm seed cpu.age cpu.ready.credit cpu.ready.size_le
      Sfit height.report height.wordRoom path unit height.replay height.measure
      (height.funded_aperture S unit Sfit v.calendarUnit_rate) G _ _ _ _ _ _ _ allocation
      states site e record _)
  apply CalendarTerms.RankedRows.onBranch_property _ _ _ _ _
    (fun _ r=>EntryOrder.timePin r.numbering=hist)
  ext j
  rfl

run_cmd Lean.modifyEnv fun env => Lean.LibrarySuggestions.nameDenyListExt.addEntry env "wideCalendar_first_field"
end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
