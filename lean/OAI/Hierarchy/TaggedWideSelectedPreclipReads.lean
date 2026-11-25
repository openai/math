import OAI.Hierarchy.TaggedWideSelectedPreclipLayout
import OAI.Hierarchy.TaggedWidePreclipCarriedBits
import OAI.Hierarchy.TaggedWideSelectedSignedApertures
import OAI.Hierarchy.TaggedWideCalendarDayPins

namespace OAI
/-! # Selected RAM reads on the signed intermediate state -/

/- Install the original selected read with the function type inferred by the kernel from its closed value. -/
open Lean Meta Elab Command in
local elab "kernelSelectedRead " declared:ident " := " body:term : command => do
  let target := (← getCurrNamespace) ++ declared.getId.eraseMacroScopes
  runTermElabM fun context => do
    let value ← Term.elabTermAndSynthesize body none
    let closed ← mkLambdaFVars context (← instantiateMVars value) (usedOnly := true)
    let closed ← instantiateMVars closed
    let closed ← Term.levelMVarToParam closed
    let closed := ShareCommon.shareCommon' closed
    if closed.hasFVar || closed.hasMVar || closed.hasSorry then
      let fvars := (Lean.collectFVars {} closed).fvarIds.map (·.name)
      let mvars ← Meta.getMVars closed
      let data := m!"free={repr fvars}, metavariables={repr (mvars.map (·.name))}, placeholder={closed.hasSorry}"
      throwErrorAt body "{target} has {data}"
    let result ← match Kernel.check (← getEnv) {} closed with
      | .ok result => pure result
      | .error ex => throwErrorAt body "{ex.toMessageData (← getOptions)}"
    let shared := ShareCommon.shareCommon' #[result, closed]
    let levels := (collectLevelParams (collectLevelParams {} shared[0]!) shared[1]!).params.toList
    addDecl (.defnDecl {
      name := target
      levelParams := levels
      type := shared[0]!
      value := shared[1]!
      hints := .regular 0
      safety := .safe
    })
    modifyEnv (addNoncomputable · target)


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

local notation "lay" => v.wideInstalledLayout x m ell short u δ ξ unitCost g
local notation "first" => (lay).pruneScratch+(lay).pruneRows+1
local notation "top" => (v.privateArena (v.widePlacement h width) h width).endAddress v.mesh
variable (routeAge : v.routingHeight≤h) (height : v.BranchRoleHeight h width) (t : Fin (events v.mesh).length) (a : Attempt) (onDate : (events v.mesh).get t=.attempt a)

local notation "extent" => (v.wide_funded_extent h width v.maxBits).trans Sfit
local notation "chosen" => WireTelescope.CalendarTape.Prefix.pathVisitAt j t onDate
local notation "date" => v.wide_funded_date_with h width S extent perm seed cpu.age cpu.ready.credit
  cpu.ready.size_le (chosen).prior (chosen).choice (chosen).future

local notation "inputs" => v.selectedPreclipInputs m ell short u δ ξ unitCost x cpu rate support
  prices pricePos buy groupsFit metadata lanesFit e perm tag j


open CoreBoard.HistoryRoles LinearAlgebra.SpectralBooks ChordGraph SiteTensor
local notation "old" => v.wide_funded_date h width S extent perm seed cpu.age cpu.ready.credit cpu.ready.size_le
  (chosen).prior (chosen).choice
local notation "scheduleAge" => (max_le_iff.mp routeAge).1
local notation "scheduleTail" => (max_le_iff.mp scheduleAge).2
local notation "feeAge" => (max_le_iff.mp ((max_le_iff.mp scheduleTail).2)).1
local notation "vroom" => v.wideHistoryUnit unitCost*x.w
local notation "cap" => v.wideNeighborCap width unitCost
local notation "fixed" => fun _ : Public v.sampler h v.W k v.wideJobs=>vroom
local notation "native" => v.wide_selected_local_return m ell short u δ ξ unitCost x cpu rate support
  prices pricePos buy groupsFit metadata lanesFit e perm tag j
local notation "out" => (native).2.2.2.choose
local notation "sector" => v.wideSpillDates h width ell unitCost v.maxBits first
local notation "startRole" => (g).roleStart ((sector).roleRoot (v.wideSpillRankEnd h width v.maxBits first) 0) t.succ
local notation "degree" => HistoryRoles.stride k v.sampler.degree v.wideJobs
local notation "arch" => v.selectedPreclipArchived m ell short u δ ξ unitCost x cpu rate support
  prices pricePos buy groupsFit metadata lanesFit e perm tag j t a onDate
local notation "bound" => (v.wide_selected_preclip_strict m ell short u δ ξ unitCost x cpu rate support
  prices pricePos buy groupsFit metadata lanesFit e perm tag j height t a onDate).1
local notation "realField" => v.selectedPreclipRole m ell short u δ ξ unitCost x cpu rate support
  prices pricePos buy groupsFit metadata lanesFit e perm tag j t a onDate height
local notation "within" => fun _ : Public v.sampler h v.W k v.wideJobs=>v.selectedPreclipWithin unitCost x
local notation "wordFits" => fun _ : Public v.sampler h v.W k v.wideJobs=>
    v.selectedPreclipWord m ell short u δ ξ unitCost x rate support

variable {Ex Se Data : Type} [Fintype Ex] [Fintype Se] [Fintype Data]

kernelSelectedRead selected_preclip_carried_bits := fun (siteId : Fin (siteLast h d k+1)) (gate : Tagged.WideControlJoin.Gate)
    (timelineCapacity : Public v.sampler h v.W k v.wideJobs→ℕ)
    (wiring : Fin (((es).length+1)*Fintype.card ((r:Public v.sampler h v.W k v.wideJobs)×Fin (timelineCapacity r)))→Data)
    (ext : Ex→Bool) (sel : Se→Bool) (bits : Data→Bool) (mem : Memory gate.W) (clipSide : Bool) => fun state =>
  (old).preclip_indexed_carried_at date Sfit height.measure height.report feeAge height.wordRoom first
    inputs arch (date).preclipUnique fixed bound within siteId state gate timelineCapacity wiring ext sel bits mem
    t (v.selectedPreclipCode m ell short u δ ξ unitCost x cpu perm j t a onDate).2 clipSide

/-- Every occupied bit of the true selected corrected row is seen by both
halves of the attempt. The original printed date is recovered from its path
visit, and the physical input ordinal is independent of the corrected cap. -/
add_decl_doc selected_preclip_carried_bits

kernelSelectedRead selected_offer_read := fun (siteId : Fin (siteLast h d k+1)) (gate : Tagged.WideControlJoin.Gate)
    (timelineCapacity : Public v.sampler h v.W k v.wideJobs→ℕ)
    (wiring : Fin (((es).length+1)*Fintype.card ((r:Public v.sampler h v.W k v.wideJobs)×Fin (timelineCapacity r)))→Data)
    (ext : Ex→Bool) (sel : Se→Bool) (bits : Data→Bool) (mem : Memory gate.W) (clipSide : Bool) => fun state active atWidth =>
  (old).preclip_indexed_offer_read date Sfit height.measure height.report feeAge height.wordRoom first
    inputs arch (date).preclipUnique fixed bound within siteId state gate timelineCapacity wiring ext sel bits mem
    t (v.selectedPreclipCode m ell short u δ ξ unitCost x cpu perm j t a onDate).2 clipSide active atWidth

run_cmd Lean.modifyEnv fun env => Lean.LibrarySuggestions.nameDenyListExt.addEntry env "selected_preclip_carried_bits"
run_cmd Lean.modifyEnv fun env => Lean.LibrarySuggestions.nameDenyListExt.addEntry env "selected_offer_read"
end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage CoreBoard CoreRoute ReportSockets
open CatalystArchive CatalogueRows Tagged WireTelescope CalendarTape TaggedShorterBudget TaggedShorterSupergroups
open Tagged.WideStack Filter ThreeFlat.RAM CoreBoard.PhysicalTerm
open TaggedPrune Tagged.WideControlJoin
open scoped Classical BigOperators Fin.CommRing
set_option quotPrecheck false
set_option hygiene false
set_option maxRecDepth 12000
set_option maxHeartbeats 1600000
set_option cleanup.letToHave false
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

variable (routeAge : v.routingHeight≤h)
local notation "arenaRoom" => (v.wide_funded_extent h width v.maxBits).trans Sfit
local notation "Z" => v.routedSchedule h width S arenaRoom seed cpu.age cpu.ready.credit cpu.ready.size_le
  Sfit routeAge support.size.widthFloor support.size.words
local notation "rout" => (Z).nativeRouting D
local notation "sites" => SignedSites.ofCalendar (cpu:=cpu) Z control v.calendarTerminalWidth
  (v.calendarTerminalPins x m ell short)
local notation "source" => fun _ : Fin (m+1)=>slots
local notation "count" => purchaseModules v.W u δ ξ menu x
local notation "target" => fun i=>purchaseCandidates h v.W k v.wideJobs slots ((menu).height i x) (count i)
local notation "Buy" => PurchaseList (F:=F) (C:=C) menu x source target count
local notation "Ex" => OpenPins h width (rout).catalyst
local notation "report" π:arg j:arg => v.wide_reported_path h width S π seed cpu.age cpu.ready.credit cpu.ready.size_le
  Sfit support.size.late support.size.words j
variable (prices : v.PhysicalCounts u A δ ξ m) (pricePos : 0≤κ)
    (groupsFit : GroupRoom v.W k v.wideJobs u δ ξ menu x)
    (metadata : ∀t:Fin (m+1),1+(menu).height t x+(menu).height t x≤(menu).payload t x)
    (lanesFit : v.wideInstalledCap unit≤2^ell)
variable (buy : Buy) (e : Ex→Bool) (perm : Equiv.Perm (Tagged.Row h)) (i : Fin ((rout).count perm))
    (tag : (perm : Tagged.Row h→Tagged.Row h)=Tagged.tag (fun n=>e (.inl n)))
local notation "path" => (Fintype.equivFin (Path sl es (base perm))).symm i
local notation "record" => CalendarTape.encode sl es (base perm) path

open CoreBoard.HistoryRoles CoreBoard.HistoryRoles.BranchRoles Tagged.WideCalendarSites
open ThreeFlat Routing
open LinearAlgebra.SpectralBooks ChordGraph
open Tagged.WideStack.Leaf ProtocolRAMReportedPorts
variable (height : v.BranchRoleHeight h width)
local notation "G" => (v.wideFullGates x m ell short u δ ξ unit cpu.room).2
local notation "W" => Native.wordBits h d Native.copies
local notation "root" => (WireTelescope.CalendarTape.Prefix.start : WireTelescope.CalendarTape.Prefix sl es (base perm) es (base perm))
local notation "tree" => WireTelescope.CalendarTape.Prefix.cursorSlot («slot»:=sl) (events:=es) (x₀:=base perm)
local notation "ws" => WireTelescope.CalendarTape.Prefix.atWidth ((Z).width perm)
local notation "top" => WireTelescope.CalendarTape.Prefix.atCursor root
local notation "branch" => WireTelescope.CalendarTape.Prefix.histories root path
local notation "stop" => terminal tree es top branch
local notation "input" => (reader).format.windows.header es record seed
local notation "bill" => v.wide_reported_path_native h width S perm seed cpu.age cpu.ready.credit cpu.ready.size_le
  Sfit support.size.late support.size.words path
local notation "admitted" => (bill).choose
local notation "cost" => (bill).choose_spec.choose
local notation "names" => (bill).choose_spec.choose_spec.choose
local notation "accepted" => (bill).choose_spec.choose_spec.choose_spec.1
local notation "native" => v.wide_native_report h width S perm.symm input v.maxBits Sfit admitted
  cpu.ready.credit cpu.ready.size_le cost (0:Word W) names
local notation "runAt" => v.wide_selected_local_return m ell short u δ ξ unit x cpu v.calendarUnit_rate support
  prices pricePos buy groupsFit metadata lanesFit e perm tag path
local notation "out" => (runAt).2.2.2.choose
local notation "actual" => Classical.choice (support.funding S Sfit perm.symm input admitted cpu.ready.credit
  cpu.ready.size_le cost (0:Word W) names accepted)
local notation "install" ok:arg => FundedCutRows.rowData v x S perm.symm input m ell short unit (native).rows
  (native).geometry actual prices pricePos buy groupsFit metadata ok lanesFit
local notation "geom" => typeMenu κ A v.W m k v.wideJobs ell v.stage_positive (fun _=>short+ell)
local notation "dir" => WideMemory.dir h v.W k v.wideJobs
local notation "ports" => WideMemory.H h v.W k v.wideJobs
local notation "b" => (v.widePlacement h width).catalogue
local notation "order" => v.wideOrder h width
local notation "roles" => HistoryRoles.ceiling v.sampler («h»:=h) («W»:=v.W) (k:=k) (attempts:=v.wideJobs)
  v.mesh unit v.keepLimit (fuel v.mesh) width
local notation "view" => v.wideHistoryUnit unit*width
local notation "times" => ((es).length+1)*Fintype.card ((r:Public v.sampler h v.W k v.wideJobs)×Fin (roles r))
local notation "shape" => v.widePathRoles h width S perm seed cpu.age cpu.ready.credit cpu.ready.size_le Sfit
  height.report height.wordRoom path unit height.replay height.measure (height.funded_aperture S unit Sfit v.calendarUnit_rate)
local notation "pins" => v.widePathCells h width S perm seed cpu.age cpu.ready.credit cpu.ready.size_le Sfit
  height.report height.wordRoom path unit height.replay height.measure (height.funded_aperture S unit Sfit v.calendarUnit_rate)
local notation "place" => timelineFin tree ws pins es top branch
local notation "replayed" => cursorReport perm ((Z).width perm) ((Z).reported perm) branch
local notation "Rpt" => CoreBoard.Report perm d k width (fuel v.mesh*width) v.radius 1 (ws stop)
local notation "table" r:arg => (⟨(r).edges,(r).rows⟩ : CalendarTerms.RowBoard)
local notation "plan" r:arg => CalendarTerms.RankedRows (F:=F) (geom).index D (dir).groups ports (2^ell) width m times view (table r)

local notation "same" => v.wide_selected_geometry m ell short u δ ξ unit x cpu v.calendarUnit_rate support
  prices pricePos buy groupsFit metadata lanesFit e perm tag path
local notation "sameRows" => congrArg (fun r:RowGeometry h d k width (fuel v.mesh*width) v.radius 1=>
  (⟨r.1,r.2.1⟩:CalendarTerms.RowBoard)) same
local notation "kept" => (native).geometry.links.Keep (2^h)
local notation "recorded" => v.wideCalendarPartyPlace m ell short u δ ξ x cpu Z perm i height (fun _=>rfl)
local notation "rnk" ok:arg => CalendarTerms.RankedRows.onBranch Z perm i sameRows (install ok)
local notation "wordTable" => (r : Fin (replayed).edges)→Fin (2^((replayed).rows r).width)
local notation "states" => SiteChoices tree ws es top branch

local notation "data" ok:arg words:arg q:arg => v.calendarDayPins (C:=C) m ell short u δ ξ x cpu support routeAge
  prices pricePos groupsFit metadata lanesFit buy e perm i tag height ok words q

open LinearAlgebra.SpectralBooks.SiteTensor Tagged.PassiveWindow
local notation "K" => siteLast h d k+1
local notation "deg" => HistoryRoles.stride k v.sampler.degree v.wideJobs
local notation "bound" => v.wideNeighborCap width unit
local notation "ends" => sorted v.sampler perm.symm v.depth (shape).mark ∘ (shape).order
local notation "portsAt" => named v.sampler perm.symm v.depth (shape).mark (shape).exclusive (shape).order
local notation "socket" => shelfSlot («h»:=h) («W»:=v.W) (k:=k) (attempts:=v.wideJobs) v.sampler
local notation "here" => named_coordinate v.sampler perm.symm v.depth (shape).mark (shape).exclusive (shape).order
local notation "timer" => SignedSites.calendarTime (v:=v) (x:=x) (m:=m) (ell:=ell) (short:=short) (unitCost:=unit)
local notation "boundAt" => v.wide_outer_lane h width unit
variable (ok : kept) (words : wordTable) (q : states) (j : Fin (es).length) (s : Fin K) (right : Bool)
local notation "timeAt" => if right then j.succ else j.castSucc
local notation "bits" => (shape).bits timeAt
local notation "fits" => fun r=>((shape).fits timeAt r false).trans (boundAt (portsAt (r,false)))
local notation "slotAt" => PacketNeighbor.localSlot ends bits portsAt socket here s
local notation "chart" => (shape).atWidth timeAt
local notation "parts" => carried ends bits s fits slotAt chart
local notation "current" => datedState tree ws s es top branch timeAt (q s)
local notation "assignment" => data ok words q
local notation "value" => Sum.elim e (Sum.elim record (Sum.elim assignment ((G).terminal out)))
local notation "tap" => LedgerStep.outerWord (cap:=bound) G es roles socket timer j s right

kernelSelectedRead calendar_day_preclip_carried_bits := fun (a : Attempt) (onDate : (es).get j=.attempt a) (clipSide : Bool) =>
  v.selected_preclip_carried_bits m ell short u δ ξ unit x cpu v.calendarUnit_rate support prices pricePos buy
    groupsFit metadata lanesFit e perm tag path routeAge height j a onDate s G roles timer e record assignment out clipSide

/-- The genuine chosen calendar's terminal CPU, external record and ranked private
pins, evaluated at both physical reads of the selected signed middle state. -/
add_decl_doc calendar_day_preclip_carried_bits

kernelSelectedRead calendar_day_offer_read := fun (a : Attempt) (onDate : (es).get j=.attempt a) (clipSide : Bool) =>
  v.selected_offer_read m ell short u δ ξ unit x cpu v.calendarUnit_rate support prices pricePos buy
    groupsFit metadata lanesFit e perm tag path routeAge height j a onDate s G roles timer e record assignment out clipSide

run_cmd Lean.modifyEnv fun env => Lean.LibrarySuggestions.nameDenyListExt.addEntry env "calendar_day_preclip_carried_bits"
run_cmd Lean.modifyEnv fun env => Lean.LibrarySuggestions.nameDenyListExt.addEntry env "calendar_day_offer_read"
end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
