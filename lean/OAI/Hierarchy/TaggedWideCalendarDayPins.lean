import OAI.Hierarchy.TaggedWideCalendarEndpointDay
import OAI.Hierarchy.TaggedWideFundedIndexedRouted
import OAI.Hierarchy.TaggedWidePathOuterBits

namespace OAI
/-! # Literal native and tensor arguments of a single original calendar site -/
noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
section
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage CoreBoard ReportSockets CatalogueRows CatalystArchive
open Tagged Tagged.WideStack TaggedShorterBudget TaggedShorterSupergroups ProtocolRAMEmit
open ProtocolRAMReportedPorts PurchaseFrozen
open scoped Classical BigOperators
set_option quotPrecheck false
set_option hygiene false
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option cleanup.letToHave false

variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ κ A δ ξ C : ℝ} {u : ℝ→ℝ}
    (v : FixedProtocolFormat F k p q Q σ Λ) (x : WideParent κ A) (tapeSize : ℕ)
    (π : Equiv.Perm (Fin (2^x.h))) (input : Boot.Tape x.h (2^v.W)) (m ell short unitCost : ℕ)
local notation "b" => (v.widePlacement x.h x.w).catalogue
local notation "jobs" => v.wideJobs
local notation "geom" => typeMenu κ A v.W m k jobs ell v.stage_positive (fun _=>short+ell)
local notation "menu" => (geom).menu u δ ξ
local notation "slots" => purchaseSlots x.h v.W k jobs ell
local notation "reserve" => fuel v.mesh*x.w
variable (raw : Fin (b).rows→ ProtocolRAMEmit.Row)
    (geometry : Geometry (boardLayout x.h (2^v.W) k x.w reserve) v.radius 1 raw)
    (actual : v.FundedCutRows x.h x.w tapeSize π input raw geometry unitCost)
    (prices : v.PhysicalCounts u A δ ξ m) (pricePos : 0≤κ)
    (buy : ∀t:Fin (m+1),Purchased F menu x t slots
      (purchaseCandidates x.h v.W k jobs slots ((menu).height t x) (purchaseModules v.W u δ ξ menu x t))
      (purchaseModules v.W u δ ξ menu x t) C)
    (groupsFit : GroupRoom v.W k jobs u δ ξ menu x)
    (metadata : ∀t:Fin (m+1),1+(menu).height t x+(menu).height t x≤(menu).payload t x)
    (lanesFit : v.wideInstalledCap unitCost≤2^ell)
open CoreBoard.PhysicalTerm Tagged.WideControlJoin WideCalendarSites HistoryRoles
open ThreeFlat Routing WireTelescope WireTelescope.CalendarTape TaggedPrune

local notation "days" => events v.mesh
local notation "dated" => v.wideDated x.h x.w ell unitCost
local notation "lay" => v.wideInstalledLayout x m ell short u δ ξ unitCost dated
local notation "size" => v.wideInstalledSize x m ell unitCost dated
local notation "seed" => v.wideInstalledHeader x m ell short u δ ξ unitCost dated
  (v.wide_dated_sites x.h x.w ell unitCost) (v.wide_dated_edges x.h x.w ell unitCost) (fun _=>0)
local notation "W" => Native.wordBits x.h (2^v.W) Native.copies
variable {N : ℕ} (cpu : v.ParentFullCPUs m ell short u δ ξ unitCost N x) (room : cpu.SiteRoom)
local notation "G" => (v.wideFullGates x m ell short u δ ξ unitCost cpu.room).2
local notation "slot" => (v.wideSelector x.h x.w cpu.age cpu.ready.credit cpu.ready.size_le).format.slot
variable (Z : CalendarTerms F x.h (2^v.W) k x.w reserve v.radius 1 slot days (v.wideOrigin x.h x.w size seed))
local notation "D" => v.parentShared x m ell short unitCost ((days).length+1)
local notation "Ex" => OpenPins x.h x.w ((Z).nativeRouting D).catalyst
local notation "Se" => Fin ((Z).nativeRouting D).selectors
local notation "cap" => v.widePrivateUnit unitCost*x.w
local notation "roles" => HistoryRoles.ceiling v.sampler (h:=x.h) («W»:=v.W) (k:=k) (attempts:=jobs)
  v.mesh unitCost v.keepLimit (fuel v.mesh) x.w
local notation "n" => ((days).length+1)*Fintype.card ((r:Public v.sampler x.h v.W k jobs)×Fin (roles r))

variable (perm : Equiv.Perm (Tagged.Row x.h)) (i : Fin (((Z).nativeRouting D).count perm))
local notation "branch" => (Fintype.equivFin (Path slot days ((v.wideOrigin x.h x.w size seed) perm))).symm i
local notation "original" => (Z).reported perm branch
local notation "time" => v.wideHistoryGate («Ex»:=Ex) («Se»:=Se) x m ell short u δ ξ unitCost cpu.room room.history
local notation "rout" => (Z).nativeRouting D
local notation "accept" => ((rout).links ⟨perm,i⟩).Keep (2^x.h)
local notation "flagAt" => (lay).pruneScratch+(lay).pruneRows
local notation "cursor" => CalendarTape.Prefix.cursorSlot («slot»:=slot) (events:=days) (x₀:=(v.wideOrigin x.h x.w size seed) perm)
local notation "hs" => CalendarTape.Prefix.atCursor (CalendarTape.Prefix.start : CalendarTape.Prefix slot days ((v.wideOrigin x.h x.w size seed) perm)
  days ((v.wideOrigin x.h x.w size seed) perm))
local notation "ws" => CalendarTape.Prefix.atWidth ((Z).width perm)
local notation "branchAt" => CalendarTape.Prefix.histories (CalendarTape.Prefix.start : CalendarTape.Prefix slot days ((v.wideOrigin x.h x.w size seed) perm)
  days ((v.wideOrigin x.h x.w size seed) perm)) branch

variable {v x tapeSize π input m ell short unitCost raw geometry actual prices pricePos buy
  groupsFit metadata lanesFit cpu room Z perm i}
variable {mem before initial out : Memory W}
local notation "signedBoard" => RowGeometry x.h (2^v.W) k x.w reserve v.radius 1
variable (same : reportGeometry perm original = (⟨(b).rows,raw,geometry⟩ : signedBoard))
local notation "sameRows" => congrArg
  (fun r : signedBoard => (⟨r.1,r.2.1⟩ : CalendarTerms.RowBoard)) same
local notation "imageType" => FundedCutRows.WindowReceipt v x tapeSize π input m ell short unitCost
  raw geometry actual prices pricePos buy groupsFit metadata lanesFit cpu.room room.purchase mem before initial out
local notation "sourceAt" ok:arg => FundedCutRows.rowData v x tapeSize π input m ell short unitCost
  raw geometry actual prices pricePos buy groupsFit metadata ok lanesFit
local notation "rankAt" ok:arg => CalendarTerms.RankedRows.onBranch Z perm i sameRows (sourceAt ok)
local notation "rankFacts" ex:arg sel:arg ok:arg place:arg => CalendarTerms.RankedRows.Endpoints Z (geom).index G time
  a.enter a.finish a.step perm i ex sel ((G).terminal out) (rankAt ok) place

variable (image : imageType) (ex : Ex → Bool) (sel : Se → Bool)
    (ok : geometry.links.Keep (2^x.h)) (place : PartyBit cursor ws days hs branchAt ↪ Fin n)
local notation "ranking" => rankAt ok
local notation "stepOp" => CalendarTape.Prefix.atStep ((Z).width perm) ((Z).operator perm)
local notation "replayed" => cursorReport perm ((Z).width perm) ((Z).reported perm) branchAt
local notation "wordTable" => (e : Fin (replayed).edges) → Fin (2^((replayed).rows e).width)
local notation "choices" => SiteChoices cursor ws days hs branchAt
local notation "view" => v.wideHistoryUnit unitCost*x.w
local notation "observed" d:arg q:arg s:arg j:arg => TypedWiring.value (a.step s j)
  (CalendarTerms.readPins (B:=G) (ranking).numbering ex sel ((G).terminal out)
    (nativePins («view»:=view) (geom).index (replayed).rows (ranking).positive (ranking).stage
      (ranking).installed (ranking).cap d (placedBits cursor ws days hs branchAt place q)))
local notation "valueAt" q:arg s:arg j:arg => datedState cursor ws s days hs branchAt j (q s)
local notation "matrixAt" j:arg => indexedStep cursor ws stepOp days hs branchAt j



local notation "dayPinsAt" kp:arg entryWords:arg choicesAt:arg =>
  (nativePins («view»:=view) (geom).index (replayed).rows (rankAt kp).positive (rankAt kp).stage
    (rankAt kp).installed (rankAt kp).cap entryWords (placedBits cursor ws days hs branchAt place choicesAt))
      ∘ (rankAt kp).numbering.symm

private def paidCalendarPartyBits (keptHere : geometry.links.Keep (2^x.h)) (entryWords : wordTable) (choicesAt : choices) : D → Bool :=
  dayPinsAt keptHere entryWords choicesAt

end

section
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage CoreBoard ReportSockets CatalogueRows CatalystArchive
open Tagged Tagged.WideStack TaggedShorterBudget TaggedShorterSupergroups ProtocolRAMEmit
open ProtocolRAMReportedPorts PurchaseFrozen
open scoped Classical BigOperators
set_option quotPrecheck false
set_option hygiene false
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option cleanup.letToHave false

variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ κ A δ ξ C : ℝ} {u : ℝ→ℝ}
    (v : FixedProtocolFormat F k p q Q σ Λ) (x : WideParent κ A) (tapeSize : ℕ)
    (π : Equiv.Perm (Fin (2^x.h))) (input : Boot.Tape x.h (2^v.W)) (m ell short unitCost : ℕ)
local notation "b" => (v.widePlacement x.h x.w).catalogue
local notation "jobs" => v.wideJobs
local notation "geom" => typeMenu κ A v.W m k jobs ell v.stage_positive (fun _=>short+ell)
local notation "menu" => (geom).menu u δ ξ
local notation "slots" => purchaseSlots x.h v.W k jobs ell
local notation "reserve" => fuel v.mesh*x.w
variable (raw : Fin (b).rows→ ProtocolRAMEmit.Row)
    (geometry : Geometry (boardLayout x.h (2^v.W) k x.w reserve) v.radius 1 raw)
    (actual : v.FundedCutRows x.h x.w tapeSize π input raw geometry unitCost)
    (prices : v.PhysicalCounts u A δ ξ m) (pricePos : 0≤κ)
    (buy : ∀t:Fin (m+1),Purchased F menu x t slots
      (purchaseCandidates x.h v.W k jobs slots ((menu).height t x) (purchaseModules v.W u δ ξ menu x t))
      (purchaseModules v.W u δ ξ menu x t) C)
    (groupsFit : GroupRoom v.W k jobs u δ ξ menu x)
    (metadata : ∀t:Fin (m+1),1+(menu).height t x+(menu).height t x≤(menu).payload t x)
    (lanesFit : v.wideInstalledCap unitCost≤2^ell)
open CoreBoard.PhysicalTerm Tagged.WideControlJoin WideCalendarSites HistoryRoles
open ThreeFlat Routing WireTelescope WireTelescope.CalendarTape TaggedPrune

local notation "days" => events v.mesh
local notation "dated" => v.wideDated x.h x.w ell unitCost
local notation "lay" => v.wideInstalledLayout x m ell short u δ ξ unitCost dated
local notation "size" => v.wideInstalledSize x m ell unitCost dated
local notation "seed" => v.wideInstalledHeader x m ell short u δ ξ unitCost dated
  (v.wide_dated_sites x.h x.w ell unitCost) (v.wide_dated_edges x.h x.w ell unitCost) (fun _=>0)
local notation "W" => Native.wordBits x.h (2^v.W) Native.copies
variable {N : ℕ} (cpu : v.ParentFullCPUs m ell short u δ ξ unitCost N x) (room : cpu.SiteRoom)
local notation "G" => (v.wideFullGates x m ell short u δ ξ unitCost cpu.room).2
local notation "slot" => (v.wideSelector x.h x.w cpu.age cpu.ready.credit cpu.ready.size_le).format.slot
variable (a : SignedSites v m ell short δ ξ unitCost cpu)
local notation "Z" => a.schedule
local notation "D" => v.parentShared x m ell short unitCost ((days).length+1)
local notation "Ex" => OpenPins x.h x.w ((Z).nativeRouting D).catalyst
local notation "Se" => Fin ((Z).nativeRouting D).selectors
local notation "cap" => v.widePrivateUnit unitCost*x.w
local notation "roles" => HistoryRoles.ceiling v.sampler (h:=x.h) («W»:=v.W) (k:=k) (attempts:=jobs)
  v.mesh unitCost v.keepLimit (fuel v.mesh) x.w
local notation "n" => ((days).length+1)*Fintype.card ((r:Public v.sampler x.h v.W k jobs)×Fin (roles r))

variable (perm : Equiv.Perm (Tagged.Row x.h)) (i : Fin (((Z).nativeRouting D).count perm))
local notation "branch" => (Fintype.equivFin (Path slot days ((v.wideOrigin x.h x.w size seed) perm))).symm i
local notation "original" => (Z).reported perm branch
local notation "time" => v.wideHistoryGate («Ex»:=Ex) («Se»:=Se) x m ell short u δ ξ unitCost cpu.room room.history
local notation "rout" => (Z).nativeRouting D
local notation "accept" => ((rout).links ⟨perm,i⟩).Keep (2^x.h)
local notation "flagAt" => (lay).pruneScratch+(lay).pruneRows
local notation "cursor" => CalendarTape.Prefix.cursorSlot («slot»:=slot) (events:=days) (x₀:=(v.wideOrigin x.h x.w size seed) perm)
local notation "hs" => CalendarTape.Prefix.atCursor (CalendarTape.Prefix.start : CalendarTape.Prefix slot days ((v.wideOrigin x.h x.w size seed) perm)
  days ((v.wideOrigin x.h x.w size seed) perm))
local notation "ws" => CalendarTape.Prefix.atWidth ((Z).width perm)
local notation "branchAt" => CalendarTape.Prefix.histories (CalendarTape.Prefix.start : CalendarTape.Prefix slot days ((v.wideOrigin x.h x.w size seed) perm)
  days ((v.wideOrigin x.h x.w size seed) perm)) branch

variable {v x tapeSize π input m ell short unitCost raw geometry actual prices pricePos buy
  groupsFit metadata lanesFit cpu room a perm i}
variable {mem before initial out : Memory W}
local notation "signedBoard" => RowGeometry x.h (2^v.W) k x.w reserve v.radius 1
variable (same : reportGeometry perm original = (⟨(b).rows,raw,geometry⟩ : signedBoard))
local notation "sameRows" => congrArg
  (fun r : signedBoard => (⟨r.1,r.2.1⟩ : CalendarTerms.RowBoard)) same
local notation "imageType" => FundedCutRows.WindowReceipt v x tapeSize π input m ell short unitCost
  raw geometry actual prices pricePos buy groupsFit metadata lanesFit cpu.room room.purchase mem before initial out
local notation "sourceAt" ok:arg => FundedCutRows.rowData v x tapeSize π input m ell short unitCost
  raw geometry actual prices pricePos buy groupsFit metadata ok lanesFit
local notation "rankAt" ok:arg => CalendarTerms.RankedRows.onBranch Z perm i sameRows (sourceAt ok)
local notation "rankFacts" ex:arg sel:arg ok:arg place:arg => CalendarTerms.RankedRows.Endpoints Z (geom).index G time
  a.enter a.finish a.step perm i ex sel ((G).terminal out) (rankAt ok) place

variable (image : imageType) (ex : Ex → Bool) (sel : Se → Bool)
    (ok : geometry.links.Keep (2^x.h)) (place : PartyBit cursor ws days hs branchAt ↪ Fin n)
local notation "ranking" => rankAt ok
local notation "stepOp" => CalendarTape.Prefix.atStep ((Z).width perm) ((Z).operator perm)
local notation "replayed" => cursorReport perm ((Z).width perm) ((Z).reported perm) branchAt
local notation "wordTable" => (e : Fin (replayed).edges) → Fin (2^((replayed).rows e).width)
local notation "choices" => SiteChoices cursor ws days hs branchAt
local notation "view" => v.wideHistoryUnit unitCost*x.w
local notation "observed" d:arg q:arg s:arg j:arg => TypedWiring.value (a.step s j)
  (CalendarTerms.readPins (B:=G) (ranking).numbering ex sel ((G).terminal out)
    (nativePins («view»:=view) (geom).index (replayed).rows (ranking).positive (ranking).stage
      (ranking).installed (ranking).cap d (placedBits cursor ws days hs branchAt place q)))
local notation "valueAt" q:arg s:arg j:arg => datedState cursor ws s days hs branchAt j (q s)
local notation "matrixAt" j:arg => indexedStep cursor ws stepOp days hs branchAt j



local notation "dayPinsAt" kp:arg entryWords:arg choicesAt:arg =>
  @paidCalendarPartyBits F (inferInstance : Field F) k p q Q σ Λ κ A δ ξ C u v x tapeSize π input
    m ell short unitCost raw geometry actual prices pricePos buy groupsFit metadata lanesFit N cpu
    (Z) perm i same place kp entryWords choicesAt

private theorem dayCheck_of_named_party_bits (j : Fin (days).length) :
    FundedCutRows.DayCheck (a:=a) (room:=room) (perm:=perm) (i:=i) same ex sel place image j ↔
      ∀ (kept : geometry.links.Keep (2^x.h)) (entryWords : wordTable) (choicesAt : choices) s,
        TypedWiring.value (a.step s j)
          (Sum.elim ex (Sum.elim sel (Sum.elim (dayPinsAt kept entryWords choicesAt) ((G).terminal out)))) =
        (matrixAt j) s (valueAt choicesAt s j.castSucc) (valueAt choicesAt s j.succ) := Iff.rfl

end

open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage CoreBoard CoreRoute ReportSockets
open CatalystArchive CatalogueRows Tagged WireTelescope CalendarTape TaggedShorterBudget TaggedShorterSupergroups
open Tagged.WideStack Filter ThreeFlat.RAM CoreBoard.PhysicalTerm
open TaggedPrune Tagged.WideControlJoin
open scoped Classical BigOperators Fin.CommRing
set_option quotPrecheck false
set_option hygiene false
set_option cleanup.letToHave false
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

open Lean Elab Term Meta in
private def recoveredDayInputs (observation : Lean.Expr) : MetaM (Array Lean.Expr) := do
  let some nativeDay ← whnfUntil observation ``FundedCutRows.DayCheck
    | throwError "expected the original paid calendar day"
  let args := nativeDay.getAppArgs
  unless args.size == 48 && args[35]!.isAppOf ``SignedSites.ofCalendar do
    throwError "expected the selected CPU, schedule, and row geometry"
  return args

open Lean Elab Term Meta in
local elab "paidAssignmentAt " family:term " withInputs " "[" operands:term,* "]" : term => do
  let daily ← elabTerm family none
  let domain ← whnf (← inferType daily)
  unless domain.isForall do throwError "expected the selected physical dates"
  let localValues ← operands.getElems.mapM (fun argument => elabTerm argument none)
  withLocalDeclD `physicalDate domain.bindingDomain! fun dayNumber => do
    let ds ← recoveredDayInputs (mkApp daily dayNumber)
    let siteArgs := ds[35]!.getAppArgs
    let actualSchedule := siteArgs[siteArgs.size - 4]!
    let inputs := ds.extract 0 34 ++ #[actualSchedule,ds[36]!,ds[37]!,ds[42]!,ds[45]!] ++ localValues
    let values := mkAppN (← mkConstWithFreshMVarLevels ``paidCalendarPartyBits) inputs
    if (Lean.collectFVars {} values).fvarSet.contains dayNumber.fvarId! then
      throwError "the funded party bits must be independent of the sampled date"
    return values

open Lean Elab Command Term Meta in
local elab "recordFundedDayPins " named:term : command => do
  let n := (← getCurrNamespace) ++ `calendarDayPins
  runTermElabM fun context => do
    let construction ← withoutErrToSorry <| elabTerm named none
    synthesizeSyntheticMVarsNoPostponing
    let value ← Term.levelMVarToParam (← mkLambdaFVars context (← instantiateMVars construction) (usedOnly := true))
    let type ← instantiateMVars (← inferType value)
    if value.hasFVar || value.hasMVar || value.hasSorry || type.hasFVar || type.hasMVar || type.hasSorry then
      throwError "the funded assignment must be closed"
    addDecl (.defnDecl {
      name := n
      levelParams := (collectLevelParams {} type).params.toList
      type := type
      value := value
      hints := .abbrev
      safety := .safe
    })
    addDocStringCore n "The Boolean data of the selected physical calendar rank from the funded native row."

recordFundedDayPins (fun (ok : kept) (words : wordTable) (statesAt : states) =>
  paidAssignmentAt (v.calendarDayRead (C:=C) m ell short u δ ξ x cpu room control support routeAge prices pricePos
    groupsFit metadata lanesFit buy e perm i tag height) withInputs [ok,words,statesAt])


open Lean Elab Command Term Meta in
local elab "recordPaidCalendarEquivalence " family:term " usingPins " pinFunction:term : command => do
  let theoremName := (← getCurrNamespace) ++ `calendarDayRead_iff
  runTermElabM fun context => do
    let days ← withoutErrToSorry <| elabTerm family none
    let publicPins ← withoutErrToSorry <| elabTerm pinFunction none
    synthesizeSyntheticMVarsNoPostponing
    let days ← instantiateMVars days
    let publicPins ← instantiateMVars publicPins
    let dateFamily ← whnf (← inferType days)
    unless dateFamily.isForall do throwError "expected the selected calendar date"
    let (statement, proof) ← withLocalDeclD `j dateFamily.bindingDomain! fun j => do
      let day := mkApp days j
      let ds ← recoveredDayInputs day
      unless ds.size == 48 do throwError "expected the original day-check operands"
      let rule ← mkConstWithFreshMVarLevels ``dayCheck_of_named_party_bits
      let checked := mkAppN rule (ds.extract 0 43 ++ #[ds[46]!, ds[43]!, ds[44]!, ds[45]!, ds[47]!])
      let original ← inferType checked
      unless original.isAppOfArity ``Iff 2 && original.getAppArgs[0]!.isAppOf ``FundedCutRows.DayCheck do
        throwError "expected the original day-check equivalence"
      let publicDay ← forallBoundedTelescope original.getAppArgs[1]! (some 4) fun operands equation => do
        unless operands.size == 4 && equation.isAppOfArity ``Eq 3 do
          throwError "expected the physical site equality on four operands"
        let gate := equation.getAppArgs[1]!
        unless gate.isAppOf ``TypedWiring.value do throwError "expected the selected physical row circuit"
        let external := gate.getAppArgs.back!
        let selector := external.getAppArgs.back!
        let dataPair := selector.getAppArgs.back!
        unless external.isAppOf ``Sum.elim && selector.isAppOf ``Sum.elim && dataPair.isAppOf ``Sum.elim do
          throwError "expected the four physical gate inputs"
        let dataIndex := dataPair.getAppNumArgs - 2
        unless dataPair.getAppArgs[dataIndex]!.isAppOf ``paidCalendarPartyBits do
          throwError "expected the named purchased data input"
        let publicData := mkAppN publicPins (operands.extract 0 3)
        let publicPair := mkAppN dataPair.getAppFn (dataPair.getAppArgs.set! dataIndex publicData)
        let withSelector := mkAppN selector.getAppFn (selector.getAppArgs.set! (selector.getAppNumArgs - 1) publicPair)
        let allPins := mkAppN external.getAppFn (external.getAppArgs.set! (external.getAppNumArgs - 1) withSelector)
        let publicGate := mkAppN gate.getAppFn (gate.getAppArgs.set! (gate.getAppNumArgs - 1) allPins)
        mkForallFVars operands (mkAppN equation.getAppFn (equation.getAppArgs.set! 1 publicGate))
      let atDate := mkApp2 (mkConst ``Iff) day publicDay
      return (← mkForallFVars #[j] atDate, ← mkLambdaFVars #[j] checked)
    let closedType ← mkForallFVars context (← instantiateMVars statement) (usedOnly := false)
    let closedValue ← mkLambdaFVars context (← instantiateMVars proof) (usedOnly := false)
    let checkedValue ← Term.levelMVarToParam closedValue
    let checkedType ← Term.levelMVarToParam closedType
    if checkedValue.hasFVar || checkedValue.hasMVar || checkedValue.hasSorry ||
        checkedType.hasFVar || checkedType.hasMVar || checkedType.hasSorry then
      throwError "the physical calendar equivalence has unbound operands"
    addDecl (.thmDecl {
      name := theoremName
      levelParams := (collectLevelParams {} checkedType).params.toList
      type := checkedType
      value := checkedValue
    })

recordPaidCalendarEquivalence (v.calendarDayRead (C:=C) m ell short u δ ξ x cpu room control support routeAge prices pricePos
  groupsFit metadata lanesFit buy e perm i tag height)
  usingPins (v.calendarDayPins (C:=C) m ell short u δ ξ x cpu support routeAge prices pricePos
    groupsFit metadata lanesFit buy e perm i tag height)

run_cmd Lean.modifyEnv fun env =>
  Lean.LibrarySuggestions.nameDenyListExt.addEntry (Lean.LibrarySuggestions.nameDenyListExt.addEntry env "calendarDayPins") "calendarDayRead_iff"
end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
