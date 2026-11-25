import OAI.Hierarchy.TaggedWideRankedCuts
import OAI.Hierarchy.TaggedWideRankedPrivateCells
import OAI.Hierarchy.TaggedWideFundedReceiptCuts

namespace OAI
/-! # Purchased cuts and their masks at the actual signed-site rank -/

noncomputable section
open scoped Fin.CommRing
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
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
local notation "ports" => WideMemory.H x.h v.W k jobs
local notation "dir" => WideMemory.dir x.h v.W k jobs
local notation "order" => v.wideOrder x.h x.w
local notation "positive" => (b).transport order
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
    (kept : geometry.links.Keep (2^x.h)) (lanesFit : v.wideInstalledCap unitCost≤2^ell)
open CoreBoard.PhysicalTerm Tagged.WideControlJoin WideCalendarSites HistoryRoles
open ThreeFlat Routing WireTelescope WireTelescope.CalendarTape TaggedPrune

local notation "real" => FundedCutRows.installed v x tapeSize π input m ell short unitCost raw geometry actual
  prices pricePos buy groupsFit metadata kept lanesFit
local notation "days" => events v.mesh
local notation "dated" => v.wideDated x.h x.w ell unitCost
local notation "lay" => v.wideInstalledLayout x m ell short u δ ξ unitCost dated
local notation "size" => v.wideInstalledSize x m ell unitCost dated
local notation "seed" => v.wideInstalledHeader x m ell short u δ ξ unitCost dated
  (v.wide_dated_sites x.h x.w ell unitCost) (v.wide_dated_edges x.h x.w ell unitCost) (fun _=>0)
local notation "dst" => TerminalLayout.destination (v.wideSignedPage x.h x.w
  (v.fixedTerminalStock (v.widePlacement x.h x.w) x.h x.w))
local notation "W" => Native.wordBits x.h (2^v.W) Native.copies
variable {N : ℕ} (cpu : v.ParentFullCPUs m ell short u δ ξ unitCost N x) (room : cpu.SiteRoom)
local notation "G" => (v.wideFullGates x m ell short u δ ξ unitCost cpu.room).2
local notation "slot" => (v.wideSelector x.h x.w cpu.age cpu.ready.credit cpu.ready.size_le).format.slot
variable (a : SignedSites v m ell short δ ξ unitCost cpu)
local notation "Z" => a.schedule
local notation "D" => v.parentShared x m ell short unitCost ((days).length+1)
local notation "Ex" => OpenPins x.h x.w ((Z).nativeRouting D).catalyst
local notation "Se" => Fin ((Z).nativeRouting D).selectors
local notation "Priv" => (b).Private order
local notation "cap" => v.widePrivateUnit unitCost*x.w
local notation "lim" => fun _:Priv=>cap
local notation "view" => v.wideHistoryUnit unitCost*x.w
local notation "roles" => HistoryRoles.ceiling v.sampler (h:=x.h) («W»:=v.W) (k:=k) (attempts:=jobs)
  v.mesh unitCost v.keepLimit (fuel v.mesh) x.w
local notation "history" => Fin (((days).length+1)*Fintype.card
  ((r:Public v.sampler x.h v.W k jobs)×Fin (roles r)))
local notation "outputBits" => ((Fin (dir).groups×Fin ports)×Fin view)
local notation "num" => CalendarTerms.privateWorkspace (geom).index (Equiv.refl Priv) lim roles
  (dir).groups ports (2^ell) ((days).length+1) view x.w
local notation "freeNet" => v.widePrivateGate («Ex»:=Ex) («Se»:=Se) x m ell short u δ ξ unitCost cpu.room room.privateBits
local notation "planeNet" => v.widePlane («Ex»:=Ex) («Se»:=Se) x m ell short u δ ξ unitCost cpu.room

local notation "n" => ((days).length+1)*Fintype.card ((r:Public v.sampler x.h v.W k jobs)×Fin (roles r))
local notation "Board" => (⟨(b).rows,raw⟩ : CalendarTerms.RowBoard)
local notation "dataAt" => CalendarTerms.RankedRows (F:=F) (geom).index D (dir).groups ports (2^ell) x.w m n view

local notation "purchase" => FundedCutRows.rowData v x tapeSize π input m ell short unitCost raw geometry actual
  prices pricePos buy groupsFit metadata kept lanesFit
variable (perm : Equiv.Perm (Tagged.Row x.h)) (i : Fin (((Z).nativeRouting D).count perm))
local notation "branch" => (Fintype.equivFin (Path slot days ((v.wideOrigin x.h x.w size seed) perm))).symm i
local notation "original" => (Z).reported perm branch
variable (reported : (⟨(original).edges,(original).rows⟩ : CalendarTerms.RowBoard)=Board)
local notation "atRank" => CalendarTerms.RankedRows.onBranch Z perm i reported purchase


local notation "hardware" => a.installed room
local notation "cuts" => fun t=>(buy t).cut ((hardware).read t)
local notation "pad" => cpu.positiveGate room Z
local notation "port" => FundedCutRows.port v x tapeSize π input unitCost raw geometry actual
local notation "anchor" => (FundedCutRows.aperture actual) x.formats.2.1
local notation "old" => atScale positive (fun _=>0) 0 raw
local notation "seedRoot" => v.wideInstalledRoot x
local notation "K" => v.wideInstalledCap unitCost
local notation "base" => v.wideGroupROM x dated v.maxBits seedRoot
local notation "words" => v.wideWindowWords x m ell short u δ ξ K dated v.maxBits seedRoot
local notation "upper" => (show (lay).floor<2^W from by
  have h : (lay).floor≤(lay).pruneScratch:=Nat.le_add_right _ _
  have e:=v.wideFullGates_prune_room (u:=u) (δ:=δ) (ξ:=ξ) x m ell short unitCost cpu.room
  omega)
local notation "bounds" t => v.wideWindow_limits x m ell short u δ ξ unitCost dated room.purchase upper t old
  (fun row => show (raw row).link=row.val from FundedCutRows.originalId actual row) (FundedCutRows.masked_width v x tapeSize π input unitCost raw geometry actual)
local notation "bought" => FundedCutRows.printed v x tapeSize π input m ell short unitCost raw geometry actual
  prices pricePos buy groupsFit metadata kept lanesFit
variable (mem before initial out : Memory W)
  (directory : ∀j,base≤ j → j< base+2*ProtocolRAMPurchaseSampler.span (dir).groups → before j=words mem j)
  (emitted : ∀j,dst≤ j → j< dst+9*(b).rows → before j=ProtocolRAMEmit.emitted dst raw initial j)
  (slotsAt : ∀t side (j:ProtocolRAMPackedPlacement.Live old x.w),
    (if side then ((lay).inputs t).right else ((lay).inputs t).left).read before (j.val.val:Word W)=
      ((port side j.val).val*2^ell:ℕ))
local notation "active" => fun j hj=>((FundedCutRows.owner actual) x.formats.2.1 ⟨j,hj⟩ false) ▸
  (anchor (⟨j,hj⟩,false)).1.isLt
local notation "group" t => fun j _=>v.wideWindow_owner_read («W»:=W) x m ell short u δ ξ K dated v.maxBits seedRoot
  t raw initial before emitted (v.wideWindow_rows_fit x m ell short u δ ξ unitCost dated upper) j
local notation "printed" t => v.wideCutAnchor x m ell short u δ ξ K dated v.maxBits seedRoot t mem before old
  (bounds t) (bought t) directory active (group t) (slotsAt t)
variable (terminal : ∀t q,out (((lay).windows t).address ((lay).windowBase t) q)=(printed t).word old q)

include terminal in
/-- The actual cut pins of the installed signed-site hardware and its fixed
positive-mask gate read the same two native per-format boards. -/
theorem FundedCutRows.site_cuts_masks (ex : Ex→ Bool) (sel : Se→ Bool) :
    CalendarTerms.RankedRows.CutsAndMask G purchase cuts pad ex sel ((G).terminal out) := by
  constructor
  · exact FundedCutRows.cuts (v:=v) (x:=x) (tapeSize:=tapeSize) (π:=π) (input:=input)
      (m:=m) (ell:=ell) (short:=short) (unitCost:=unitCost) (raw:=raw) (geometry:=geometry)
      (actual:=actual) (prices:=prices) (pricePos:=pricePos) (buy:=buy) (groupsFit:=groupsFit)
      (metadata:=metadata) (kept:=kept) (lanesFit:=lanesFit) («lim»:=cpu.room) (large:=room.purchase)
      (mem:=mem) (before:=before) (initial:=initial) (out:=out) (retained:=directory)
      (reported:=emitted) (portWords:=slotsAt) (terminal:=terminal) («Z»:=Z)
      (privateOrder:=Equiv.refl Priv) (privateCap:=lim) (historyCap:=roles) (dates:=(days).length+1)
      («view»:=view) (head:=cpu.firstPins ((Z).nativeRouting D).catalyst)
      (paidHead:=cpu.paidPins ((Z).nativeRouting D).catalyst)
      (flag:=v.wideKeepNetwork x m ell short u δ ξ unitCost cpu.room Ex Se D)
      («mask»:=pad) («free»:=freeNet) («plane»:=planeNet)
      (timeline:=v.wideHistoryGate («Ex»:=Ex) («Se»:=Se) x m ell short u δ ξ unitCost cpu.room room.history)
      (enter:=a.enter) (finish:=a.finish) (step:=a.step) ex sel
  · exact FundedCutRows.masks (v:=v) (x:=x) (tapeSize:=tapeSize) (π:=π) (input:=input)
      (m:=m) (ell:=ell) (short:=short) (unitCost:=unitCost) (raw:=raw) (geometry:=geometry)
      (actual:=actual) (prices:=prices) (pricePos:=pricePos) (buy:=buy) (groupsFit:=groupsFit)
      (metadata:=metadata) (kept:=kept) (lanesFit:=lanesFit) («lim»:=cpu.room) (large:=room.purchase)
      (mem:=mem) (before:=before) (initial:=initial) (out:=out) (retained:=directory)
      (reported:=emitted) (portWords:=slotsAt) (terminal:=terminal) («Z»:=Z)
      (privateOrder:=Equiv.refl Priv) (privateCap:=lim) (historyCap:=roles) (dates:=(days).length+1)
      («view»:=view) (low:=room.positive) ex sel

include terminal in
/-- Transport the original two native observations onto exactly the dependent
row family used by all the other gates at the selected real path rank. -/
theorem FundedCutRows.ranked_cuts_masks (ex : Ex→ Bool) (sel : Se→ Bool) :
    CalendarTerms.RankedRows.CutsAndMask G atRank cuts pad ex sel ((G).terminal out) := by
  apply CalendarTerms.RankedRows.onBranch_property Z perm i reported purchase
    (fun _ rows=>CalendarTerms.RankedRows.CutsAndMask G rows cuts pad ex sel ((G).terminal out))
  exact FundedCutRows.site_cuts_masks v x tapeSize π input m ell short unitCost raw geometry actual
    prices pricePos buy groupsFit metadata kept lanesFit cpu room a mem before initial out
    directory emitted slotsAt terminal ex sel

/-- At a selected original branch, the two program readouts are obtained
from its funded window receipt without rechoosing any port or slot. -/
theorem FundedCutRows.ranked_window_fields
    (image : FundedCutRows.WindowReceipt v x tapeSize π input m ell short unitCost raw geometry actual
      prices pricePos buy groupsFit metadata lanesFit cpu.room room.purchase mem before initial out)
    (ex : Ex→Bool) (sel : Se→Bool) :
    CalendarTerms.RankedRows.CutsAndMask G atRank cuts pad ex sel ((G).terminal out) :=
  FundedCutRows.ranked_cuts_masks v x tapeSize π input m ell short unitCost raw geometry actual
    prices pricePos buy groupsFit metadata kept lanesFit cpu room a perm i reported mem before initial out
    image.directory image.emitted image.slotsAt (image.terminal kept) ex sel

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
