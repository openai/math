import OAI.Hierarchy.ProbeFixedNativeBudget
import OAI.Hierarchy.ProbeFixedReserveTotal
import OAI.Hierarchy.ProbeFixedReleasedSupply

namespace OAI
/-! # The real used-reserve bank and dated signed releases in the native protocol bound -/
noncomputable section
set_option quotPrecheck false
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage ProbeStage.Native CoreBoard
open StripChart StripDirectory ReportSockets PurchaseStage PurchaseFrozen PurchaseCT CatalogueRows
open CatalystArchive
open scoped BigOperators Classical
variable {F : Type*} [Field F] {k : ℕ} {p q Q σ Λ : ℝ}
  (v : FixedProtocolFormat F k p q Q σ Λ) (P : v.Placement) (z width r : ℕ)
  (banks : RouteSettlement.Banks) (src tab dest : ℕ) (owners : Bank)
local notation "N" => Stages z (2^v.W)
local notation "W" => wordBits z (2^v.W) copies
local notation "A" => v.billedAccount P z width r banks src tab dest owners
local notation "C" => v.nativeChart P z width r banks src tab dest owners
local notation "fmt" => v.nativeFormats P z width
local notation "bs" => v.nativeBoards P z width
local notation "items" => (v.mesh.inject+v.mesh.cool)*v.mesh.outerFuel
local notation "sink" => P.catalogue.sink r banks src tab dest owners
local notation "receipts" => v.receipts P z width r banks src tab dest owners
local notation "days" => v.birthMarks P z width r banks src tab dest owners
local notation "feeds" => feedColumns («N»:=N) v.mesh (v.privateArena P z width) fmt P.joint.initial width v.keepLimit
local notation "role" => fun a=>(StripChart.header F bs a).fieldTerm
local notation "ids" => StripChart.id F bs P.catalogue

/-- All global temperatures, prices, charged openings and dated labels are
those of the executed program. The positive charge comparison is localized to
one event (direct/mate, tree, and overflow). The catalyst debit identity is
localized to the actual complete owner tape. -/
theorem settled_budget (m : Memory W) (π : Equiv.Perm (Fin (2^z))) (wide : v.widthFloor≤width)
    (empty : ∀i : Commodity (Fin (2^z)) N k,m (P.joint.initial+PurchaseInventory.slot i)=0)
    (order : Fin P.catalogue.coreRows≃Edges v.sampler z (2^v.W) k)
    (room : items*(count z (2^v.W) k*paths z v.sampler.degree v.depth)=P.catalogue.boughtRows)
    (spill : Attempt→Traversals) (feed : Boundary → CommodityColumn→Traversals) (maxBits : ℕ)
    {count : ℕ} (L : OwnerLedger)
    (hist : Dates C m L (v.releasedBase P z width) count width)
    (keys : (Columns z (2^v.W)×Fin k)≃Fin count) (book : ReserveUse.Archive) (reserve : ℕ)
    (site : Fin (recordCount v.mesh (CatalystArchive.issued hist))→Fin count) (archiveMem : Memory W)
    {I : Type*} [Fintype I] (ordinary : I→List (Fin P.catalogue.rows))
    (back : Columns z (2^v.W)×Fin k→List (Fin P.catalogue.rows))
    (enum : Fin r≃RouteOccurrence ordinary back) (ci : I→ℕ)
    (reconciled : Whole.Reconciliation sink book reserve site (debit v.mesh (CatalystArchive.issued hist)) enum ci keys archiveMem)
    (shape : ∀u,.attempt u∈events v.mesh→L.rows (.attempt u)=(fmt u).pricedArea.occurrences)
    (origins : ∀a,∀ha : Event.attempt a∈events v.mesh,StripChart.AttemptPorts N v.depth k
      (StripChart.header F bs a).rows (max (Fintype.card (PayloadRole N k)) (Fintype.card (PurchasedRole v.depth k)))
      a (hist a ha).entry) (fits : width<2^W) :
    let settled:=ReserveUse.output book banks reserve site (debit v.mesh (CatalystArchive.issued hist)) archiveMem
    let used:=fun j=>RouteSettlement.actual banks.used settled (keys j).val
    let mEnd:=run C (events (C).mesh) m
    let marks:=days m
    let ord:=P.catalogue.ordinal v.sampler π v.depth marks order room
    let metric:=lenCode v.sampler π v.depth marks v.radius
    let len:=extendedLength ord metric
    let slices:=paidSlices v.mesh fmt feeds sink P.catalogue.idBase role ids (v.nativeTrees P z width) spill feed maxBits
    let stock:=((A).read (.outer (v.mesh.inject+v.mesh.cool) 0) mEnd).bits
    let paths:=fun i : Commodity (Fin (2^z)) N k=>(commodityWalk (S:=v.sampler) π i).map (Sum.inl (β:=Bought v.sampler π v.depth marks))
    let center:=fun j : Columns z (2^v.W)×Fin k=>(catalystWalk (S:=v.sampler) j).map (Sum.inl (β:=Bought v.sampler π v.depth marks))
    CalendarReadbacks A C m (2^z) v.mesh.inject v.actualK v.limit v.finish ((dyadicScale v.W)^8) ((v.W:ℝ)⁻¹^2)
      v.loss v.menu.margin (probeDensity k v.W) (purchaseReward k v.W) →
    Calendar.mounted C (events (C).mesh) m → ArchiveRoom C m (v.mesh.inject+v.mesh.cool) →
    (∀e∈events v.mesh,((eventSlices fmt feeds sink P.catalogue.idBase role ids (v.nativeTrees P z width) spill feed maxBits e).map
      (fun s=>s.toll mEnd len width)).sum≤(receipts mEnd e).install) →
    (∀(u : Fin (v.mesh.inject+v.mesh.cool)) (h : Fin v.mesh.outerFuel),
      let a:=Attempt.outer u.val h.val
      let sh:=v.frozenMarket P z width u h
      let frozen:=v.frozenInput P z width r banks src tab dest owners m u h
      ∃fixture : Memory W,sh.shelf.Incoming (k:=k) sh.sampler π sh.depth sh.phase sh.temperature sh.kind frozen ∧
      (∀i : Key z (2^v.W) k,sh.shelf.Prepared sh.sampler sh.depth fixture i frozen) ∧
      sh.rows≤2^(fmt a).batch.decisionBits ∧ (fmt a).batch.purchaseLink.lengthCode=.lit 1) →
    TermBudget p q Q Λ (2^z) width v.radius (∑_j : Columns z (2^v.W)×Fin k,reserve)
      (scaleOf v.sampler π v.depth marks) (fun e=>(metric e:ℝ))
      (fun e=>((PaidWidths.total slices mEnd (ord e)+routeLoad paths stock e+routeLoad center (fun j=>reserve-used j) e:ℕ):ℝ)/width) := by
  intro settled used mEnd marks ord metric len slices stock paths center accounts mounted archive invoice shelf
  obtain ⟨same,funded⟩:=v.reserve_receipt P z width r banks src tab dest owners L m hist keys book
    reserve site archiveMem ordinary back enum ci reconciled shape fits mounted
  exact v.native_budget P z width r banks src tab dest owners m π wide empty order room spill feed
    maxBits reserve used funded accounts mounted archive
    (v.dated_supply P z width r banks src tab dest owners L m hist shape origins fits mounted) invoice shelf same

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
