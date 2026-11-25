import OAI.Hierarchy.ProbeFixedCatalogueBudget
import OAI.Hierarchy.ProbeFixedOriginalPrice
import OAI.Hierarchy.ProbeFixedEventCosts
import OAI.Hierarchy.ProbeFixedBirthFees

namespace OAI
/-! # The actual fixed chart's terminal paid-link and residual-stock inequality -/

noncomputable section
set_option quotPrecheck false
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option cleanup.letToHave false
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage ProbeStage.Native CoreBoard
open StripChart StripDirectory ReportSockets PurchaseStage PurchaseFrozen PurchaseCT CatalogueRows
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
theorem native_budget (m : Memory W) (π : Equiv.Perm (Fin (2^z))) (wide : v.widthFloor≤width)
    (empty : ∀i : Commodity (Fin (2^z)) N k,m (P.joint.initial+PurchaseInventory.slot i)=0)
    (order : Fin P.catalogue.coreRows≃Edges v.sampler z (2^v.W) k)
    (room : items*(count z (2^v.W) k*paths z v.sampler.degree v.depth)=P.catalogue.boughtRows)
    (spill : Attempt→Traversals) (feed : Boundary → CommodityColumn→Traversals) (maxBits : ℕ)
    (reserve : ℕ) (used : Columns z (2^v.W)×Fin k→ℕ) (funded : ∀j,used j≤reserve) :
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
    (∀a,Event.attempt a∈events v.mesh → ∀i : Fin (fmt a).pricedArea.occurrences,
      (mEnd ((fmt a).pricedArea.direct+(fmt a).pricedArea.occurrences+i.val)).val≠0 →
      v.paidSupply z a (v.occurrencePort P z width a i).val=true) →
    (∀e∈events v.mesh,((eventSlices fmt feeds sink P.catalogue.idBase role ids (v.nativeTrees P z width) spill feed maxBits e).map
      (fun s=>s.toll mEnd len width)).sum≤(receipts mEnd e).install) →
    (∀(u : Fin (v.mesh.inject+v.mesh.cool)) (h : Fin v.mesh.outerFuel),
      let a:=Attempt.outer u.val h.val
      let sh:=v.frozenMarket P z width u h
      let frozen:=v.frozenInput P z width r banks src tab dest owners m u h
      ∃fixture : Memory W,sh.shelf.Incoming (k:=k) sh.sampler π sh.depth sh.phase sh.temperature sh.kind frozen ∧
      (∀i : Key z (2^v.W) k,sh.shelf.Prepared sh.sampler sh.depth fixture i frozen) ∧
      sh.rows≤2^(fmt a).batch.decisionBits ∧ (fmt a).batch.purchaseLink.lengthCode=.lit 1) →
    ((events v.mesh).map (fun ev=>(receipts mEnd ev).releasedBits)).sum=∑j,used j →
    TermBudget p q Q Λ (2^z) width v.radius (∑_j : Columns z (2^v.W)×Fin k,reserve)
      (scaleOf v.sampler π v.depth marks) (fun e=>(metric e:ℝ))
      (fun e=>((PaidWidths.total slices mEnd (ord e)+routeLoad paths stock e+routeLoad center (fun j=>reserve-used j) e:ℕ):ℝ)/width) := by
  intro mEnd marks ord metric len slices stock paths center history ready archive classify entry frozen released
  have pos : 0<width := v.clock.inject_pos.trans_le (v.clock.inject_width.trans wide)
  apply v.catalogueBudget C m rfl (v.privateArena P z width) fmt P.joint.initial width
    (v.issued P z width r banks src tab dest owners) empty wide feeds sink P.catalogue.idBase role ids
    (v.nativeTrees P z width) spill feed maxBits π marks ord len (fun _=>reserve) used (receipts mEnd)
    (extendedLength_nonneg ord metric) (extendedLength_apply ord metric) funded history
  · intro e live
    apply v.receipt_bill P z width r banks src tab dest owners mEnd e pos
    · rintro a rfl;exact classify a live
    · rintro u h j b rfl
      exact v.inner_not_opened P z width r banks src tab dest owners m u h j b live ready archive
  · exact entry
  · intros;rfl
  · intros;rfl
  · intro u h
    obtain ⟨fixture,inc,rom,padding,one⟩:=frozen u h
    exact v.born_capacity P z width r banks src tab dest owners m π u h fixture inc rom archive ready padding one
  · exact released

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
