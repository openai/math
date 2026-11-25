import OAI.Hierarchy.ProbeFixedReceipts
import OAI.Hierarchy.ProtocolRAMRepairCommodity
import OAI.Hierarchy.ProbePaidRoleCost
import OAI.Hierarchy.ProtocolRAMCalendarFeedCharge

namespace OAI
/-! # Original-strip and physical spill costs in the archived positive receipt -/

noncomputable section
open scoped Fin.CommRing
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage ProbeStage.Native CoreBoard
open StripChart StripDirectory CatalogueRows StockCommit
open scoped BigOperators Classical

variable {F : Type*} [Field F] {k : ℕ} {p q Q σ Λ : ℝ}
  (v : FixedProtocolFormat F k p q Q σ Λ) (P : v.Placement) (z width r : ℕ)
  (banks : RouteSettlement.Banks) (src tab dest : ℕ) (owners : Bank)
local notation "N" => Stages z (2^v.W)
local notation "bank" => v.nativeBoards P z width
local notation "fmt" => v.nativeFormats P z width
local notation "C" => v.nativeChart P z width r banks src tab dest owners
local notation "sink" => P.catalogue.sink r banks src tab dest owners
local notation "rec" => v.receipts P z width r banks src tab dest owners

/-- Installed direct edges and both paid radii, the physical selector spine and
repeated core edges are tested at the actual archived row with positive width. -/
theorem receipt_install {w : ℕ} (m : Memory w) (a : Attempt) (len : Fin P.catalogue.rows→ℝ)
    (routes : Traversals) (bound : ℕ) (cost : Fin (fmt a).occurrences→ℝ) (mask second : Expr)
    (tree : Fin (fmt a).pricedArea.rows→List (Fin P.catalogue.rows))
    (core : Fin (fmt a).pricedArea.goods→List (Fin P.catalogue.rows)) :
    let f:=fmt a
    let forest:=v.nativeTrees P z width a
    let role:=(StripChart.header F bank a).fieldTerm
    let ids:=StripChart.id F bank P.catalogue a
    f.occurrences≤2^w →
    (∀i : Fin f.occurrences,(m (f.pricedArea.direct+i.val)).val≠0 → ∃e : Fin P.catalogue.rows,
      ((f.labelSource sink P.catalogue.idBase role ids).edge.eval m (i.val:Word w)).val=e.val ∧ len e=cost i) →
    forest.catalystMate=some (mask,second) →
    (∀i : Fin f.occurrences,mask.eval m (i.val:Word w)≠0 → (m (f.pricedArea.direct+i.val)).val≠0 →
      ∃e : Fin P.catalogue.rows,(second.eval m (i.val:Word w)).val=e.val ∧ len e=v.radius) →
    forest.Reads m tree → routes.Reads m core → bound<2^w → f.board.batch.copies<2^w →
    (∀i : Fin f.pricedArea.rows,(m (f.pricedArea.broadcast+i.val)).val≤bound) →
    (∀i : Fin f.pricedArea.rows,f.board.batch.copies*(m (f.pricedArea.broadcast+i.val)).val<2^w) →
    (∀i : Fin f.occurrences,(m (f.pricedArea.direct+i.val)).val≠0 →
      cost i+(if mask.eval m (i.val:Word w)=0 then 0 else (v.radius:ℝ))≤v.paidRate P z width r banks src tab dest owners m a i) →
    (∀i : Fin f.pricedArea.rows,(m (f.pricedArea.broadcast+i.val)).val≠0 →
      ((tree i).map len).sum≤v.cost.atAttempt a) →
    (∀i : Fin f.pricedArea.goods,(m (f.pricedArea.output+f.pricedArea.goods+f.pricedArea.goods+i.val)).val≠0 →
      ((core i).map len).sum≤v.coreCharge P z width a i 0) →
    (((f.paidSlices sink P.catalogue.idBase role ids forest routes bound).map (fun t=>t.toll m len width)).sum ≤
      (rec m (.attempt a)).install) := by
  intro f forest role ids fit hits mate reached locations paths word copies bits full price treeCost routeCost
  let B:=repair C a
  let cols:=(fresh f.pricedArea f.stockSource).eventColumns B.purchaseOut
  have exactCost := f.two_radii_charge sink P.catalogue.idBase role ids forest routes bound width m len cost
    mask second (v.radius:ℝ) tree core B.purchaseOut f.pricedArea.rows (fun _=>0)
    fit hits mate reached locations paths word copies bits full
  have boundCost := charges_install_mono cols m width f.board.batch.copies
    (fun i=>cost i+(if mask.eval m (i.val:Word w)=0 then 0 else (v.radius:ℝ)))
    (v.paidRate P z width r banks src tab dest owners m a)
    (fun i=>((tree i).map len).sum) (fun _=>v.cost.atAttempt a)
    (fun i=>((core i).map len).sum) (fun i=>v.coreCharge P z width a i 0)
    (fun _ : Fin f.pricedArea.rows=>0) (fun i : Fin f.pricedArea.rows=>v.openingCharge (m (B.boughtFields 5+i.val)).val)
    price treeCost routeCost
  have real := exactCost.le.trans boundCost
  cases a <;> exact real

/-- For feeds the nonzero coefficient is the genuine overflow and every hop
comes from the core walk of the commodity at its original row-major slot. -/
theorem receipt_feed {w : ℕ} (m : Memory w) (b : Boundary) (len : Fin P.catalogue.rows→ℝ)
    (paths : CommodityColumn→Traversals)
    (walk : Fin (FeedLayout.lanes N k*2^z)→List (Fin P.catalogue.rows)) :
    let L:=FeedLayout.atEvent («N»:=N) v.mesh (v.privateArena P z width) fmt P.joint.initial width v.keepLimit b
    (∀l : Fin (FeedLayout.lanes N k),(paths (L.column l)).Reads m (fun i : Fin (2^z)=>walk (finProdFinEquiv (l,i)))) →
    (∀i : FeedLayout.Good z N k,(m (L.overflow+PurchaseInventory.slot i)).val≠0 →
      ((walk (PurchaseInventory.slotEquiv z N k i)).map len).sum≤routeCap N v.radius (PurchaseInventory.lane i)) →
    (((L.columns.map (fun c=>c.paidSlice (paths c))).map (fun t=>t.toll m len width)).sum ≤ (rec m (.feed b)).install) := by
  intro L reads cost
  rw [L.installed_charge paths m width len walk reads]
  let price (j : Fin (PurchaseInventory.footprint z N k)) :=
    ((m (L.overflow+j.val)).val:ℝ)/width*((walk j).map len).sum
  have reindex : (∑ j : Fin (PurchaseInventory.footprint z N k), price j) =
      ∑ i : FeedLayout.Good z N k, price ((PurchaseInventory.slotEquiv z N k) i) :=
    ((PurchaseInventory.slotEquiv z N k).sum_comp price).symm
  refine reindex.le.trans ?_
  change (∑ i : FeedLayout.Good z N k, price ((PurchaseInventory.slotEquiv z N k) i)) ≤
    ∑ i : FeedLayout.Good z N k,
      ((m (L.overflow+PurchaseInventory.slot i)).val:ℝ)*routeCap N v.radius (PurchaseInventory.lane i)/width
  apply Finset.sum_le_sum
  intro i _
  change ((m (L.overflow+PurchaseInventory.slot i)).val:ℝ)/width*
      ((walk ((PurchaseInventory.slotEquiv z N k) i)).map len).sum ≤
    ((m (L.overflow+PurchaseInventory.slot i)).val:ℝ)*routeCap N v.radius (PurchaseInventory.lane i)/width
  rw [div_mul_eq_mul_div]
  by_cases zero : (m (L.overflow+PurchaseInventory.slot i)).val=0
  · simp [zero]
  · exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (cost i zero) (Nat.cast_nonneg _)) (Nat.cast_nonneg _)

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
