import OAI.Hierarchy.ProbeFixedPostedBills

namespace OAI
/-! # The signed receipt printed by each event of the fixed protocol -/

noncomputable section
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

/-- Both signs of a packet coordinate use the same archived role and price word.
The lane classified as a catalyst uses the price of its two radial edges. -/
def paidRate {w : ℕ} (m : Memory w) (a : Attempt) (i : Fin (fmt a).pricedArea.occurrences) : ℝ :=
  let label := (fmt a).labelSource sink P.catalogue.idBase (StripChart.header F bank a).fieldTerm (StripChart.id F bank P.catalogue a)
  v.printedCharge P z width a i (m (label.out+i.val)).val

/-- Direct installations, selector broadcasts, ordinary inventory overflow,
purchase flags, and released catalyst bits are read at their original addresses. -/
def attemptReceipt {w : ℕ} (m : Memory w) (a : Attempt) : Charges :=
  let f:=fmt a
  let B:=repair C a
  let c:=(fresh f.pricedArea f.stockSource).eventColumns B.purchaseOut
  charges c f.pricedArea.occurrences f.pricedArea.rows f.pricedArea.goods f.pricedArea.rows m width
    f.board.batch.copies (v.paidRate P z width r banks src tab dest owners m a)
    (fun _=>v.cost.atAttempt a) (fun i=>v.coreCharge P z width a i 0)
    (fun i=>v.openingCharge (m (B.boughtFields 5+i.val)).val)

/-- Reserve attempts can install and debit ordinary widths. They can never open
a fresh path. This definition also gives zero opening to unexecuted reserve indices. -/
def receipts {w : ℕ} (m : Memory w) : Event→Charges
  | .attempt a =>
    let receipt:=v.attemptReceipt P z width r banks src tab dest owners m a
    match a with
    | .outer _ _ => receipt
    | .inner _ _ _ _ => {receipt with opening:=0}
  | .feed b =>
    let L:=FeedLayout.atEvent («N»:=N) v.mesh (v.privateArena P z width) fmt P.joint.initial width v.keepLimit b
    ⟨∑i : FeedLayout.Good z N k,((m (L.overflow+PurchaseInventory.slot i)).val:ℝ)*
      routeCap N v.radius (PurchaseInventory.lane i)/width,0,0⟩

local notation "rec" => v.receipts P z width r banks src tab dest owners
local notation "issued" => v.issued P z width r banks src tab dest owners

theorem receipt_bill {w : ℕ} (m : Memory w) (e : Event) (positive : 0<width)
    (debit : ∀a, e=.attempt a → ∀i : Fin (fmt a).pricedArea.occurrences,
      (m ((fmt a).pricedArea.direct+(fmt a).pricedArea.occurrences+i.val)).val≠0 →
      v.paidSupply z a (v.occurrencePort P z width a i).val=true)
    (reserve : ∀u a j b, e=.attempt (.inner u a j b) → ∀i : Fin (fmt (.inner u a j b)).pricedArea.rows,
      (m ((repair C (.inner u a j b)).purchaseOut+i.val)).val=0) :
    (issued e).bill width m=(rec m e).net v.radius width := by
  cases e with
  | feed b =>
    apply spillRows_bill
  | attempt a =>
    let f:=fmt a
    let B:=repair C a
    let L:=f.labelSource sink P.catalogue.idBase (StripChart.header F bank a).fieldTerm (StripChart.id F bank P.catalogue a)
    have h : (issued (.attempt a)).bill width m=(v.attemptReceipt P z width r banks src tab dest owners m a).net v.radius width := by
      apply reportedRows_bill f.pricedArea f.stockSource L B (fun _=>0) width f.board.batch.copies v.radius
        (v.printedCharge P z width a) (fun _ _=>v.cost.atAttempt a) (v.coreCharge P z width a) (fun _=>v.openingCharge)
        m (v.paidRate P z width r banks src tab dest owners m a) positive
      · intro _ _;rfl
      · intro i hi
        exact v.supply_price P z width a i _ (debit a rfl i hi)
    cases a with
    | outer u a => exact h
    | inner u a j b =>
      have none : (v.attemptReceipt P z width r banks src tab dest owners m (.inner u a j b)).opening=0 := by
        change (∑i : Fin (fmt (.inner u a j b)).pricedArea.rows,
          ((m ((repair C (.inner u a j b)).purchaseOut+i.val)).val:ℝ)*_)=0
        exact Finset.sum_eq_zero (fun i _=>by rw [reserve u a j b rfl i];simp)
      simpa only [receipts,Charges.net,none] using h

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
