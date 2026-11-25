import OAI.Hierarchy.ProbeFixedBirthFees
import OAI.Hierarchy.ProtocolRAMCatalystArchiveDates
import OAI.Hierarchy.ProtocolRAMCatalystPurchasedOrigin

namespace OAI
/-! # Every negative catalyst word on the final invoice has a dated physical owner -/

noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe CatalystArchive ProbeStage ProbeStage.Native CoreBoard
open StripChart StripDirectory
open scoped BigOperators Classical Fin.CommRing
variable {F : Type*} [Field F] {k : ℕ} {p q Q σ Λ : ℝ}
  (v : FixedProtocolFormat F k p q Q σ Λ) (P : v.Placement) (z width r : ℕ)
  (banks : RouteSettlement.Banks) (src tab dest : ℕ) (owners : Bank)
local notation "W" => wordBits z (2^v.W) copies
local notation "fmt" => v.nativeFormats P z width
local notation "C" => v.nativeChart P z width r banks src tab dest owners
local notation "rec" => v.receipts P z width r banks src tab dest owners

/-- The base is the negative half of the original priced strip port column. -/
def releasedBase : Event→ℕ
  | .attempt a=>(fmt a).pricedArea.direct+(fmt a).pricedArea.occurrences
  | .feed _=>0

/-- Local readback for each original round and every real selector.
The physical packet width bound gives exact natural-number decoding. -/
theorem released_entry_word {count : ℕ} (L : OwnerLedger) (m : Memory W)
    (history : Dates C m L (v.releasedBase P z width) count width)
    (shape : ∀a,.attempt a∈events v.mesh→L.rows (.attempt a)=(fmt a).pricedArea.occurrences)
    (widthFits : width<2^W) (admitted : Calendar.mounted C (events (C).mesh) m) (a : Attempt) (live : .attempt a∈events v.mesh)
    (i : Fin (history a live).entry.rows) :
    ((run C (events (C).mesh) m) ((fmt a).pricedArea.direct+(fmt a).pricedArea.occurrences+i.val)).val=
      (history a live).entry.bits i := by
  let H:=history a live
  let ar:=(fmt a).pricedArea
  have countRows : H.entry.rows=ar.occurrences := H.shape.trans (shape a live)
  have onChart : Event.attempt a ∈ events (C).mesh := live
  obtain ⟨t,here⟩:=List.mem_iff_get.mp onChart
  have cut:=ordinal_slot C m t admitted
  change Slot C m ((events (C).mesh).get t) _ _ _ at cut
  rw [here] at cut
  have before : ar.direct+ar.occurrences+i.val<ar.stop := by
    have hi : i.val<ar.occurrences := i.isLt.trans_le countRows.le
    unfold StockCommit.Area.stop StockCommit.Area.output StockCommit.Area.excess StockCommit.Area.clip
      StockCommit.Area.src StockCommit.Area.broadcast
    omega
  have word:=v.attempt_word P z width r banks src tab dest owners m _ a _ _ cut _ before
  have entry : after C (.attempt a) (entryMemory C m a)
      (ar.direct+ar.occurrences+i.val)=(H.entry.bits i : Word W) := H.posted i
  have sameWord := congrArg (fun state : Memory W =>
    after C (.attempt a) state (ar.direct+ar.occurrences+i.val)) cut.entryMemory
  exact (congrArg Fin.val (word.trans (sameWord.symm.trans entry))).trans
    (Fin.val_cast_of_lt ((H.entry.fits i).trans_lt widthFits))

set_option maxHeartbeats 1000000 in
theorem released_at_date {count : ℕ} (L : OwnerLedger) (m : Memory W)
    (history : Dates C m L (v.releasedBase P z width) count width)
    (shape : ∀a,.attempt a∈events v.mesh→L.rows (.attempt a)=(fmt a).pricedArea.occurrences)
    (widthFits : width<2^W) (admitted : Calendar.mounted C (events (C).mesh) m) (a : Attempt) (live : .attempt a∈events v.mesh) :
    (rec (run C (events (C).mesh) m) (.attempt a)).releasedBits =
      ∑ j : Fin (history a live).entry.rows,(history a live).entry.bits j := by
  have receipt (mem : Memory W) (event : Attempt) :
      (rec mem (.attempt event)).releasedBits =
        ∑ j : Fin (fmt event).pricedArea.occurrences,
          (mem ((fmt event).pricedArea.direct+(fmt event).pricedArea.occurrences+j.val)).val := by
    have openingOnly (which : Attempt) (c : Charges) :
        (match which with
         | .outer _ _ => c
         | .inner _ _ _ _ => {c with opening := 0}).releasedBits = c.releasedBits := by
      cases which <;> rfl
    calc
      _ = (v.attemptReceipt P z width r banks src tab dest owners mem event).releasedBits := by
        exact openingOnly event (v.attemptReceipt P z width r banks src tab dest owners mem event)
      _ = _ := by
        simp only [attemptReceipt, Calendar.charges, StockCommit.eventColumns, StockCommit.fresh]
  have sumRows {n t : ℕ} (same : t=n) (f : Fin n → ℕ) (g : Fin t → ℕ)
      (point : ∀ i, f (Fin.cast same i)=g i) : (∑ j, f j)=∑ i, g i := by
    cases same
    exact Finset.sum_congr rfl fun i _ => point i
  let H:=history a live
  let ar:=(fmt a).pricedArea
  let rv:=run C (events (C).mesh) m
  have countRows : H.entry.rows=ar.occurrences := H.shape.trans (shape a live)
  exact (receipt rv a).trans (sumRows countRows
    (fun j : Fin ar.occurrences => (rv (ar.direct+ar.occurrences+j.val)).val) H.entry.bits
    (fun i => v.released_entry_word P z width r banks src tab dest owners L m history shape widthFits admitted a live i))

/-- Every dated position required by the native reserve scatter is exactly its
line on the signed financial invoice, including zero-arity boundary feeds. -/
theorem released_clock {count : ℕ} (L : OwnerLedger) (m : Memory W)
    (history : Dates C m L (v.releasedBase P z width) count width)
    (shape : ∀a,.attempt a∈events v.mesh→L.rows (.attempt a)=(fmt a).pricedArea.occurrences)
    (widthFits : width<2^W) (admitted : Calendar.mounted C (events (C).mesh) m) (t : Fin (events v.mesh).length) :
    (rec (run C (events (C).mesh) m) ((events v.mesh).get t)).releasedBits=
      ∑j,(atTime v.mesh (CatalystArchive.issued history) t).bits j := by
  let total (e : CatalystArchive.Entry count width) : ℕ := ∑ j, e.bits j
  have charge (event : Event) (member : event ∈ events v.mesh) :
      (rec (run C (events (C).mesh) m) event).releasedBits =
        total (eventEntry (CatalystArchive.issued history) event) := by
    cases event with
    | feed b => simp [total, eventEntry, noneEntry, receipts]
    | attempt a =>
      have actual : Event.attempt a ∈ events (C).mesh := member
      have entry : CatalystArchive.issued history a = (history a actual).entry := by
        unfold CatalystArchive.issued
        rw [dite_eq_left actual]
      exact (v.released_at_date P z width r banks src tab dest owners L m history shape
        widthFits admitted a member).trans (congrArg total entry.symm)
  exact charge ((events v.mesh).get t) ((events v.mesh).get_mem t)

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
