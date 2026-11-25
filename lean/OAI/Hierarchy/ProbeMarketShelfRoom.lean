import OAI.Hierarchy.ProtocolRAMPurchaseCapacity
import OAI.Hierarchy.ProtocolRAMCalendarMarketShape
import OAI.Hierarchy.ProbeStageTemplateSize

namespace OAI
/-! # Readiness of the sampler on its actual calendar shelf -/

namespace Hierarchy.ProtocolRAM.Calendar.Boot
open ProbeStage ProbeStage.Native PurchaseCT PurchaseFrozen
open scoped Classical
noncomputable section
variable {z d k : ℕ}

/-- Every true stage fits the address word, using its actual template and
the bound on the total number of sockets. -/
theorem stage_span_room (hd : 1 ≤ d) (t : StageAt z d) :
    (stageAt z d t).span ≤ 2^(wordBits z d copies) := by
  let s := stageAt z d t
  let : Nonempty s.Group := ⟨(advisedStage z d (Equiv.refl _) t).group 0⟩
  have size := (template_dyadic hd s (List.get_mem ..)).2
  have one : 1 ≤ Fintype.card s.Group := Fintype.card_pos
  have count : s.span ≤ Fintype.card s.Group*s.span := Nat.le_mul_of_pos_left _ one
  have cap : 4^(rounds d+1)*2^z=extent z d := (room_slots z d).symm
  exact (count.trans (size.trans cap.le)).trans (extent_word z d copies).le

/-- The attached bank contains exactly one word per input ordinal in every
stage and direction. Its address is resolved anew at every date. -/
theorem shelf_stock_end (m : Market z d k)
    (inv : m.shelf.stockBase+PurchaseInventory.footprint z (2*rounds d+1) k ≤ m.shelf.thresholdBase)
    (table : m.shelf.table.base+m.shelf.table.size ≤ m.shelf.firstBase) (t : StageAt z d) (j : Fin (2*k)) :
    (m.shelf.stock t j).base+(m.shelf.stock t j).size ≤ m.shelf.firstBase :=
  (stock_end m.shelf.stockBase z (stageNumber t) j).trans (inv.trans ((Nat.le_add_right ..).trans table))

/-- The actual threshold, incoming stock, CT columns, sampler scratch and
per-ball output all occupy the named finite ranges on this market. -/
theorem shelf_dimensions (m : Market z d k) (hd : 1 ≤ d)
    (heap : heapEnd z d copies ≤ m.shelf.stockBase)
    (inv : m.shelf.stockBase+PurchaseInventory.footprint z (2*rounds d+1) k ≤ m.shelf.thresholdBase)
    (table : m.shelf.table.base+m.shelf.table.size ≤ m.shelf.firstBase)
    (endAt : m.flags+m.rows<2^wordBits z d copies)
    (directions : 2*k<2^wordBits z d copies) (degree : m.sampler.degree ≤ 2^wordBits z d copies) (i : Key z d k) :
    Ready m.sampler (stage i) (m.shelf.cfg m.sampler m.depth i) := by
  have after := heap.trans ((Nat.le_add_right ..).trans inv)
  have head : m.shelf.firstBase ≤ m.flags := by
    unfold Market.flags Shelf.flagsBase
    omega
  have threshold : m.shelf.thresholdBase+m.shelf.table.size ≤ m.shelf.firstBase := table
  have raw := (root_extent (z:=z) (d:=d)).trans after
  have small : 2^z<2^wordBits z d copies := by omega
  have banksBound (c : Fin 3) :
      (stageBank z d (stageNumber (stage i)) c).Fits (wordBits z d copies) m.shelf.firstBase := by
    have last := stageBank_end z d (stageNumber (stage i)) c
    have size : (stageBank z d (stageNumber (stage i)) c).size=2^z := by
      simp only [Bank.size,stageBank_bits]
    exact ⟨Nat.two_pow_pos _,size.trans_lt small,last.trans (by omega)⟩
  apply m.shelf.ready m.sampler m.depth i hd after raw _ _
    ⟨banksBound 0,banksBound 1,banksBound 2⟩
    (by rw [wordBits_linear];omega) directions degree (stage_span_room hd _) endAt
  · intro j
    exact ⟨heap.trans (Nat.le_add_right ..),Nat.two_pow_pos _,small,
      (stock_end m.shelf.stockBase z (stageNumber (stage i)) j).trans inv⟩
  · exact ⟨Nat.two_pow_pos _,by omega,table⟩

end
end Hierarchy.ProtocolRAM.Calendar.Boot

end OAI
