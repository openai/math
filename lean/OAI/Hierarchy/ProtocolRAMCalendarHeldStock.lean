import OAI.Hierarchy.ProtocolRAMCalendarHeld
import OAI.Hierarchy.ProtocolRAMCalendarFeedPurchase
import OAI.Hierarchy.ProtocolRAMCalendarFeedStock

namespace OAI
/-! # Conservation of native stock and the undelivered part of a scheduled reserve -/

namespace Hierarchy.ProtocolRAM.Calendar
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe
open scoped Fin.CommRing
noncomputable section
variable {w q d h N k : ℕ}

namespace FeedLayout
variable (L : FeedLayout h N k)

/-- Exact site transport for a payload injection or a subsequent cooling tick.
Both newly active stock and paid spill are read at the physical commodity slot. -/
theorem outer_balance (C : Chart w q d) (p : ℕ) (m : Memory w) (i : Good h N k)
    (record : let bits := PurchaseInventory.stock L.active m i+
        if p<C.mesh.inject then slice C.mesh.inject L.width p*payloadUnit i else 0
      let out := after C (.feed (.outer p)) m
      (out (L.kept+PurchaseInventory.slot i)).val=min bits (L.cap*L.width) ∧
      (out (L.overflow+PurchaseInventory.slot i)).val=bits-min bits (L.cap*L.width)) :
    let out := after C (.feed (.outer p)) m
    held C.mesh.inject L.width p*payloadUnit i+PurchaseInventory.stock L.active m i=
      held C.mesh.inject L.width (p+1)*payloadUnit i+
        (out (L.kept+PurchaseInventory.slot i)).val+(out (L.overflow+PurchaseInventory.slot i)).val := by
  dsimp only at record ⊢
  rw [record.1,record.2]
  have move := congrArg (·*payloadUnit i) (held_step C.mesh.inject L.width p)
  rw [Nat.add_mul] at move
  by_cases live : p<C.mesh.inject <;> simp only [live,ite_true,ite_false,Nat.zero_mul] at move ⊢ <;> omega

/-- The saved table remains immutable through all reserve repairs. Its gated
logical balance decreases exactly by the word injected into the active bank. -/
theorem inner_balance (C : Chart w q d) (p a j : ℕ) (m : Memory w) (i : Good h N k)
    (index : j<C.mesh.reserveSteps)
    (record : let bits := PurchaseInventory.stock L.active m i+
        (if (m (C.modeAt (.outer p a)) = 3) then slice C.mesh.reserveSteps (PurchaseInventory.stock L.saved m i) j else 0)
      let out := after C (.feed (.inner p a j)) m
      (out (L.kept+PurchaseInventory.slot i)).val=min bits (L.cap*L.width) ∧
      (out (L.overflow+PurchaseInventory.slot i)).val=bits-min bits (L.cap*L.width)) :
    let out := after C (.feed (.inner p a j)) m
    let reserve := PurchaseInventory.stock L.saved m i
    let pending := fun t => if (m (C.modeAt (.outer p a)) = 3) then held C.mesh.reserveSteps reserve t else 0
    pending j+PurchaseInventory.stock L.active m i=
      pending (j+1)+(out (L.kept+PurchaseInventory.slot i)).val+(out (L.overflow+PurchaseInventory.slot i)).val := by
  dsimp only at record ⊢
  rw [record.1,record.2]
  have move := held_step C.mesh.reserveSteps (PurchaseInventory.stock L.saved m i) j
  rw [ite_eq_left index] at move
  by_cases buy : m (C.modeAt (.outer p a))=3 <;> simp only [buy,ite_true,ite_false] <;> omega

end FeedLayout
namespace StockCommit

/-- The original RAM stock equals the newly active and held words after the
one physical buy split, including odd widths. -/
theorem buy_balance (a : Area) (s : Sources) (g : LabelSource) (b : Batch q d)
    (m : Memory w) (i : Fin a.goods)
    (record : let out := (pricedSegment a s g w b).after m
      let old := (m (s.old.base+i.val)).val
      (out (a.output+i.val)).val=old/2 ∧ (out (a.output+a.goods+i.val)).val=old-old/2 ∧
        out (a.output+a.goods+a.goods+i.val)=0) :
    let out := (pricedSegment a s g w b).after m
    (m (s.old.base+i.val)).val=(out (a.output+i.val)).val+(out (a.output+a.goods+i.val)).val ∧
      out (a.output+a.goods+a.goods+i.val)=0 := by
  dsimp only at record ⊢
  exact ⟨by rw [record.1,record.2.1]; omega,record.2.2⟩

end StockCommit
end
end Hierarchy.ProtocolRAM.Calendar

end OAI
