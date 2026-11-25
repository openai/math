import OAI.Hierarchy.ProtocolRAMCalendarEconomicStart

namespace OAI
/-! # Potential, payload and initial inventory for the same executed startup as all upper price pages -/

noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage ProbeStage.Native
open scoped Classical Fin.CommRing
variable {z d N k phases jobs w : ℕ}

structure InitialPrices (b : JointHeader.Board) (z N k : ℕ) (phase : Fin phases→PhasePrice)
    (stock : ℕ→ℕ) (m : Memory w) : Prop where
  scores : ∀i,GlobalTests.Resident (GlobalTests.page (JointHeader.scores b z N k) z N k i.val) z N k (phase i) m
  original : ∀i : Fin (GlobalTests.rows z N k),m (b.initial+i.val)=(stock i.val:Word w)

theorem start_prices (b : JointHeader.Board) (phase : Fin phases→PhasePrice) (π : Equiv.Perm (Fin (2^z)))
    (stock : ℕ→ℕ) (raw : Boot.Tape z d) (markets : Fin jobs→Market z d k) {size : ℕ}
    (layout : Boot.Layout markets size) (hd : 1≤d) (first : 2^z≤b.initial) (heap : heapEnd z d copies≤b.initial)
    (within : JointHeader.stop b z N k phases≤ size) (before : ∀i,JointHeader.stop b z N k phases≤Boot.low (markets i)) :
    InitialPrices b z N k phase stock (Boot.booted markets size (JointHeader.words b z d N k phase π stock raw)) := by
  refine ⟨JointHeader.score_origin b phase π stock raw markets layout hd first heap within before,?_⟩
  intro i
  have low:=Nat.add_lt_add_left i.isLt b.initial
  have fit:=low.trans_le (JointHeader.order b z N k)
  exact (JointHeader.low_origin b phase π stock raw markets layout hd first within before _ (heap.trans (Nat.le_add_right ..)) fit).trans
    ((JointHeader.below_scores b phase π stock raw _ fit).symm.trans (JointHeader.initial_stock b phase π stock raw i))

theorem InitialPrices.empty {b : JointHeader.Board} {phase : Fin phases→PhasePrice} {m : Memory w}
    (start : InitialPrices b z N k phase (fun _=>0) m) (i : GlobalTests.Goods z N k) :
    (m (b.initial+PurchaseInventory.slot i)).val=0 := by
  exact congrArg Fin.val (start.original (PurchaseInventory.slotEquiv z N k i))

end Hierarchy.ProtocolRAM.Calendar
end

end OAI
