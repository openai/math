import OAI.Hierarchy.ProtocolRAMStoredPurchaseCount
import OAI.Hierarchy.ProbeLiveSlots
import OAI.Hierarchy.ProtocolRAMPurchaseMarketDensity
import OAI.Hierarchy.ProbePurchasedOccurrence

namespace OAI
/-! # Counting retained typed chains in the native purchase decision table -/

namespace Hierarchy.ProtocolRAM.PurchaseFrozen.Shelf

open Computability.VPVNP.BurstRAM PrivateRAM ProbeStage ProbeStage.Native
open scoped Fin.CommRing BigOperators Classical
noncomputable section
variable {z d k : ℕ}

/-- Specialization to the packed words in the memory returned by the native run. -/
theorem packedCount_liveChains_result (sh : Shelf) (S : PurchaseSampler) (π : Equiv.Perm (Fin (2^z)))
    (depth : ℕ) (hd : 1≤ d) (phase : PhasePrice) (T : ℝ) (kind : ℕ) (frozen fixture : Mem z d)
    (input : sh.Incoming (k:=k) S π depth phase T kind frozen)
    (prepared : ∀ i : Key z d k, sh.Prepared S depth fixture i frozen)
    (room : sh.flagsBase S z d k depth+count z d k*paths z S.degree depth<2^wordBits z d copies) :
    sh.packedCount S k depth (sh.result S k depth frozen) =
      Fintype.card (LiveChains S π depth (StripDirectory.actualMarks sh phase T kind frozen (k:=k))) := by
  obtain ⟨_,_,_,words⟩ := sh.run S π depth hd phase T kind frozen fixture input prepared room
  exact sh.packedCount_liveChains S π depth phase T kind frozen _ words

/-- A calendar entry carries signed purchase marks exactly when its native mode is three. -/
def catalogueMarks (mode : ℕ) (sh : Shelf) (phase : PhasePrice) (T : ℝ) (kind : ℕ)
    (frozen : Mem z d) : StageAt z d → Fin k × Bool → Finset (Fin (2^z)) :=
  if mode=3 then StripDirectory.actualMarks sh phase T kind frozen else fun _ _ => ∅

theorem catalogueMarks_buy (mode : ℕ) (sh : Shelf) (phase : PhasePrice) (T : ℝ) (kind : ℕ)
    (frozen : Mem z d) (buy : mode=3) :
    catalogueMarks (k:=k) mode sh phase T kind frozen = StripDirectory.actualMarks sh phase T kind frozen := by
  simp [catalogueMarks,buy]

/-- Every purchased chain uses `depth+1` marked tiles. Thus an idle calendar
entry has no live chains, including when the depth is zero. -/
theorem card_liveChains_idle (mode : ℕ) (sh : Shelf) (S : PurchaseSampler)
    (π : Equiv.Perm (Fin (2^z))) (depth : ℕ) (phase : PhasePrice) (T : ℝ) (kind : ℕ)
    (frozen : Mem z d) (idle : mode≠3) :
    Fintype.card (LiveChains S π depth (catalogueMarks (k:=k) mode sh phase T kind frozen)) = 0 := by
  have noneKept (t : StageAt z d) : (advisedPurchases S π t depth ∅).1.length=0 := by
    let shape := stageAt z d t
    let choices := ProtocolRAMPurchaseOwners.successor (advisedStage z d π t)
      (Fintype.equivFin shape.Group).toEmbedding (D:=S.degree) (AdaptiveProbe.portDigits (S.rows shape.span))
    have account := (PurchaseDFS.purchase_spec choices depth (∅ : Finset (Fin (2^z)))).2.2
    rw [Finset.card_empty] at account
    change (advisedPurchases S π t depth ∅).1.length*(depth+1)+
      (advisedPurchases S π t depth ∅).2.card=0 at account
    have zero : (advisedPurchases S π t depth ∅).1.length*(depth+1)=0 := by omega
    exact (Nat.mul_eq_zero.mp zero).resolve_right (Nat.succ_ne_zero depth)
  rw [liveChain_card]
  simp [liveCount,catalogueMarks,idle,noneKept]

end
end Hierarchy.ProtocolRAM.PurchaseFrozen.Shelf

end OAI
