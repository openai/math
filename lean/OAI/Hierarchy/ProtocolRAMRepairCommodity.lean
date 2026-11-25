import OAI.Hierarchy.ProtocolRAMPurchaseInventory
import OAI.Hierarchy.ProtocolRAMRepairCommit

namespace OAI
/-! # The same physical commodity index for signed-mark reading, repair, and pricing -/

namespace Hierarchy.ProtocolRAM.PurchaseInventory
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe
open scoped BigOperators Classical Fin.CommRing
noncomputable section

variable {w h N k n : ℕ}

theorem card_commodity (h N k : ℕ) : Fintype.card (Commodity (Fin (2^h)) N k)=footprint h N k := by
  simp [Commodity,footprint,Fintype.card_sum,Fintype.card_prod]
  ring

/-- These are precisely the offsets used by the live signed-stock bank, including the
leading payload lane. Every physical slot is the balance of one genuine commodity. -/
def slotEquiv (h N k : ℕ) : Commodity (Fin (2^h)) N k ≃ Fin (footprint h N k) :=
  let f := fun c => (⟨slot c,slot_lt c⟩ : Fin (footprint h N k))
  Equiv.ofBijective f ((Fintype.bijective_iff_injective_and_card f).2
    ⟨fun _ _ e => slot_injective (congrArg Fin.val e),(card_commodity h N k).trans (Fintype.card_fin _).symm⟩)

@[simp] theorem slotEquiv_val (c : Commodity (Fin (2^h)) N k) : (slotEquiv h N k c).val=slot c := rfl

def repairKind (bank : Bank) (p : RepairHistogram.Columns) (m : Memory w) (e : Fin n) :
    Option (Commodity (Fin (2^h)) N k) :=
  (RepairHistogram.kind (goods:=footprint h N k) bank p m e).map (slotEquiv h N k).symm

theorem repairKind_iff (bank : Bank) (p : RepairHistogram.Columns) (m : Memory w) (e : Fin n)
    (c : Commodity (Fin (2^h)) N k) : repairKind bank p m e=some c ↔
    RepairHistogram.kind bank p m e=some (slotEquiv h N k c) := by
  cases htag : RepairHistogram.kind (goods:=footprint h N k) bank p m e with
  | none => simp [repairKind,htag]
  | some j => simp [repairKind,htag,Equiv.symm_apply_eq]

theorem resource_commodity (bank : Bank) (p : RepairHistogram.Columns) (m : Memory w) (bits : Fin n → ℕ)
    (c : Commodity (Fin (2^h)) N k) : OuterBank.resourceBits (repairKind bank p m) bits c =
      OuterBank.resourceBits (RepairHistogram.kind bank p m) bits (slotEquiv h N k c) := by
  unfold OuterBank.resourceBits
  apply Finset.sum_congr rfl
  intro e _
  by_cases tagged : RepairHistogram.kind (goods:=footprint h N k) bank p m e=some (slotEquiv h N k c)
  · rw [ite_eq_left ((repairKind_iff bank p m e c).2 tagged),ite_eq_left tagged]
  · rw [ite_eq_right (fun eq=>tagged ((repairKind_iff bank p m e c).1 eq)),ite_eq_right tagged]

theorem commodity_balance (s : RepairHistogram.CommitPlan) (p : RepairHistogram.Columns) (n : ℕ) (m : Memory w)
    (c : Commodity (Fin (2^h)) N k) (sep : s.bank.base+footprint h N k≤ s.src)
    (funded : OuterBank.resourceBits (repairKind s.bank p m) (RepairHistogram.consumedBits (n:=n) p m) c≤ stock s.bank.base m c)
    (room : stock s.bank.base m c+OuterBank.resourceBits (repairKind s.bank p m) (RepairHistogram.installedBits (n:=n) p m) c<2^w) :
    stock s.bank.base m c+OuterBank.resourceBits (repairKind s.bank p m) (RepairHistogram.installedBits (n:=n) p m) c=
      RepairHistogram.raw s.bank p s.src n m (slotEquiv h N k c)+
      OuterBank.resourceBits (repairKind s.bank p m) (RepairHistogram.consumedBits (n:=n) p m) c := by
  simp only [resource_commodity,stock] at funded room ⊢
  exact RepairHistogram.balance s.bank p s.src n m (slotEquiv h N k c) sep funded room

theorem commodity_retained (s : RepairHistogram.CommitPlan) (p : RepairHistogram.Columns) (m : Memory w)
    (ready : RepairHistogram.CommitReady p s w n (footprint h N k) m) (c : Commodity (Fin (2^h)) N k)
    (wide : 4≤2^w) (payload cap : ℕ) (limit : s.limit=cap*payload) (room : s.limit<2^w)
    (excess : s.excess.base=s.clip.base+footprint h N k) (clipCap : footprint h N k≤ s.clip.size)
    (excessCap : footprint h N k≤ s.excess.size) (bankCap : footprint h N k≤ s.bank.size)
    (mode : (s.mode.eval (RepairHistogram.beforeTransfer p s n (footprint h N k) m) (slot c:Word w)).val=2) :
    stock s.activeOut (RepairHistogram.commitOut p s n (footprint h N k) m) c =
      min (RepairHistogram.raw s.bank p s.src n m (slotEquiv h N k c)) (cap*payload) :=
  (RepairHistogram.commit_repair p s m ready (slotEquiv h N k c) wide payload cap limit room excess
    clipCap excessCap bankCap mode).1

theorem repairKind_none (bank : Bank) (p : RepairHistogram.Columns) (m : Memory w) (e : Fin n) :
    repairKind (h:=h) (N:=N) (k:=k) bank p m e=none ↔
      RepairHistogram.kind (goods:=footprint h N k) bank p m e=none := by
  cases native : RepairHistogram.kind (goods:=footprint h N k) bank p m e <;> simp [repairKind,native]

theorem commodity_cash (s : RepairHistogram.CommitPlan) (p : RepairHistogram.Columns) (m : Memory w)
    (unit price : Fin n → ℝ) (bc : ℝ) :
    cashChange (repairKind (h:=h) (N:=N) (k:=k) s.bank p m) unit price bc =
      cashChange (RepairHistogram.kind (goods:=footprint h N k) s.bank p m) unit price bc := by
  simp only [cashChange,repairKind_none]

theorem pairing_slots (x y : Fin (footprint h N k) → ℝ) :
    pairing (fun c => x (slotEquiv h N k c)) (fun c => y (slotEquiv h N k c)) = pairing x y :=
  (slotEquiv h N k).sum_comp (fun j => x j*y j)

/-- Reindex both the signed direct bill and the clipped excess back onto the payload
and signed-altimeter commodities used by the nonlinear account. -/
theorem commodity_paid {rows : ℕ} {E : Type*} (s : RepairHistogram.CommitPlan) (p : RepairHistogram.Columns)
    (m : Memory w) (payload cap : ℕ) (cash : ℝ) (price : Fin n → ℝ) (bc : Fin rows → ℝ)
    (walk : Fin (footprint h N k) → List E) (len : E → ℝ) (box : Fin (footprint h N k) → ℝ)
    (ordinary : ∀ i,((walk i).map len).sum≤box i) (covered : (Expr.lookup s.bank .row).inputEnd≤ s.clip.base)
    (endFit : s.clip.base+footprint h N k+footprint h N k<2^w) (size : footprint h N k≤ s.bank.size)
    (bound : cap*payload<2^w) :
    RepairHistogram.postedCash p s.bank s.src n s.clip.base cap payload m cash price bc walk len ≤ cash+
      cashChange (repairKind (h:=h) (N:=N) (k:=k) s.bank p m)
        (netUnits payload (RepairHistogram.installedBits p m) (RepairHistogram.consumedBits p m))
        price ((∑r,bc r)/payload) +
      pairing (fun c => bitStock payload (spillBits cap payload (RepairHistogram.raw s.bank p s.src n m)) (slotEquiv h N k c))
        (fun c => box (slotEquiv h N k c)) := by
  rw [commodity_cash,pairing_slots]
  exact RepairHistogram.paid p s.bank s.src n s.clip.base cap payload m cash price bc walk len box ordinary
    covered endFit size bound

end
end Hierarchy.ProtocolRAM.PurchaseInventory

end OAI
