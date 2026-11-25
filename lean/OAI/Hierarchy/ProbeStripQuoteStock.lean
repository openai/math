import OAI.Hierarchy.ProbeStripScore
import OAI.Hierarchy.ProtocolRAMCalendarGlobalCalibration

namespace OAI
/-! # The phase quote reads shared with the two preceding global tests -/

noncomputable section
namespace Hierarchy.ProtocolRAM.StripDirectory
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe AttemptGate Calendar Calendar.GlobalTests
open scoped Classical Fin.CommRing

variable {z N k w : ℕ}

theorem QuoteCells.ofStock {A : AccountColumns (Goods z N k)} {x : Inventory (Goods z N k)}
    {l : Layout} {stocks : Bank} {s : PhasePrice} {m : Memory w} (R : ReadStock A x l stocks s m)
    (prices : Bank) (rom : ∀ (i : Fin (kinds N k)) (n : Fin l.stride),
      prices.read m ((i.val*l.stride+n.val:ℕ):Word w)=(s.word i.val n.val:Word w)) :
    QuoteCells s m prices (offsets l) stocks PurchaseInventory.slot PurchaseInventory.lane x.bits l.stride := by
  let e := PurchaseInventory.slotEquiv z N k
  have atRow (c : Goods z N k) : (e c).val=PurchaseInventory.slot c := rfl
  have rowKind (c : Goods z N k) : (kind (e c)).val=PurchaseInventory.lane c := by
    dsimp only [kind]
    rw [show (PurchaseInventory.slotEquiv z N k).symm (e c)=c from e.symm_apply_apply c]
  have tableBits (c : Goods z N k) : (m (stocks.base+(e c).val)).val=x.bits c := by
    simpa only [show (PurchaseInventory.slotEquiv z N k).symm (e c)=c from e.symm_apply_apply c] using R.bits (e c)
  constructor
  · intro c
    have read := R.resident.off (e c)
    have inside : (e c).val < (offsets l).size := (e c).isLt.trans_le R.rowCap
    unfold Bank.read
    rw [←atRow c,Fin.val_cast_of_lt ((e c).isLt.trans R.rowRoom),Nat.mod_eq_of_lt inside,
      ←rowKind c]
    exact read
  · intro c
    unfold Bank.read
    rw [←atRow c,Fin.val_cast_of_lt ((e c).isLt.trans R.rowRoom),Nat.mod_eq_of_lt ((e c).isLt.trans_le R.stockCap),
      ←tableBits c,Fin.cast_val_eq_self]
  · intro c
    let j : Fin (kinds N k) := ⟨PurchaseInventory.lane c,PurchaseInventory.lane_lt _⟩
    let n : Fin l.stride := ⟨x.bits c,(tableBits c) ▸ (R.limit (e c))⟩
    exact rom j n

/-- Mount exactly the true finite phase-price table. Subsequent admissible
writes can be outside its physical span, leaving this read unchanged. -/
theorem priceROM (s : PhasePrice) (price : Bank) (kinds stride : ℕ) (base : Memory w)
    (room : kinds*stride<2^w) (cap : kinds*stride≤price.size)
    (i : Fin kinds) (n : Fin stride) :
    price.read (s.advice price kinds stride base) ((i.val*stride+n.val:ℕ):Word w) =
      (s.word i.val n.val:Word w) := by
  exact s.read_advice price kinds stride i.val n.val base i.isLt n.isLt room cap

end Hierarchy.ProtocolRAM.StripDirectory
end

end OAI
