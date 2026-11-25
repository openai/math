import OAI.Hierarchy.DescentPackSelectionCounters

namespace OAI
/-! # Physical capacity differences equal the number of earlier units in the chosen bin -/

namespace Hierarchy.DescentPacking.SelectionTrace
open FirstFitRAM PairRAM ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open scoped BigOperators Classical Fin.CommRing
noncomputable section
variable {w : ℕ} {I V : Type*} [Fintype V] [DecidableEq V]

theorem remaining {p : Layout} (amount : I→ℕ) (xs : List I) (cap : V→ℕ) (m : Memory w)
    (room : Room w (Fintype.card V) p) (fits : xs.length≤p.slots)
    (values : capacityWords p.caps cap m) (bounded : ∀v,cap v < 2^w)
    (input : ∀i : Fin xs.length,m (p.need+i.val)=(amount (xs.get i):Word w))
    (widths : ∀i∈xs,amount i < 2^w) (j : Fin xs.length) (v : V) :
    final p (Fintype.card V) m (capacityBase p.bits p.caps j.val+(Fintype.equivFin V v).val)=
      ((pack amount (xs.take j.val) cap).remaining v:Word w) := by
  let n := Fintype.card V
  let x := capacityBase p.bits p.caps j.val+(Fintype.equivFin V v).val
  have before : x < capacityBase p.bits p.caps xs.length := by
    have mul := Nat.mul_le_mul_right (2^p.bits+1) (Nat.succ_le_of_lt j.isLt)
    have enough := (Fintype.equivFin V v).isLt.trans_le room.bins
    simp only [Nat.succ_mul] at mul
    dsimp [x,capacityBase]
    omega
  have whole := Nat.mul_le_mul_right (2^p.bits+1) fits
  have hi := room.reserve
  have end_ := room.end_
  have done : capacityBase p.bits p.caps xs.length+n < 2^w := by
    have := room.bins
    dsimp [n,capacityBase,Prefix.base] at *
    omega
  have historyEnd : capacityBase p.bits p.caps xs.length ≤ capacityBase p.bits p.caps p.slots :=
    Nat.add_le_add_left whole p.caps
  have beforeOffsets : x < p.offsets :=
    ((before.trans_le historyEnd).trans_le (Nat.le_add_right ..)).trans_le
      ((Nat.le_add_right ..).trans room.reserve)
  have kept := Prefix.issued_frame n p.amount p.tag p.offsets p.slots (first p n m) x beforeOffsets
  apply kept.trans
  rw [first_taken n m xs.length fits]
  apply (history_before n p.bits p.caps p.amount _ xs.length (p.slots-xs.length) x before).trans
  apply remaining_read p.bits p.caps p.amount amount xs cap m room.bins (Layout.need_low room) done values bounded
    (fun i=>by simpa [Layout.amount,Layout.index,i.isLt.trans_le fits] using input i) widths j.val j.isLt.le v

theorem balance {p : Layout} (amount : I→ℕ) (xs : List I) (cap : V→ℕ) (m : Memory w)
    (room : Room w (Fintype.card V) p) (fits : xs.length≤p.slots)
    (values : capacityWords p.caps cap m) (bounded : ∀v,cap v < 2^w)
    (input : ∀i : Fin xs.length,m (p.need+i.val)=(amount (xs.get i):Word w))
    (widths : ∀i∈xs,amount i < 2^w) (j : Fin xs.length) (v : V) :
    cap v-(final p (Fintype.card V) m (capacityBase p.bits p.caps j.val+(Fintype.equivFin V v).val)).val=
      ∑i : Locations (pack amount xs cap).decisions,if i.val < j.val ∧
        ((pack amount xs cap).decisions.get i).2=some v then amount ((pack amount xs cap).decisions.get i).1 else 0 := by
  have small : (pack amount (xs.take j.val) cap).remaining v < 2^w := by
    have := (pack amount (xs.take j.val) cap).account v
    have := bounded v
    omega
  rw [remaining amount xs cap m room fits values bounded input widths j v,Fin.val_cast_of_lt small]
  exact used_prefix amount xs cap j.val v

end
end Hierarchy.DescentPacking.SelectionTrace

end OAI
