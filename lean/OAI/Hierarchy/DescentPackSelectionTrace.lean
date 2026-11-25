import OAI.Hierarchy.DescentWholePackPrefix
import OAI.Hierarchy.DescentMatchedPrefixRAM

namespace OAI
/-! # Width-bounded packing and immutable source, decision and offset receipts -/

namespace Hierarchy.DescentPacking.SelectionTrace
open FirstFitRAM PairRAM ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical BigOperators Fin.CommRing
noncomputable section
variable {w : ℕ} {I V : Type*} [Fintype V] [DecidableEq V]

structure Layout where
  need : ℕ
  caps : ℕ
  bits : ℕ
  slots : ℕ
  offsets : ℕ

/-- Saturation is used solely past the fixed public number of program iterations. -/
def Layout.index (p : Layout) (i : ℕ) := if i < p.slots then i else 0
def Layout.amount (p : Layout) (i : ℕ) := p.need+p.index i
def Layout.tag (p : Layout) (i : ℕ) := choiceWord p.bits p.caps (p.index i)

structure Room (w n : ℕ) (p : Layout) : Prop where
  need : p.need+max 1 p.slots≤p.caps
  bins : n≤2^p.bits
  reserve : capacityBase p.bits p.caps p.slots+2^p.bits+1≤p.offsets
  end_ : Prefix.base p.offsets p.slots+2 < 2^w

theorem Layout.need_low {p : Layout} {n : ℕ} (room : Room w n p) (i : ℕ) :
    p.amount i < p.caps := by
  obtain ⟨lo,_,_,_⟩ := room
  unfold Layout.amount Layout.index
  split <;> omega

theorem Layout.tag_low {p : Layout} {n : ℕ} (room : Room w n p) (i : ℕ) :
    p.tag i < p.offsets := by
  have ix : p.index i≤p.slots := by unfold Layout.index;split <;> omega
  have mul := Nat.mul_le_mul_right (2^p.bits+1) ix
  have lim := room.reserve
  unfold Layout.tag choiceWord capacityBase at *
  omega

def first (p : Layout) (n : ℕ) (m : Memory w) :=
  FirstFitRAM.history n p.bits p.caps p.amount 0 p.slots m

def final (p : Layout) (n : ℕ) (m : Memory w) :=
  Prefix.after n p.amount p.tag p.offsets p.slots (first p n m)

def program (w n : ℕ) (p : Layout) : Procedure w :=
  (FirstFitRAM.sweep w n p.bits p.caps p.amount 0 p.slots).seq
    (Prefix.program w n p.amount p.tag p.offsets p.slots)

private theorem capacity_fits {p : Layout} {n k : ℕ} (room : Room w n p) (within : k≤p.slots) :
    capacityBase p.bits p.caps k+n<2^w := by
  have row : capacityBase p.bits p.caps k≤capacityBase p.bits p.caps p.slots :=
    Nat.add_le_add_left (Nat.mul_le_mul_right (2^p.bits+1) within) p.caps
  have below : capacityBase p.bits p.caps k+n≤p.offsets :=
    (Nat.add_le_add row room.bins).trans ((Nat.le_succ _).trans room.reserve)
  have begin_ : p.offsets≤Prefix.base p.offsets p.slots := Nat.le_add_right _ _
  exact (below.trans (begin_.trans (Nat.le_add_right _ 2))).trans_lt room.end_

theorem exec {p : Layout} {n : ℕ} (m : Memory w) (room : Room w n p) :
    (program w n p).Exec m (final p n m) ((p.slots*rowCost n+4)+(p.slots*168+20)) := by
  have sector := room.reserve
  have capStart : p.caps≤capacityBase p.bits p.caps p.slots := Nat.le_add_right _ _
  have capEnd : p.caps≤p.offsets :=
    capStart.trans ((Nat.le_add_right _ _).trans ((Nat.le_succ _).trans sector))
  apply Procedure.Exec.then (sweep_exec n p.bits p.caps p.amount m 0 p.slots room.bins
    (Layout.need_low room) (by simpa only [Nat.zero_add] using capacity_fits room (le_refl p.slots)))
  exact Prefix.exec n p.amount p.tag p.offsets p.slots (first p n m)
    (fun i=>(Layout.need_low room i).trans_le capEnd) (Layout.tag_low room) room.end_

theorem first_taken {p : Layout} (n : ℕ) (m : Memory w) (i : ℕ) (live : i≤p.slots) :
    first p n m=FirstFitRAM.history n p.bits p.caps p.amount i (p.slots-i)
      (FirstFitRAM.history n p.bits p.caps p.amount 0 i m) := by
  unfold first
  conv_lhs => arg 6;rw [show p.slots=i+(p.slots-i) by omega]
  rw [history_split,Nat.zero_add]

theorem decisions {p : Layout} (amount : I→ℕ) (xs : List I) (cap : V→ℕ) (m : Memory w)
    (room : Room w (Fintype.card V) p) (fits : xs.length≤p.slots)
    (values : capacityWords p.caps cap m) (bounded : ∀v,cap v < 2^w)
    (input : ∀i : Fin xs.length,m (p.need+i.val)=(amount (xs.get i):Word w))
    (widths : ∀i∈xs,amount i < 2^w) (i : Locations (pack amount xs cap).decisions) :
    final p (Fintype.card V) m (p.tag i.val)=(binTag ((pack amount xs cap).decisions.get i).2:Word w) := by
  have len := congrArg List.length (pack amount xs cap).order
  simp only [List.length_map] at len
  have old := i.isLt
  have lt : i.val < xs.length := by omega
  have inside : i.val < p.slots := lt.trans_le fits
  have native := history_pack p.bits p.caps 0 p.amount amount xs cap m room.bins (Layout.need_low room)
    (by simpa only [Nat.zero_add] using capacity_fits room fits)
    (by simpa [capacityBase] using values) bounded
    (fun j=>by simpa [Layout.amount,Layout.index,j.isLt.trans_le fits] using input j) widths
  have tail := history_before (Fintype.card V) p.bits p.caps p.amount
    (FirstFitRAM.history (Fintype.card V) p.bits p.caps p.amount 0 xs.length m)
    xs.length (p.slots-xs.length) (p.tag i.val) (by
      have before := Nat.mul_le_mul_right (2^p.bits+1) lt
      have next := Nat.mul_le_mul_right (2^p.bits+1) (Nat.succ_le_of_lt lt)
      simp only [Layout.tag,Layout.index,inside,ite_true,choiceWord,capacityBase,Nat.succ_mul] at *;omega)
  have retain := Prefix.issued_frame (Fintype.card V) p.amount p.tag p.offsets p.slots (first p (Fintype.card V) m)
    (p.tag i.val) (Layout.tag_low room i.val)
  apply retain.trans
  rw [first_taken (p:=p) (Fintype.card V) m xs.length fits]
  exact tail.trans (by simpa [Layout.tag,Layout.index,inside] using native.2 i)

end
end Hierarchy.DescentPacking.SelectionTrace

end OAI
