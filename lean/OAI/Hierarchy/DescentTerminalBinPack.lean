import OAI.ThreeFlat.Routing.CallBatches

namespace OAI
/-! # Chronological contiguous allocation in equal-width terminal bins

The cursor is the first unoccupied absolute row. A site fits at that cursor
or starts at the next bin boundary. Every skipped row is paid by the site
that forced the advance.
-/

namespace Hierarchy.DescentTerminalBinPack
open ThreeFlat.Routing
open scoped BigOperators
variable {S : ℕ}

def demand (count : Fin S → ℕ) (i : ℕ) := if h : i<S then count ⟨i,h⟩ else 0

def startAt (W used size : ℕ) :=
  if used%W+size ≤ W then used else used+(W-used%W)

/-- Absolute end of the prefix of sites, excluding the right endpoint. -/
def cursor (W : ℕ) (count : Fin S → ℕ) : ℕ → ℕ
  | 0 => 0
  | i+1 => startAt W (cursor W count i) (demand count i)+demand count i

def first (W : ℕ) (count : Fin S → ℕ) (i : Fin S) := startAt W (cursor W count i.val) (count i)
def last (W : ℕ) (count : Fin S → ℕ) (i : Fin S) := first W count i+count i-1
def bin (W : ℕ) (count : Fin S → ℕ) (i : Fin S) := first W count i / W
def offset (W : ℕ) (count : Fin S → ℕ) (i : Fin S) := first W count i % W
def bins (W : ℕ) (count : Fin S → ℕ) := poolBatchCount (cursor W count S) W
def purchased (W : ℕ) (count : Fin S → ℕ) := bins W count*W

theorem first_eq (W : ℕ) (count : Fin S → ℕ) (i : Fin S) :
    first W count i=bin W count i*W+offset W count i := by
  simpa only [bin,offset,Nat.mul_comm W] using (Nat.div_add_mod (first W count i) W).symm

theorem cursor_step (W : ℕ) (count : Fin S → ℕ) (i : Fin S) :
    cursor W count (i.val+1)=first W count i+count i := by
  simp [cursor,first,demand,i.isLt]

theorem first_ge (W : ℕ) (count : Fin S → ℕ) (i : Fin S) :
    cursor W count i.val ≤ first W count i := by
  unfold first startAt
  split <;> omega

theorem cursor_mono (W : ℕ) (count : Fin S → ℕ) : Monotone (cursor W count) := by
  apply monotone_nat_of_le_succ
  intro i
  simp only [cursor,startAt]
  split <;> omega

theorem ordered (W : ℕ) (count : Fin S → ℕ) {i j : Fin S} (early : i<j) :
    first W count i+count i ≤ first W count j := by
  rw [←cursor_step]
  exact (cursor_mono W count (show i.val+1 ≤ j.val from early)).trans (first_ge W count j)

theorem in_bin {W : ℕ} (positive : 0<W) (count : Fin S → ℕ) (i : Fin S)
    (fit : count i ≤ W) : offset W count i+count i ≤ W := by
  let c := cursor W count i.val
  change (if c%W+count i ≤ W then c else c+(W-c%W))%W+count i ≤ W
  split
  · assumption
  · have rest := Nat.mod_lt c positive
    have edge : c+(W-c%W)=(c/W+1)*W := by
      have eqn := Nat.div_add_mod c W
      rw [Nat.mul_comm W (c/W)] at eqn
      rw [Nat.succ_mul]
      omega
    simpa only [edge,Nat.mul_mod_left,Nat.zero_add] using fit

theorem end_le_purchased {W : ℕ} (positive : 0<W) (count : Fin S → ℕ) :
    cursor W count S ≤ purchased W count := by
  simpa only [purchased,bins,Nat.mul_comm W] using
    CallPool.count_le_batches_mul (cursor W count S) W positive

theorem bin_lt {W : ℕ} (positive : 0<W) (count : Fin S → ℕ) (i : Fin S) (live : 0<count i) :
    bin W count i<bins W count := by
  apply (Nat.div_lt_iff_lt_mul positive).mpr
  have lim := (cursor_mono W count (show i.val+1 ≤ S from i.isLt)).trans (end_le_purchased positive count)
  rw [cursor_step] at lim
  change _ ≤ bins W count*W at lim
  omega

/-- Each charged row has an explicit address in the purchased array. -/
def rowIndex {W : ℕ} (positive : 0<W) (count : Fin S→ℕ) :
    (Σ i, Fin (count i)) ↪ Fin (purchased W count) where
  toFun z := ⟨first W count z.1+z.2.val,by
    have h := (cursor_mono W count (show z.1.val+1 ≤ S from z.1.isLt)).trans
      (end_le_purchased positive count)
    rw [cursor_step] at h
    exact (Nat.add_lt_add_left z.2.isLt _).trans_le h⟩
  inj' := by
    rintro ⟨i,a⟩ ⟨j,b⟩ eqn
    have atRow : first W count i+a.val=first W count j+b.val := congrArg Fin.val eqn
    have eqSite : i=j := by
      rcases lt_trichotomy i j with h | e | h
      · have sep := ordered W count h
        have bound := a.isLt
        omega
      · exact e
      · have sep := ordered W count h
        have bound := b.isLt
        omega
    subst j
    have eqSlot : a=b := Fin.ext (Nat.add_left_cancel atRow)
    cases eqSlot
    rfl

theorem last_eq (W : ℕ) (count : Fin S → ℕ) (i : Fin S) (live : 0<count i) :
    last W count i+1=first W count i+count i := by unfold last; omega

theorem cursor_le_sum (W : ℕ) (count : Fin S → ℕ) (k : ℕ) :
    cursor W count k ≤ 2*(∑ i ∈ Finset.range k,demand count i) := by
  induction k with
  | zero => simp [cursor]
  | succ i ih =>
    rw [Finset.sum_range_succ,Nat.mul_add,cursor,startAt]
    split <;> omega

theorem cursor_le_total (W : ℕ) (count : Fin S → ℕ) {k : ℕ} (hk : k ≤ S) :
    cursor W count k ≤ 2*∑ i,count i := by
  have total := cursor_le_sum W count S
  rw [←Fin.sum_univ_eq_sum_range] at total
  apply (cursor_mono W count hk).trans
  simpa [demand] using total

theorem paid (W : ℕ) (count : Fin S → ℕ) : purchased W count ≤ 2*(∑ i,count i)+W := by
  have floor : purchased W count ≤ cursor W count S+W :=
    (Nat.div_mul_le_self (cursor W count S+W-1) W).trans (Nat.sub_le ..)
  exact floor.trans (Nat.add_le_add_right (cursor_le_total W count le_rfl) _)

theorem paid_of_le {W budget : ℕ} (count : Fin S → ℕ) (total : (∑ i,count i) ≤ budget) :
    purchased W count ≤ 2*budget+W :=
  (paid W count).trans (Nat.add_le_add_right (Nat.mul_le_mul_left _ total) _)

/-- The inclusive signed interval for a positive site fits inside one
purchased bin, including any reserved row counted in the site's demand. -/
theorem interval {W : ℕ} (positive : 0<W) (count : Fin S → ℕ) (i : Fin S)
    (live : 0<count i) (half : count i ≤ W/2) :
    bin W count i<bins W count ∧ bin W count i*W ≤ first W count i ∧
      first W count i ≤ last W count i ∧ last W count i<(bin W count i+1)*W := by
  have begin := first_eq W count i
  have inside := in_bin positive count i (half.trans (Nat.div_le_self ..))
  have lastRow := last_eq W count i live
  rw [Nat.succ_mul]
  exact ⟨bin_lt positive count i live,by omega,by omega,by omega⟩

end Hierarchy.DescentTerminalBinPack

end OAI
