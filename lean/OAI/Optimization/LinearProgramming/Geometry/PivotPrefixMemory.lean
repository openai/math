import OAI.Optimization.LinearProgramming.Geometry.PivotPrefixLayout
import OAI.Optimization.LinearProgramming.Geometry.PivotStageRAM

/-! Concrete prefix storage and the fixed instruction block that commits an accepted row. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Geometry
namespace PivotPrefixRAM

open RAM RAM.Block

/-- Permanent high arguments, including the row-major rounded output, packed triple
scratch, and the separate address-bank table of pivots. -/
structure Layout (base : Memory ℚ) (r n B : ℕ) : Prop where
  rank : base.index 129 = r
  columns : base.index 130 = n
  precision : base.index 138 = B
  triplesHigh : 256 ≤ base.index 133
  rowsHigh : 256 ≤ base.index 134
  pivotsHigh : 256 ≤ base.index 136
  separate : base.index 133+3*n ≤ base.index 134 ∨ base.index 134+r*n ≤ base.index 133

/-- Previously accepted pivots and rows are simultaneously present in their public tapes.
Registers 140–149 include signed-minor descriptors and the downstream label coordinates. -/
structure Stored {n a : ℕ} (base m : Memory ℚ) (rows : Fin a → PivotRow n)
    (price : Fin n → ℚ) (B : ℕ) : Prop where
  length : m.index 128 = a
  rowCursor : m.index 135 = base.index 134 + a*n
  pivotCursor : m.index 137 = base.index 136 + a
  permanent (i) : 129 ≤ i → i ≤ 149 → i ≠ 135 → i ≠ 137 → i ≠ 139 → m.index i = base.index i
  pivots (s : Fin a) : m.index (base.index 136+s.val) = (rows s).pivot.val
  rounded (s : Fin a) (j : Fin n) : m.data (base.index 134+s.val*n+j.val) = (rows s).rounded price B j

/-- Cells that the deterministic pivot stage and output commit preserve. This lets an
oracle implementation keep its own internal state in disjoint storage across stages. -/
structure CallerFrame (base u v : Memory ℚ) (r n : ℕ) : Prop where
  data (i) : 27 ≤ i → (i < base.index 134 ∨ base.index 134+r*n ≤ i) → v.data i = u.data i
  index (i) : 140 ≤ i → (i < base.index 136 ∨ base.index 136+r ≤ i) → v.index i = u.index i

/-- The current batch has materialized all three fields used by the deterministic scan. -/
structure PackedRow {n : ℕ} (m : Memory ℚ) (row : PivotRow n) (price : Fin n → ℚ) (L : ℕ) : Prop where
  raw (j : Fin n) : m.data (m.index 133+3*j.val) = row.raw j
  logs (j : Fin n) : m.data (m.index 133+3*j.val+1) = row.logs j
  prices (j : Fin n) : m.data (m.index 133+3*j.val+2) = price j
  localWidth (j : Fin n) (q) : q < 3 → ratBits (m.data (m.index 133+3*j.val+q)) ≤ L

theorem Stored.empty (m : Memory ℚ) {n : ℕ} (price : Fin n → ℚ) (B : ℕ) : Stored m (initial m) Fin.elim0 price B := by
  refine ⟨by simp [initial],by simp [initial],by simp [initial],?_,fun j => j.elim0,fun j => j.elim0⟩
  intro i lo hi h135 h137 h139
  simp [initial,h135,h137,h139,show i ≠ 128 by omega]

theorem CallerFrame.initial (m : Memory ℚ) (r n : ℕ) : CallerFrame m m (PivotPrefixRAM.initial m) r n := by
  constructor
  · intro _ _ _; rfl
  · intro i hi _
    simp [PivotPrefixRAM.initial,show i ≠ 128 by omega,show i ≠ 135 by omega,show i ≠ 137 by omega,show i ≠ 139 by omega]

/-- Prepare a fresh one for the status test in low scratch, so client registers 146–149
are available for the designated coordinate, second input, dual rank, and allocation end. -/
def branchMemory (m : Memory ℚ) : Memory ℚ := m.putIndex 15 1

theorem Stored.branch {n a B : ℕ} {base m : Memory ℚ} {rows : Fin a → PivotRow n} {price : Fin n → ℚ}
    (hs : Stored base m rows price B) (high : 256 ≤ base.index 136) : Stored base (branchMemory m) rows price B := by
  refine ⟨hs.length,hs.rowCursor,hs.pivotCursor,?_,?_,hs.rounded⟩
  · intro i lo hi h135 h137 h139
    simpa [branchMemory, show i ≠ 15 by omega] using hs.permanent i lo hi h135 h137 h139
  · intro j
    simpa [branchMemory,show base.index 136+j.val ≠ 15 by omega] using hs.pivots j

theorem CallerFrame.branch (base m : Memory ℚ) (r n : ℕ) : CallerFrame base m (branchMemory m) r n := by
  refine ⟨fun _ _ _ => rfl,?_⟩
  intro i hi _; simp [branchMemory,show i ≠ 15 by omega]

theorem PackedRow.branch {n L : ℕ} {m : Memory ℚ} {row : PivotRow n} {price : Fin n → ℚ}
    (hp : PackedRow m row price L) : PackedRow (branchMemory m) row price L :=
  ⟨hp.raw,hp.logs,hp.prices,hp.localWidth⟩

def acceptedStage : Block := .seq stageArgs (.seq PivotStageRAM.block commitRow)

/-- On acceptance the previous output remains readable, the next signed rounded row and
winning pivot are written to their designated cells, and the two output cursors advance. -/
theorem acceptRow {r n a H L B : ℕ} (D : Matrix (Fin (a+1)) (Fin n) ℚ) (rows : Fin a → PivotRow n)
    (row : PivotRow n) (price : Fin n → ℚ) (f : PivotKey n → ℚ) (base m : Memory ℚ)
    (bounds : Layout base r n B) (ha : a < r) (hs : Stored base m rows price B)
    (hp : PackedRow m row price L) (hb : RowRAM.Within H m)
    (he : MinorQuery.eval f (pivotStep D (fun j => (rows j).pivot) price) = some row)
    (spec : PivotStepSpec D (fun j => (rows j).pivot) price f row) :
    ∃ t k, k ≤ n*(32*B+210)+27 ∧
      Eval (RowRAM.Within (PivotStageRAM.stageWidth n H L B)) acceptedStage m k t ∧
      Stored base t (Fin.lastCases row rows) price B ∧ CallerFrame base m t r n ∧ t.index 139 = m.index 139 := by
  let u := stageMemory m
  have same (i : ℕ) (hi : 9 ≤ i) : u.index i = m.index i := by
    simp [u,stageMemory,show i ≠ 0 by omega,show i ≠ 4 by omega,show i ≠ 6 by omega,show i ≠ 8 by omega]
  have reg (i : ℕ) (lo : 129 ≤ i) (hi : i ≤ 149) (h135 : i ≠ 135) (h137 : i ≠ 137) (h139 : i ≠ 139) :=
    hs.permanent i lo hi h135 h137 h139
  have ptr : u.index 4 = m.index 133 := by simp [u,stageMemory]
  have dst : u.index 8 = m.index 135 := by simp [u,stageMemory]
  have usrc : u.index 4 = base.index 133 := ptr.trans (reg 133 (by decide) (by decide) (by decide) (by decide) (by decide))
  have udst : u.index 8 = base.index 134+a*n := dst.trans hs.rowCursor
  have room : a*n+n ≤ r*n := by simpa only [Nat.succ_mul] using Nat.mul_le_mul_right n (Nat.succ_le_of_lt ha)
  have sep : u.index 4+3*n ≤ u.index 8 ∨ u.index 8+n ≤ u.index 4 := by
    rw [usrc,udst]; rcases bounds.separate with h | h <;> omega
  have uc : u.index 0 = n := by
    rw [show u.index 0 = m.index 130 by simp [u,stageMemory],reg 130 (by decide) (by decide) (by decide) (by decide) (by decide),bounds.columns]
  have ub : u.index 6 = B := by
    rw [show u.index 6 = m.index 138 by simp [u,stageMemory],reg 138 (by decide) (by decide) (by decide) (by decide) (by decide),bounds.precision]
  have srcHigh := bounds.triplesHigh
  have dstHigh := bounds.rowsHigh
  have pivotHigh := bounds.pivotsHigh
  obtain ⟨v,k,hk,step,hv⟩ := PivotStageRAM.block_spec D (fun j => (rows j).pivot) price f row he spec u H L B hb
    (fun j q h => by rw [ptr]; exact hp.localWidth j q h) ub uc (by omega) (by omega) sep
    (fun j => by unfold PivotRAM.inputMinor; rw [ptr]; exact hp.raw j)
    (fun j => by unfold PivotRAM.inputLog; rw [ptr]; exact hp.logs j)
    (fun j => by unfold PivotRAM.inputPrice; rw [ptr]; exact hp.prices j)
  have high (i : ℕ) (hi : 14 ≤ i) : v.index i = m.index i :=
    (hv.index i (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)).trans (same i (by omega))
  have vslot : v.index 137 = base.index 136+a := (high 137 (by decide)).trans hs.pivotCursor
  have vcount : v.index 130 = n := (high 130 (by decide)).trans ((reg 130 (by decide) (by decide) (by decide) (by decide) (by decide)).trans bounds.columns)
  obtain ⟨t,commit,hc⟩ := commitRow_spec v (fun q => ratBits q ≤ PivotStageRAM.stageWidth n H L B) step.safe_end (by omega)
  have setup := stageArgs_eval m (fun q => ratBits q ≤ PivotStageRAM.stageWidth n H L B) (fun i => (hb i).trans (Nat.le_add_right _ _))
  refine ⟨t,4+(k+(4*v.index 130+6)),?_,setup.seq (step.seq commit),?_,?_,?_⟩
  · rw [vcount]; nlinarith
  · constructor
    · rw [hc.row,high 128 (by decide),hs.length]
    · rw [hc.nextRow,high 135 (by decide),hs.rowCursor,vcount,Nat.succ_mul,Nat.add_assoc]
    · rw [hc.nextSlot,vslot,Nat.add_assoc]
    · intro i lo hi h135 h137 h139
      exact (hc.frame i (by omega) (by omega) h135 h137 (by omega)).trans ((high i (by omega)).trans (reg i lo hi h135 h137 h139))
    · intro j
      refine Fin.lastCases ?_ (fun q => ?_) j
      · simp only [Fin.val_last,Fin.lastCases_last]
        rw [← vslot,hc.pivot,hv.pivot]
      · simp only [Fin.val_castSucc,Fin.lastCases_castSucc]
        have hq := q.isLt
        rw [hc.frame _ (by omega) (by omega) (by omega) (by omega) (by omega),high _ (by omega)]
        exact hs.pivots q
    · intro j i
      refine Fin.lastCases ?_ (fun q => ?_) j
      · simp only [Fin.val_last,Fin.lastCases_last]
        rw [hc.data,← udst,hv.rounded]
      · simp only [Fin.val_castSucc,Fin.lastCases_castSucc]
        have previous : q.val*n+n ≤ a*n := by simpa only [Nat.succ_mul] using Nat.mul_le_mul_right n q.isLt
        have hi := i.isLt
        rw [hc.data,hv.data _ (by omega) (Or.inl (by omega))]
        exact hs.rounded q i
  · constructor
    · intro i hi outside
      rw [hc.data,hv.data _ hi (by omega)]
      rfl
    · intro i hi outside
      exact (hc.frame _ (by omega) (by omega) (by omega) (by omega) (by omega)).trans (high i (by omega))
  · exact (hc.frame _ (by decide) (by decide) (by decide) (by decide) (by omega)).trans (high _ (by decide))

end PivotPrefixRAM
end Geometry
end LinearProgramming
end Optimization
end OAI
