import OAI.Computability.BorderVNP.CubeTeamOwnedArenaSetup
import OAI.Computability.BorderVNP.CubeScatterArenaDelivered
import OAI.Computability.BorderVNP.TransmissionDataProgram

/-! # The actual shared interval emitter's ABI and word capacity -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.CubeArena

open VPVNP.BurstRAM BorderVNP.Cube BorderVNP.Cube.Physical BorderVNP.Cube.Tally
open CubeHeaderInstall CubeLengths

/-- Shared interval writer layout, directly from the native cube allocation,
the selected coordinate, and the number of preceding data records. -/
def Layout.sharedRows (a : Layout) (frame axis dataCount : ℕ) : SharedRows.Layout :=
  ⟨frame,a.header.d,a.n+1,axis,a.header.header,a.header.header+13+a.header.entries,
    a.rowSelectorBits,a.ownerBase,a.pairBase,a.pairStride,a.records,dataCount⟩

/-- The group scanner addresses exactly the directed views that this writer emits. -/
theorem Layout.shared_scanner (a : Layout) (frame team axis dataCount : ℕ) :
    TeamRowPrepare.Layout.ofShared (a.sharedRows frame axis dataCount) team =
      a.scanner frame team axis a.rowSelectorBits := rfl

/-- The record array extends over both the data prefix and the triangular symbol-pair suffix. -/
private theorem records_end (a : Layout) : a.records+7*a.maxRows ≤ a.pairBase := by
  unfold Layout.pairBase TableLayout.reserveEnd; omega

/-- A bounded physically decoded declaration and the allocated high-water word
supply all size, disjointness and word-arithmetic obligations of the seven-column writer. -/
theorem Layout.shared_fits (a : Layout) (w frame dataCount : ℕ) (axis : Fin (a.n+1))
    (mem : ℕ → ℕ) (rows : Sym2 (Fin a.header.d) → Fin (a.n+1) → ℕ)
    (table : StoredRows mem (a.header.header+13+a.header.entries) rows)
    (cap : ∀ p j, rows p j ≤ a.header.cap)
    (low : frame+112 ≤ a.header.header) (axes : a.header.a = a.n+1)
    (space : dataCount+a.header.d.choose 2 ≤ a.maxRows) (fit : a.stop < 2^w) :
    (a.sharedRows frame axis.val dataCount).Fits w mem := by
  let l := a.sharedRows frame axis.val dataCount
  have dec : a.header.header+13+a.header.entries+a.header.d^2*(a.n+1) ≤ a.header.packetBase := by
    simp only [Inputs.packetBase,Inputs.entries,axes,pow_two]; omega
  have pkt : a.header.packetBase ≤ a.packetEnd := Nat.le_add_right _ _
  obtain ⟨scratch,single,_,vp,pair,stop⟩ := a.separated
  have vpub : a.vertexBase ≤ a.publicBase := Nat.le_add_right _ _
  obtain ⟨power,own,_⟩ := a.source_order
  have dir : a.ownerBase+a.header.d ≤ a.records := by
    unfold Layout.records Layout.hostDirectory Layout.pairDirectory; omega
  have rend := records_end a
  have plen := a.orderedViews_before_tables
  have positive : 0 < a.pairStride := by unfold Layout.pairStride; omega
  have square : a.header.d^2 < 2^w :=
    (Nat.le_mul_of_pos_left (a.header.d^2) positive).trans_lt ((Nat.le_add_left _ _).trans_lt (plen.trans_lt fit))
  have groupFit : a.header.d < 2^w := by
    rcases Nat.eq_zero_or_pos a.header.d with zero|pos
    · rw [zero]; positivity
    · rw [pow_two] at square
      exact (Nat.le_mul_of_pos_right _ pos).trans_lt square
  have ps : a.pairBase ≤ a.stop := (Nat.le_add_right _ _).trans plen
  have count := Nat.mul_le_mul_left 7 space
  have idx (t : ℕ) (ht : t < a.header.d) (s : ℕ) (hs : s < t) :
      (s*a.header.d+t)*(a.n+1)+axis.val < a.header.d^2*(a.n+1) := by
    let x : Fin a.header.d := ⟨s,hs.trans ht⟩
    let y : Fin a.header.d := ⟨t,ht⟩
    simpa only [entryOrder_val,x,y,pow_two] using (entryOrder a.header.d (a.n+1) ((x,y),axis)).isLt
  refine ⟨⟨?_,?_⟩,groupFit,axis.isLt,square,?_,?_,?_,plen.trans fit.le,?_,?_,?_⟩
  · change frame+86 < 2^w; omega
  · change a.header.header+6 < 2^w; omega
  · change a.header.header+13+a.header.entries+a.header.d^2*(a.n+1) ≤ _; omega
  · change a.ownerBase+a.header.d ≤ _; omega
  · intro t ht s hs
    let x : Fin a.header.d := ⟨s,hs.trans ht⟩
    let y : Fin a.header.d := ⟨t,ht⟩
    have row := table x y axis
    rw [entryOrder_val,ite_eq_left (show x ≤ y from hs.le),← Nat.add_assoc] at row
    change a.rowSelectorBits+mem (a.header.header+13+a.header.entries+(s*a.header.d+t)*(a.n+1)+axis.val) ≤ a.pairStride
    rw [row]
    have declared := cap (Sym2.mk x y) axis
    unfold Layout.pairStride Layout.rowSelectorBits
    omega
  · change dataCount+a.header.d.choose 2 < 2^w; omega
  · change a.records+7*(dataCount+a.header.d.choose 2) ≤ 2^w; omega
  · intro t ht s hs j hj
    have key := idx t ht s hs
    have src : j ∈ [a.ownerBase+s,a.ownerBase+t,
        a.header.header+13+a.header.entries+(s*a.header.d+t)*(a.n+1)+axis.val,frame+13] := hj
    apply Or.inl
    change j < a.records+7*dataCount
    simp only [List.mem_cons,List.not_mem_nil,or_false] at src
    change t < a.header.d at ht
    rcases src with rfl|rfl|rfl|rfl <;> omega

end RoutingISA.CubeArena

end BorderVNP
end Computability
end OAI
