import OAI.Computability.BorderVNP.CubeScatterPaddingBanks

/-! # Concrete three-pass and diagonal updates of the physical view banks -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.Padding.Banks

open Physical Physical.Owned Physical.VertexIndex Scatter RoutingISA VPVNP.BurstRAM Tally

variable {n d blocks b h K s w : ℕ} (A : Data n d blocks b h K s)

/-- The packet scatter, then the two singleton orientations, using each preceding
stage's actual returned selector and crossing cursors and its complete memory. -/
def Data.strictMem (pair : Symbols d) (high : Bool) (sel cross : ℕ) (m : Memory w) : Memory w :=
  let D := A.packet pair high sel cross
  let endP := D.before m (packetTrials n d blocks)
  let first := A.single pair.val.1 pair.val.2 endP.sel endP.cross
  let endA := first.before endP.mem (singlePairTrials n d)
  let second := A.single pair.val.2 pair.val.1 endP.sel endA.1
  (second.before endA.2 (singlePairTrials n d)).2

/-- Scatter update at one actual ordered endpoint view; the diagonal has only one
singleton family, and the lower and upper rows visit the two sides of each packet. -/
def Data.rowMem (left right : Fin d) (sel cross : ℕ) (m : Memory w) : Memory w :=
  if lt : left < right then A.strictMem ⟨(left,right),lt⟩ false sel cross m
  else if gt : right < left then A.strictMem ⟨(right,left),gt⟩ true sel cross m
  else ((A.single left right sel cross).before m (singlePairTrials n d)).2

/-- All three stages of a strict endpoint view retain every previously correct local input. -/
theorem Data.strict_keeps (sep : A.Separate) (hw : 0 < w) (pair : Symbols d) (high : Bool)
    (sel cross : ℕ) (m : Memory w) (x : View n d blocks (h*b)) (old : A.Holds m x) :
    A.Holds (A.strictMem pair high sel cross m) x :=
  A.single_keeps sep _ _ _ _ _ x (A.single_keeps sep _ _ _ _ _ x (A.packet_keeps sep hw pair high sel cross m x old))

/-- The memory returned by either kind of native row retains all earlier reads. -/
theorem Data.row_keeps (sep : A.Separate) (hw : 0 < w) (left right : Fin d) (sel cross : ℕ)
    (m : Memory w) (x : View n d blocks (h*b)) (old : A.Holds m x) :
    A.Holds (A.rowMem left right sel cross m) x := by
  unfold Data.rowMem
  split
  · exact A.strict_keeps sep hw _ _ _ _ _ _ old
  split
  · exact A.strict_keeps sep hw _ _ _ _ _ _ old
  · exact A.single_keeps sep _ _ _ _ _ _ old

private theorem strict_single (sep : A.Separate) (pair : Symbols d) (high : Bool) (sel cross : ℕ)
    (m : Memory w) (q : SingleSlot n d blocks (h*b)) (side : Bool)
    (hit : (q.1.val.1 A.axis = pair.val.1 ∧ q.1.val.2 A.axis = pair.val.2) ∨
      (q.1.val.1 A.axis = pair.val.2 ∧ q.1.val.2 A.axis = pair.val.1)) :
    A.Holds (A.strictMem pair high sel cross m) (.single q side) := by
  let endP := (A.packet pair high sel cross).before m (packetTrials n d blocks)
  let first := A.single pair.val.1 pair.val.2 endP.sel endP.cross
  let endA := first.before endP.mem (singlePairTrials n d)
  let second := A.single pair.val.2 pair.val.1 endP.sel endA.1
  rcases hit with ab | ba
  · apply A.single_keeps sep pair.val.2 pair.val.1 endP.sel endA.1 endA.2 (.single q side)
    exact first.final_slot endP.mem q ab.1 ab.2
  · exact second.final_slot endA.2 q ba.1 ba.2

private theorem strict_vertex (sep : A.Separate) (hw : 0 < w) (pair : Symbols d) (high : Bool) (sel cross : ℕ)
    (m : Memory w) (p : Packet n d blocks) (v : Vertex (n+1))
    (inRow : p.1.1 A.axis = pair) (own : vertexLabel p v A.axis = groupSymbol p A.axis high) :
    A.Holds (A.strictMem pair high sel cross m) (.vertex p v) := by
  let D := A.packet pair high sel cross
  exact A.single_keeps sep _ _ _ _ _ _ (A.single_keeps sep _ _ _ _ _ _
    (D.final_vertexAt m hw le_rfl p inRow v own))

/-- A complete native iteration supplies every physical view designated by its ordered
row, even when the two ends of a singleton share the chosen coordinate symbol. -/
theorem Data.row_hits (sep : A.Separate) (hw : 0 < w) (sel cross : ℕ) (m : Memory w)
    (x : View n d blocks (h*b)) : A.Holds (A.rowMem (x.row A.axis).1 (x.row A.axis).2 sel cross m) x := by
  cases x with
  | single q side =>
    let u := q.1.val.1 A.axis
    let v := q.1.val.2 A.axis
    rcases lt_trichotomy u v with lt | eq | gt
    · cases side
      · change A.Holds (A.rowMem u v _ _ _) _
        rw [Data.rowMem,dite_eq_left lt]
        exact strict_single A sep _ _ _ _ _ _ _ (Or.inl ⟨rfl,rfl⟩)
      · change A.Holds (A.rowMem v u _ _ _) _
        rw [Data.rowMem,dite_eq_right lt.not_gt,dite_eq_left lt]
        exact strict_single A sep _ _ _ _ _ _ _ (Or.inl ⟨rfl,rfl⟩)
    · have same (sd : Bool) : A.Holds (A.rowMem u u sel cross m) (.single q sd) := by
        rw [Data.rowMem,dite_eq_right (lt_irrefl _),dite_eq_right (lt_irrefl _)]
        exact (A.single u u sel cross).final_slot m q rfl eq.symm
      cases side
      · change A.Holds (A.rowMem u v _ _ _) _
        rw [← eq]; exact same _
      · change A.Holds (A.rowMem v u _ _ _) _
        rw [← eq]; exact same _
    · cases side
      · change A.Holds (A.rowMem u v _ _ _) _
        rw [Data.rowMem,dite_eq_right gt.not_gt,dite_eq_left gt]
        exact strict_single A sep _ _ _ _ _ _ _ (Or.inr ⟨rfl,rfl⟩)
      · change A.Holds (A.rowMem v u _ _ _) _
        rw [Data.rowMem,dite_eq_left gt]
        exact strict_single A sep _ _ _ _ _ _ _ (Or.inr ⟨rfl,rfl⟩)
  | vertex p v =>
    have lt : (p.1.1 A.axis).val.1 < (p.1.1 A.axis).val.2 := (p.1.1 A.axis).property
    cases bit : cornerBits p v A.axis
    · change A.Holds (A.rowMem (((View.vertex p v : View n d blocks (h*b)).row A.axis).1) _ _ _ _) _
      simp only [View.row,bit,Bool.false_eq_true,ite_false,Data.rowMem,dite_eq_left lt]
      apply strict_vertex A sep hw _ _ _ _ _ _ _ rfl
      simp [vertexLabel,bit,groupSymbol]
    · simp only [View.row,bit,ite_true,Data.rowMem,dite_eq_right lt.not_gt,dite_eq_left lt]
      apply strict_vertex A sep hw _ _ _ _ _ _ _ rfl
      simp [vertexLabel,bit,groupSymbol]

end Cube.Padding.Banks

end BorderVNP
end Computability
end OAI
