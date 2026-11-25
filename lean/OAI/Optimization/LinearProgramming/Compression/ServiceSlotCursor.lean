import OAI.Optimization.LinearProgramming.Compression.ServiceSlotMoves

/-! Address and scalar framing for scanning two padded minor records backwards. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression
namespace GeneratorTable
open RAM

structure SlotFrame (s t : Memory ℚ) : Prop where
  index : ∀ i, i<23 ∨ 40≤ i → t.index i=s.index i
  data : ∀ i, i≠0 → i≠5 → i≠6 → t.data i=s.data i

theorem SlotFrame.refl (s : Memory ℚ) : SlotFrame s s := ⟨fun _ _ => rfl,fun _ _ _ _ => rfl⟩

theorem SlotFrame.trans {s t v : Memory ℚ} (h : SlotFrame s t) (g : SlotFrame t v) : SlotFrame s v :=
  ⟨fun i hi => (g.index i hi).trans (h.index i hi),
   fun i h0 h5 h6 => (g.data i h0 h5 h6).trans (h.data i h0 h5 h6)⟩

theorem SlotFrame.putIndex {s t : Memory ℚ} (h : SlotFrame s t) (i val : ℕ) (hlo : 23≤ i) (hhi : i<40) :
    SlotFrame s (t.putIndex i val) := by
  refine ⟨fun j hj => ?_,h.data⟩
  rw [Memory.putIndex_ne _ (by omega : j≠i)]
  exact h.index _ hj

def SlotMove.dst : SlotMove → ℕ
  | .copy a _ | .incr a _ | .decr a _ | .constant a _ => a

theorem afterMoves_index (m : Memory ℚ) (xs : List SlotMove) (i : ℕ)
    (h : ∀ a∈xs, i≠a.dst) : (afterMoves m xs).index i=m.index i := by
  induction xs generalizing m with
  | nil => rfl
  | cons a xs ih =>
    rw [afterMoves,ih _ (fun x hx => h x (List.mem_cons_of_mem _ hx))]
    have ha := h a (List.mem_cons_self ..)
    cases a <;> simpa [SlotMove.act,SlotMove.dst] using Memory.putIndex_ne m ha _

theorem afterMoves_frame (m : Memory ℚ) (xs : List SlotMove)
    (h : ∀ a∈xs, 23≤ a.dst ∧ a.dst<40) : SlotFrame m (afterMoves m xs) := by
  refine ⟨fun i hi => afterMoves_index _ _ _ (fun a ha => ?_),fun i _ _ _ => by simp⟩
  have := h a ha; omega

structure SlotCursor (s t : Memory ℚ) (row col : ℕ) : Prop where
  leftRow : t.index 24=s.index 20+row
  leftCol : t.index 25=s.index 20+col
  rightRow : t.index 26=s.index 21+row
  rightCol : t.index 27=s.index 21+col

theorem SlotCursor.of_preserved {s t v : Memory ℚ} {r c : ℕ} (h : SlotCursor s t r c)
    (hp : ∀ i,24≤ i → i<28 → v.index i=t.index i) : SlotCursor s v r c :=
  ⟨(hp 24 (by decide) (by decide)).trans h.leftRow, (hp 25 (by decide) (by decide)).trans h.leftCol,
   (hp 26 (by decide) (by decide)).trans h.rightRow,(hp 27 (by decide) (by decide)).trans h.rightCol⟩

theorem setup_cursor (m : Memory ℚ) : SlotCursor m (afterMoves m setupMoves) 2 2 := by
  constructor <;> simp [setupMoves,afterMoves,SlotMove.act,Nat.add_assoc]

theorem SlotCursor.warm {s t : Memory ℚ} {r c : ℕ} (h : SlotCursor s t r c) :
    SlotCursor s (afterMoves t warmMoves) (r+1) (c+2) := by
  constructor <;> simp [warmMoves,afterMoves,SlotMove.act,h.leftRow,h.leftCol,h.rightRow,h.rightCol,Nat.add_assoc]

theorem SlotCursor.back {s t : Memory ℚ} {r c : ℕ} (h : SlotCursor s t r c) (hr : 0<r) (hc : 0<c) :
    SlotCursor s (afterMoves t backMoves) (r-1) (c-1) := by
  constructor <;> simp [backMoves,afterMoves,SlotMove.act,h.leftRow,h.leftCol,h.rightRow,h.rightCol] <;> omega

theorem SlotCursor.head {s t : Memory ℚ} {r c : ℕ} (h : SlotCursor s t r c) (hr : 0<r) :
    SlotCursor s (afterMoves t headMoves) (r-1) c := by
  constructor <;> simp [headMoves,afterMoves,SlotMove.act,h.leftRow,h.leftCol,h.rightRow,h.rightCol] <;> omega

end GeneratorTable
end Compression
end LinearProgramming
end Optimization
end OAI
