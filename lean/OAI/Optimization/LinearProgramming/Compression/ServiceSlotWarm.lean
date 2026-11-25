import OAI.Optimization.LinearProgramming.Compression.ServiceSlotCursor
import OAI.Optimization.LinearProgramming.Compression.ServiceSlotPair

/-! Initialize the two reverse scans with a single pass over the ambient dimension. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression
namespace GeneratorTable
open RAM

def warmSlots : Block := .seq (slotMoves setupMoves) (.forRange 28 22 (slotMoves warmMoves))

theorem SlotCursor.putLoop {s t : Memory ℚ} {r c : ℕ} (h : SlotCursor s t r c) (v : ℕ) :
    SlotCursor s (t.putIndex 28 v) r c := h.of_preserved fun _ hi lo => Memory.putIndex_ne _ (by omega) _

theorem SlotFrame.high {s t : Memory ℚ} (h : SlotFrame s t) {i : ℕ} (hi : 7≤ i) : t.data i=s.data i :=
  h.data i (by omega) (by omega) (by omega)

private structure Warm (P : ℚ → Prop) (s t : Memory ℚ) (j : ℕ) : Prop where
  safe : SlotSafe P t
  frame : SlotFrame s t
  cursor : SlotCursor s t (2+j) (2+2*j)
  counter : t.index 28=j
  result : t.index 23=1

theorem warmSlots_spec (P : ℚ → Prop) (s : Memory ℚ) (n : ℕ) (hn : s.index 22=n) (hs : SlotSafe P s) :
    ∃ t k, k ≤ 9*n+9 ∧ Block.Eval (SlotSafe P) warmSlots s k t ∧ SlotFrame s t ∧
      SlotCursor s t (2+n) (2+2*n) ∧ t.index 23=1 := by
  let pre := afterMoves s setupMoves
  have ep := slotMoves_eval P s setupMoves hs
  have fp : SlotFrame s pre := afterMoves_frame s setupMoves (by simp [setupMoves,SlotMove.dst])
  have hp : Warm P s (pre.putIndex 28 0) 0 := by
    exact ⟨ep.safe_end,fp.putIndex _ _ (by decide) (by decide),by simpa [pre] using (setup_cursor s).putLoop 0,
      by simp,by simp [pre,setupMoves,afterMoves,SlotMove.act]⟩
  obtain ⟨t,k,hk,run,ht⟩ := Block.Eval.forRange_invariant (safe := SlotSafe P) (body := slotMoves warmMoves)
    28 22 n 6 (fun j t => Warm P s t j) pre ep.safe_end hp
    (fun j t h => ⟨h.safe,h.counter,(h.frame.index _ (by decide)).trans hn⟩) (by
      intro j hj v h
      let z := afterMoves v warmMoves
      have ez := slotMoves_eval P v warmMoves h.safe
      have fz : SlotFrame s z := h.frame.trans (afterMoves_frame v warmMoves (by simp [warmMoves,SlotMove.dst]))
      have cz : SlotCursor s z (2+(j+1)) (2+2*(j+1)) := by
        convert h.cursor.warm using 1
      have z28 : z.index 28=v.index 28 := afterMoves_index v warmMoves 28 (by simp [warmMoves,SlotMove.dst])
      have z23 : z.index 23=v.index 23 := afterMoves_index v warmMoves 23 (by simp [warmMoves,SlotMove.dst])
      exact ⟨z,6,by decide,ez,⟨ez.safe_end,fz.putIndex _ _ (by decide) (by decide),cz.putLoop _,
        by simp [z28,h.counter], by simpa using z23.trans h.result⟩⟩)
  exact ⟨t,7+k,by omega,ep.seq run,ht.frame,ht.cursor,ht.result⟩

end GeneratorTable
end Compression
end LinearProgramming
end Optimization
end OAI
