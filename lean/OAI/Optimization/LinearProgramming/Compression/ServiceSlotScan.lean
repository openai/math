import OAI.Optimization.LinearProgramming.Compression.ServiceSlotWarm
import OAI.Optimization.LinearProgramming.Compression.ServiceSlotWord

/-! The bounded native sweep processes the pair at each row/column position, from the last
padded cell to the first.  When minor orders agree its result is their true suffix ordering. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression
namespace GeneratorTable
open RAM

variable {d e n : ℕ} {D : Matrix (Fin d) (Fin n) ℚ} {E : Matrix (Fin e) (Fin n) ℚ}

def pairSweep : Block := .forRange 28 22 (.seq (slotMoves backMoves) comparePairs)

private structure Sweep (P : ℚ → Prop) (y q : NonzeroPairMinor D E) (s t : Memory ℚ) (j : ℕ) : Prop where
  safe : SlotSafe P t
  frame : SlotFrame s t
  cursor : SlotCursor s t (2+(n-j)) (2+n+(n-j))
  counter : t.index 28=j
  result : order y.val=order q.val → t.index 23=
    orderCode ((pairBody y.val).drop (n-j)) ((pairBody q.val).drop (n-j))

theorem pairSweep_spec (y q : NonzeroPairMinor D E) (P : ℚ → Prop) (s m : Memory ℚ)
    (hd : d+e=n) (hn : s.index 22=n) (ySlot : SlotAt D E y (s.index 20) s)
    (qSlot : SlotAt D E q (s.index 21) s) (hy : 7≤ s.index 20) (hq : 7≤ s.index 21)
    (hs : SlotSafe P m) (hp : ∀ x≤4*(n+1)^2,P (x:ℚ))
    (fm : SlotFrame s m) (cm : SlotCursor s m (2+n) (2+2*n)) (hm : m.index 23=1) :
    ∃ t k, k≤25*n+2 ∧ Block.Eval (SlotSafe P) pairSweep m k t ∧ SlotFrame s t ∧
      SlotCursor s t 2 (2+n) ∧ (order y.val=order q.val → t.index 23=orderCode (pairBody y.val) (pairBody q.val)) := by
  have start : Sweep P y q s (m.putIndex 28 0) 0 := by
    refine ⟨hs,fm.putIndex _ _ (by decide) (by decide),?_,by simp,fun _ => ?_⟩
    · convert cm.putLoop 0 using 1; omega
    · have hy := order_le y.val
      have hq := order_le q.val
      simp [List.drop_eq_nil_of_le,orderCode,hy,hq,hm]
  obtain ⟨t,k,hk,run,ht⟩ := Block.Eval.forRange_invariant (safe := SlotSafe P)
    (body := .seq (slotMoves backMoves) comparePairs) 28 22 n 22 (fun j t => Sweep P y q s t j)
    m hs start (fun j t h => ⟨h.safe,h.counter,(h.frame.index _ (by decide)).trans hn⟩) (by
      intro j hj v h
      let i := n-(j+1)
      have hi : i<n := by dsimp [i]; omega
      have hi' : n-j=i+1 := by dsimp [i]; omega
      let z := afterMoves v backMoves
      have ez := slotMoves_eval P v backMoves h.safe
      have fz : SlotFrame s z := h.frame.trans (afterMoves_frame v backMoves (by simp [backMoves,SlotMove.dst]))
      have cz : SlotCursor s z (2+i) (2+n+i) := by
        convert h.cursor.back (by omega) (by omega) using 1 <;> omega
      have zl : 7≤z.index 25 := by rw [cz.leftCol]; omega
      have zr : 7≤z.index 26 := by rw [cz.rightRow]; omega
      have zc : 7≤z.index 27 := by rw [cz.rightCol]; omega
      obtain ⟨w,l,hl,ew,g⟩ := comparePairs_spec P z n (rowWord y.val i) (colWord y.val i)
        (rowWord q.val i) (colWord q.val i)
        (by rw [cz.leftRow,fz.high (by omega)]; simpa [Nat.add_assoc] using ySlot.rows ⟨i,hi⟩)
        (by rw [cz.leftCol,fz.high (by omega)]; simpa [Nat.add_assoc] using ySlot.cols ⟨i,hi⟩)
        (by rw [cz.rightRow,fz.high (by omega)]; simpa [Nat.add_assoc] using qSlot.rows ⟨i,hi⟩)
        (by rw [cz.rightCol,fz.high (by omega)]; simpa [Nat.add_assoc] using qSlot.cols ⟨i,hi⟩)
        zl zr zc (rowWord_le _ hd _) (colWord_le _ _) (rowWord_le _ hd _) (colWord_le _ _) ez.safe_end hp
      have z28 : z.index 28=v.index 28 := afterMoves_index v backMoves 28 (by simp [backMoves,SlotMove.dst])
      have z23 : z.index 23=v.index 23 := afterMoves_index v backMoves 23 (by simp [backMoves,SlotMove.dst])
      have cw := cz.of_preserved (fun x h1 h2 => g.index x (by omega))
      refine ⟨w,4+l,by omega,ez.seq ew,⟨ew.safe_end,(fz.trans g.frame).putIndex _ _ (by decide) (by decide),
        cw.putLoop _,?_,?_⟩⟩
      · simp [g.index 28 (by decide),z28,h.counter]
      · intro ho
        rw [Memory.putIndex_ne _ (by decide : 23≠28),g.result,z23,h.result ho,hi']
        exact (pairBody_drop_code y.val q.val ho i).symm)
  exact ⟨t,k,by omega,run,ht.frame,by simpa using ht.cursor,by simpa using ht.result⟩

end GeneratorTable
end Compression
end LinearProgramming
end Optimization
end OAI
