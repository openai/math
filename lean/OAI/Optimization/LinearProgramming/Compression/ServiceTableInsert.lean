import OAI.Optimization.LinearProgramming.Compression.ServiceTableInsertMoves
import OAI.Optimization.LinearProgramming.Compression.GeneratorInsertState

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression
namespace GeneratorTable

open RAM

/-- Insert a fresh generator at its physical rank, transport the complete rows and publish
the new scalar count. The rank pointer is computed from the live table. -/
def insertAtRank : Block := .seq openInsertion (.seq moveRight (.seq prepareFill (.seq copyIncoming publishCount)))

def insertCost (n g pos : ℕ) := wordInsertCost (stride n) g pos

theorem insertCost_le (n g pos : ℕ) (hp : pos ≤ g) : insertCost n g pos ≤ 30*(g+1)*(stride n+1) :=
  wordInsertCost_le _ _ _ hp

/-- Exact time, sorted mathematical result, input matrix/header frame, and preservation of
the protected native request bank for the complete sorted insertion block. -/
theorem insertAtRank_spec {d e n : ℕ} (D : Matrix (Fin d) (Fin n) ℚ) (E : Matrix (Fin e) (Fin n) ℚ)
    (keys : List (NonzeroPairMinor D E)) (q : NonzeroPairMinor D E) (P : ℚ→Prop) (s : Memory ℚ)
    (hkeys : Stored D E keys s) (hreq : SlotAt D E q (slotBase n (keys.length+1)) s) (fresh : q∉keys)
    (h14 : s.index 14 = tableBase n) (h18 : s.index 18 = stride n) (h19 : s.index 19 = rank q keys)
    (h20 : s.index 20 = slotBase n keys.length) (h21 : s.index 21 = slotBase n (keys.length+1))
    (hs : s.AllData P) (hone : P 1) (hcount : P ((keys.length+1:ℕ):ℚ)) :
    ∃t,Block.Eval (Memory.AllData P) insertAtRank s (insertCost n keys.length (rank q keys)) t ∧
      Stored D E (keys.insertIdx (rank q keys) q) t ∧ (∀a,40 ≤ a → t.index a = s.index a) ∧
      ∀a,a ≠ 0 → a ≠ 4 → a < tableBase n → t.data a = s.data a := by
  let g := keys.length
  let pos := rank q keys
  have hp : pos ≤ g := rank_le_length _ _
  obtain ⟨b,eb,bd,b8,b9,b10,bi⟩ := openInsertion_spec P s (tableBase n) (stride n) pos h14 h18 h19 hs
  obtain ⟨c,ec,sh⟩ := shiftSlots_spec P b n pos g hp (b8.trans h20) (b9.trans h21) b10 eb.safe_end
  obtain ⟨z,ez,zd,z8,z9,z11,zi⟩ := prepareFill_spec P c ec.safe_end
  have c21 := (sh.indices 21 (by decide) (by decide)).trans ((bi 21 (by decide)).trans h21)
  have c18 := (sh.indices 18 (by decide) (by decide)).trans ((bi 18 (by decide)).trans h18)
  obtain ⟨v,ev,fill⟩ := copyIncoming_spec P z n pos g hp (z8.trans c21) (z9.trans sh.source) (z11.trans c18) ez.safe_end
  have low (i : ℕ) : 4 < slotBase n i := by unfold slotBase tableBase; omega
  have v4 : v.data 4 = (g:ℚ) := by
    rw [fill.frame 4 (by decide) (Or.inl (low _)),zd,sh.frame 4 (by decide) (Or.inl (low _)),bd,hkeys.count]
  have next : P (v.data 4+1) := by simpa [v4,g,Nat.cast_add] using hcount
  obtain ⟨t,et,t4,ti,td⟩ := publishCount_spec P v ev.safe_end hone next
  refine ⟨t,eb.seq (ec.seq (ez.seq (ev.seq et))),?_,?_,?_⟩
  · exact (hkeys.of_data bd).inserted fresh (hreq.of_data bd) sh zd fill t4
      (fun j hj => td j (by unfold tableBase at hj;omega) (by unfold tableBase at hj;omega))
  · intro j hj
    rw [ti,fill.indices j (by omega) (by omega) (by omega),zi j (by omega),
      sh.indices j (by omega) (by omega),bi j (by omega)]
  · intro j h0 h4 hlow
    have below (i : ℕ) : j < slotBase n i := by unfold slotBase; omega
    rw [td j h0 h4,fill.frame j h0 (Or.inl (below _)),zd,sh.frame j h0 (Or.inl (below _)),bd]

end GeneratorTable
end Compression
end LinearProgramming
end Optimization
end OAI
