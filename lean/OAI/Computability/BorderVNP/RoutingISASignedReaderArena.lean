import OAI.Computability.BorderVNP.RoutingISASignedTaskArena
import OAI.Computability.BorderVNP.TransmissionChosenArena
import OAI.Computability.BorderVNP.DiagonalResidueRAMSources

/-! # Physical addresses of the row, column and tally operands of the chosen reader -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.SignedTaskArena

open VPVNP.BurstRAM DiagonalResidueRAM ResidueEntryInput TeamContraction.ProcessorSlots

/-- Place gate valuations immediately after all serialized tally digits. -/
noncomputable def Layout.valuation (l : Layout) (w : ℕ) := l.tallyBits+l.dim*w+1

/-- Start of the six header words, three words per gate, and the actual gather addresses. -/
noncomputable def Layout.entry (l : Layout) (w u v k : ℕ) := gateBase (l.valuation w) u v+k

/-- One-past high-water word of the entire signed computation. -/
noncomputable def Layout.endAddress (l : Layout) (w u v k : ℕ) :=
  l.entry w u v k+(6+3*k+u)

/-- The matrix circuit's advised addresses are the same real row and column
arrays as the raw pin preparation, and the fixed output of the aligned tally. -/
noncomputable def Layout.readerPlacement {w : ℕ} (l : Layout) (A : StartupArena) (u v k raw team subt : ℕ)
    (old : Fin 81 → Word w) : Diagonal.ReaderPlacement w :=
  Diagonal.ReaderPlacement.inArena A (l.valuation w) (l.entry w u v k) l.tallyBits
    (l.extension raw team subt old)

/-- All true gather addresses lie before the entry valuation bank, including
all full-width tally digits at their actual native stride. -/
theorem Layout.source_lt_valuation {J : Type*} [Fintype J] (l : Layout) {w pin row col : ℕ}
    (g : Fintype.card J=l.p.report.gadgets)
    (rows : row+(l.p.parameters+2)*pin ≤ l.tallyBits)
    (cols : col+(l.p.parameters+2)*pin ≤ l.tallyBits) (x : Board.Physical l.p.parameters pin w J) :
    sourceAddress row col l.tallyBits x < l.valuation w := by
  have bit (k : ℕ) (hk : k<l.dim) (j : Fin w) :
      l.tallyBits+k*w+j.val<l.valuation w := by
    have t := Nat.mul_le_mul_right w hk
    rw [Nat.succ_mul] at t
    have := j.isLt
    unfold valuation
    omega
  rcases x with ⟨side,j⟩ | ⟨i | t,j⟩
  · cases side <;> simp only [sourceAddress,ite_false,ite_true,Bool.false_eq_true,valuation] <;>
      have := j.isLt <;> omega
  · exact bit _ (by have := i.isLt; unfold dim; omega) j
  · apply bit
    have hi := (Fintype.equivFin J t).isLt
    unfold dim
    omega

/-- A single physical end bound and the actual delivered packet's lower
location give the complete native entry layout, including every source probe. -/
theorem Layout.reader_layout {J : Type*} [Fintype J] (l : Layout) {w pin row col dense v k : ℕ}
    (g : Fintype.card J=l.p.report.gadgets)
    (rows : row+(l.p.parameters+2)*pin ≤ l.tallyBits)
    (cols : col+(l.p.parameters+2)*pin ≤ l.tallyBits) :
    let u := Fintype.card (Board.Physical l.p.parameters pin w J)
    let src := fun i : Fin u ↦ sourceAddress row col l.tallyBits ((Fintype.equivFin _).symm i)
    dense+(6+3*k+u)*w ≤ l.tallyBits → l.endAddress w u v k < 2^w →
      DiagonalResidueRAM.Layout (l.valuation w) (l.entry w u v k) dense src v k w := by
  intro u src low high
  have vst : l.valuation w ≤ l.entry w u v k := by unfold entry gateBase; omega
  have cap : l.entry w u v k < 2^w := by unfold endAddress at high; omega
  have denseSt : dense+(6+3*k+u)*w ≤ l.entry w u v k := by
    apply low.trans
    exact (show l.tallyBits ≤ l.valuation w by unfold valuation; omega).trans vst
  have all (i : Fin u) : src i < l.valuation w := l.source_lt_valuation g rows cols _
  exact ⟨le_rfl,high,denseSt.trans_lt cap,.inl denseSt,fun i ↦ (all i).trans_le (vst.trans cap.le),
    fun i ↦ .inl (all i),fun i ↦ .inl ((all i).trans_le vst)⟩

end RoutingISA.SignedTaskArena

end BorderVNP
end Computability
end OAI
