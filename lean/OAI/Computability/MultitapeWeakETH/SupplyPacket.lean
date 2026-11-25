import OAI.Computability.MultitapeWeakETH.PacketSpan

/-! # The parent output packet as a physical source for reverse-copy frames -/

namespace OAI.Computability.MultitapeWeakETH.OperandSpan

open IntegerMultiplication Code VPVNP BurstRAM PairSimulation NodeArguments NativeGrid TerminalWords
open scoped Fin.CommRing
noncomputable section

/-- Place the output packet at address zero. Every bit is read from its
position on the supplied tape, with the native stack-memory encoding. -/
theorem packet_at_zero {w : ℕ} (bs : Bits.Word) (stride : ℕ)
    (fits : bs.length ≤ stride) (room : bs.length ≤ 2^w) :
    let A : Arena := ⟨0,stride⟩
    let P : Packet := ⟨0,bs⟩
    P.Fits A w 0 ∧ P.Stored A (DFS.scratch 0 (memory (w:=w) bs)) := by
  intro A P
  have base : A.base 0 = 0 := by simp [A,Arena.base]
  refine ⟨⟨Nat.zero_le _,fits,by simpa only [P,base,Nat.zero_add] using room⟩,?_⟩
  intro i
  have bound : i.val < bs.length := i.isLt
  change rawScratch (DFS.scratch 0 (memory bs)) ((A.base 0 + i.val : ℕ) : Word w) =
    PrivateFields.bitValue w bs[i.val]
  rw [base,Nat.zero_add]
  change PrimedInputRAM.encodeBit w (cell (bs,wordBits (i.val : Word w))) = _
  simp only [cell,capped,value_native,Fin.val_cast_of_lt (bound.trans_le room),ruler_length,
    Nat.min_eq_left bound.le,Iter.search _ _ _ bound]
  rfl

end
end OAI.Computability.MultitapeWeakETH.OperandSpan
