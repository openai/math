import OAI.Computability.VPVNP.RankQueryStackGramPorts

/-! # Input bank and bounds for the physical weighted Gram interpreter -/

namespace OAI
namespace Computability
namespace VPVNP

namespace RankQuery.Stack.GramEngine

open Engine RAMTape BurstRAM Dispatch

variable {K : Type} {w v n m p e : ℕ} {c : SliceArithmetic.Vector p e}

private def registers (w : ℕ) (slot : Fin 8) (value : ℕ) : EngineAlias.Reg → Word w :=
  fun i => if i.val = slot.val then Fin.ofNat _ value else 0

/-- Put the two matrix dimensions, the field arithmetic advice, and the
underlying entry reader's initial work bank on their literal ports. -/
def initial (w v n m : ℕ) (c : SliceArithmetic.Vector p e) (reader : Stacks K) : Stacks (Aux K)
  | .inl (.inl i) => ISA.bank Fin.elim0 (0 : Word w) (registers w 7 n) [] i
  | .inl (.inr z) => GramScalar.bank (GramScalar.wordBank 0 (registers w 3 m))
      (GramRead.arithmeticBank v c [] []) reader z
  | .inr none => []
  | .inr (some i) => MultiplyAdd.expected v c i

theorem initial_ready {readerReady : Stacks K → Prop} (reader : Stacks K) (hr : readerReady reader)
    (hn : n < 2^w) (hm : m < 2^w) : Ready w v n m c readerReady (initial w v n m c reader) := by
  refine ⟨⟨registers w 7 n, 0, ?_, ?_, fun _ => rfl⟩, rfl, fun _ => rfl,
    ⟨registers w 3 m, 0, reader, ?_, hr, fun _ => rfl⟩⟩
  · simp [registers, Code.inReg]
  · simp [registers, Code.inReg, Nat.mod_eq_of_lt hn]
  · intro i hi
    fin_cases i <;> first | omega | simp [registers, Code.inReg, gramInput, Nat.mod_eq_of_lt hm]

private theorem isa_length (rs : Dispatch.Regs EngineAlias.R w) (persistent : Word w) (i : EngineAlias.Small) :
    (ISA.bank Fin.elim0 persistent rs [] i).length ≤ w := by
  cases i with
  | reg i => simp [ISA.bank]
  | pub i => exact Fin.elim0 i
  | persistent => simp [ISA.bank]
  | work i => exact Nat.zero_le _
  | logPort i => cases i <;> exact Nat.zero_le _

/-- Size of every auxiliary stack at an instruction boundary, independent of
the time spent by the matrix entry reader. -/
theorem ready_length {readerReady : Stacks K → Prop} {s : Stacks (Aux K)} {A : ℕ}
    (hs : Ready w v n m c readerReady s) (ha : ∀ r, readerReady r → ∀ k, (r k).length ≤ A) :
    ∀ i, (s i).length ≤ w+v+e+e*v+A := by
  obtain ⟨⟨lr, lp, _, _, lh⟩, scratchEmpty, mac, ⟨gr, gp, base, _, hbase, gh⟩⟩ := hs
  rintro ((i|z)|i)
  · change (s (bank i)).length ≤ _
    rw [lh]
    exact (isa_length lr lp i).trans (by omega)
  · change ((s ∘ Sum.inl) (.inr z)).length ≤ _
    rw [gh]
    cases z with
    | words i => exact (isa_length gr gp i).trans (by omega)
    | aux i => exact (ha base hbase i).trans (by omega)
    | mul i =>
      rcases i with i | i
      · exact Nat.zero_le _
      · cases i <;> simp [GramScalar.bank, GramRead.arithmeticBank, SliceArithmetic.MultiplyCall.clean,
          SliceArithmetic.MultiplyCall.external] <;> omega
    | _ => exact Nat.zero_le _
  · cases i with
    | none => change (s scratch).length ≤ _; rw [scratchEmpty]; exact Nat.zero_le _
    | some i =>
      change (s (macPort i)).length ≤ _
      rw [mac i]
      rcases i with i | i
      · exact Nat.zero_le _
      · cases i <;> simp [MultiplyAdd.expected] <;> omega

end RankQuery.Stack.GramEngine

end VPVNP
end Computability
end OAI
