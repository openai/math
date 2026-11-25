import OAI.Optimization.LinearProgramming.Lattice.BitRoundDialogue

/-! Sizes of the physical word-dialogue frames, including both nested integer
tables and the two actual answer bits. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Lattice
namespace Bit
namespace Driver

open ExactQuantumFactoring.BitStackProgram ExactQuantumFactoring.BitStackProgram.Procedure OracleSpec

theorem signPacket_length_le (a : Row) : (signPacket a).length ≤ (intRowCode a).length := by
  have hc (z : ℤ) : (intCode z).length = z.natAbs.size+3 := by
    simp [intCode,intData,prodCode,pairBits_length,boolCode,Nat.size_eq_bits_len]
    omega
  induction a with
  | nil => decide
  | cons z zs ih =>
    change (signedField z ++ signPacket zs).length ≤ (listCode intCode (z::zs)).length
    rw [List.length_append,listCode_length_cons,hc]
    simp only [signedField,List.length_cons,Contraction.encodeNat_length]
    change (signPacket zs).length ≤ (listCode intCode zs).length at ih
    omega

theorem continuation_length (answer : Word) (e : Env) (c : Probe.Carry) :
    (WordDialogue.stateCode inputCode carryCode (.inr (answer,(e,c)))).length =
      2*answer.length+2*(envCode e).length+(Probe.carryCode c).length+3 := by
  have hframe : (frame answer).length = 2*answer.length+1 := by
    rw [← quoteBits_eq_frame,quoteBits_length]
  simp only [WordDialogue.stateCode,List.length_cons,List.length_append,carryCode,prodCode,pairBits_length,hframe]
  omega

theorem opening_length (p M : ℕ) :
    (WordDialogue.stateCode inputCode carryCode (.inl (p,M))).length = 2*p+M.size+2 := by
  simp [WordDialogue.stateCode,inputCode,prodCode,pairBits_length,unaryCode,Nat.size_eq_bits_len]

theorem sign_requestFits (reply : Word → Word) (a : Row) (e : Env) (c : Probe.Carry)
    (E B L : ℕ) (hE : (envCode e).length ≤ E)
    (hrow : (intRowCode a).length ≤ B) (hcarry : (Probe.carryCode c).length ≤ B)
    (hs : (reply (signPacket a)).length ≤ 2) (hL : 2*E+B+7 ≤ L) :
    requestFits L reply (signPacket a,(e,c)) := by
  change (signPacket a).length ≤ L ∧ (reply (signPacket a)).length ≤ L ∧
    (WordDialogue.stateCode inputCode carryCode (.inr (reply (signPacket a),(e,c)))).length ≤ L
  refine ⟨(signPacket_length_le a).trans (hrow.trans (by omega)),hs.trans (by omega),?_⟩
  rw [continuation_length]
  omega

end Driver
end Bit
end Lattice
end LinearProgramming
end Optimization
end OAI
