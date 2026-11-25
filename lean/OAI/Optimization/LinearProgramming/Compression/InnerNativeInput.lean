import OAI.Optimization.LinearProgramming.Compression.MetadataInput
import OAI.Optimization.LinearProgramming.BitRAM.NativeInstall
import OAI.Optimization.LinearProgramming.OracleSpec.PriceEncoding

/-! The native minor program receives only arithmetic registers. This block writes its
true four-field bit input and fills the initial stack, preserving the numerical sign cache. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression
namespace Inner
open RAM RAM.Block RAM.Tape OracleSpec BitRAM

theorem metadata_word_length (n g : Nat) (member : Bool) (rank : Nat) (hgr : rank≤g) :
    (inputWord n g member rank).length ≤ 4*(n+g+1)+2 := by
  have small : rank.bits.length ≤ rank := by
    rw [Nat.size_eq_bits_len]
    exact Nat.size_le.mpr (Nat.lt_two_pow_self (n := rank))
  simp only [inputWord,List.length_append,frame_length,List.length_replicate,List.length_singleton,encodeNat]
  omega

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] {P : K→Prop}

/-- The concrete emitter and loader share one physical execution. Its time depends on
the variable dimensions; the scratch windows may live at arbitrarily chosen addresses. -/
theorem installControlInput_correct (p : BitProgram) (s : Memory K) (n g : Nat) (member : Bool) (rank : Nat)
    (hs : s.AllData P) (zero : P 0) (one : P 1) (base : 3 ≤ s.index 47)
    (hn : s.index 57=n) (hg : s.index 59=g) (hm : s.index 61=member.toNat) (hr : s.index 63=rank)
    (hgr : rank≤g) :
    ∃ k≤300*(n+g+1)^2+p.stackCount+100, ∃ t,
      Eval (Memory.AllData P) (BitRAM.installControlInput p Metadata.writeInputBlock) s k t ∧
      Rep p (p.initial (inputWord n g member rank)) t ∧ MetadataEffect s t (inputWord n g member rank) := by
  obtain ⟨u,j,emit,he,word⟩ := Metadata.writeInputBlock_correct s n g member rank hs zero one base hn hg hm hr hgr
  obtain ⟨t,run,rep,effect⟩ := BitRAM.installControlInput_correct (p:=p) emit word zero base
  have length := metadata_word_length n g member rank hgr
  have square : n+g+1 ≤ (n+g+1)^2 := by
    simpa only [pow_two,Nat.mul_one] using Nat.mul_le_mul_left (n+g+1) (show 1≤n+g+1 by omega)
  exact ⟨_,by omega,t,run,rep,effect⟩

end Inner
end Compression
end LinearProgramming
end Optimization
end OAI
