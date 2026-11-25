import OAI.Optimization.LinearProgramming.Compression.BinaryWidthRAM

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression

open RAM OracleSpec.MinorLog

/-- Internal scalar return format, before its compact public address-bank publication. -/
structure PaddedReply (m : Memory ℚ) (q : ℚ) (k : ℕ) : Prop where
  value : m.data 6 = q
  sign : m.data 7 = (if q.num < 0 then 1 else 0)
  num : ∀ j < k, m.data (10+j) = ((integerDigit q.num.natAbs j : ℕ) : ℚ)
  den : ∀ j < k, m.data (10+k+j) = ((integerDigit q.den j : ℕ) : ℚ)

theorem PaddedReply.preserve {m t : Memory ℚ} {q : ℚ} {k : ℕ} (buffer : PaddedReply m q k)
    (frame : ∀ i, 6 ≤ i → t.data i = m.data i) : PaddedReply t q k :=
  ⟨(frame 6 (by decide)).trans buffer.value,(frame 7 (by decide)).trans buffer.sign,
    fun j h => (frame _ (by omega)).trans (buffer.num j h),
    fun j h => (frame _ (by omega)).trans (buffer.den j h)⟩

structure SizedReply (m : Memory ℚ) (q : ℚ) (k : ℕ) : Prop extends PaddedReply m q k where
  numeratorWidth : m.data 1 = (width q.num.natAbs : ℚ)
  denominatorWidth : m.data 2 = (width q.den : ℚ)
  position : m.data 4 = ((k+1 : ℕ) : ℚ)

def sizePublicWords : Block :=
  .seq (.op (.addrConst 1 10)) (.seq (widthScanBlock 1) (widthScanBlock 2))

theorem sizePublicWords_spec (m : Memory ℚ) (q : ℚ) (k : ℕ) {P : ℚ → Prop}
    (safe : m.AllData P) (hk : m.index 0 = k) (inrange : q.num.natAbs < 2^k ∧ q.den < 2^k)
    (buffer : PaddedReply m q k) (small : ∀ z : ℕ, z ≤ k+1 → P (z:ℚ)) :
    ∃ t, Block.Eval (Memory.AllData P) sizePublicWords m (16*k+11) t ∧ SizedReply t q k := by
  let m0 := m.putIndex 1 10
  have init := Block.Eval.op_addrConst m 1 10 safe (safe.putIndex _ _)
  obtain ⟨u,nrun,wn,_,_,ptr,uf,ui⟩ := widthScanBlock_spec m0 q.num.natAbs k 10 1 init.safe_end
    (Or.inl rfl) hk (by simp [m0]) (by decide) inrange.1 buffer.num small
  have ub : PaddedReply u q k := buffer.preserve (fun i hi => uf i (by omega) (by omega) (by omega) (by omega))
  obtain ⟨v,drun,wd,pos,_,_,vf,_⟩ := widthScanBlock_spec u q.den k (10+k) 2 nrun.safe_end
    (Or.inr rfl) ((ui 0 (by decide) (by decide)).trans hk) ptr (by omega) inrange.2 ub.den small
  have vb : PaddedReply v q k := ub.preserve (fun i hi => vf i (by omega) (by omega) (by omega) (by omega))
  refine ⟨v,?_,⟨vb,(vf 1 (by decide) (by decide) (by decide) (by decide)).trans wn,wd,pos⟩⟩
  simpa only [sizePublicWords,show 1+(8*k+5+(8*k+5))=16*k+11 by omega] using init.seq (nrun.seq drun)

end Compression
end LinearProgramming
end Optimization
end OAI
