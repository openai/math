import OAI.Optimization.LinearProgramming.RAM.NatCast
import OAI.Optimization.LinearProgramming.RAM.Array
import OAI.Optimization.LinearProgramming.Geometry.FrankWolfe

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Geometry
namespace FWRAM

open RAM

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- Initialize scalar dimension (11), round counter (12), and round limit (13). -/
def setupBlock : Block :=
  .seq (natCastBlock 11 14 32 23)
    (.straight [.const 13 8000000, .mul 13 13 11, .mul 13 13 11, .mul 13 13 11, .const 12 0])

theorem setupBlock_spec (P : K → Prop) (m : Memory K) (n : ℕ) (hn : m.index 23=n)
    (hm : m.AllData P) (h1 : P 1) (hv : ∀ j≤n, P (j:K))
    (hM : ∀ j:Fin 4, P (8000000*(n:K)^j.val)) :
    ∃ t, Block.Eval (Memory.AllData P) setupBlock m (4*n+9) t ∧
      t.data 11=(n:K) ∧ t.data 12=0 ∧ t.data 13=(fwRounds n:K) ∧
      (∀ k, k≠32 → t.index k=m.index k) ∧ (∀ k, 23<k → t.data k=m.data k) := by
  obtain ⟨s,e,hd,_,_,hidx,hdta⟩ := natCastBlock_correct P m 11 14 32 23 n (by decide) (by decide)
    hn hm h1 hv
  have hsafe : s.AllData P := e.safe_end
  let s0 := s.putData 13 8000000
  let s1 := s0.putData 13 (8000000*(n:K))
  let s2 := s1.putData 13 (8000000*(n:K)*(n:K))
  let s3 := s2.putData 13 (8000000*(n:K)*(n:K)*(n:K))
  let t := s3.putData 12 0
  have h0 : s0.AllData P := hsafe.putData _ (by simpa using hM 0)
  have ha : s1.AllData P := h0.putData _ (by simpa using hM 1)
  have hb : s2.AllData P := ha.putData _ (by simpa [pow_two,mul_assoc] using hM 2)
  have hc : s3.AllData P := hb.putData _ (by simpa [pow_succ,mul_assoc] using hM 3)
  have ht : t.AllData P := hc.putData _ (by simpa using hv 0 (Nat.zero_le _))
  have e0 : Block.Eval (Memory.AllData P) (.op (.const 13 8000000)) s 1 s0 := by
    simpa [s0] using Block.Eval.op_const s 13 8000000 hsafe (by simpa using h0)
  have e1 : Block.Eval (Memory.AllData P) (.op (.mul 13 13 11)) s0 1 s1 := by
    simpa [s1,s0,hd] using Block.Eval.op_mul s0 13 13 11 h0 (by simpa [s0,hd] using ha)
  have e2 : Block.Eval (Memory.AllData P) (.op (.mul 13 13 11)) s1 1 s2 := by
    simpa [s2,s1,s0,hd] using Block.Eval.op_mul s1 13 13 11 ha (by simpa [s1,s0,hd] using hb)
  have e3 : Block.Eval (Memory.AllData P) (.op (.mul 13 13 11)) s2 1 s3 := by
    simpa [s3,s2,s1,s0,hd] using Block.Eval.op_mul s2 13 13 11 hb (by simpa [s2,s1,s0,hd] using hc)
  have e4 : Block.Eval (Memory.AllData P) (.op (.const 12 0)) s3 1 t := by
    simpa [t] using Block.Eval.op_const s3 12 0 hc (by simpa using ht)
  refine ⟨t,?_,?_,?_,?_,hidx,?_⟩
  · have ea := e.seq (e0.seq (e1.seq (e2.seq (e3.seq (e4.seq (.skip ht))))))
    exact ea
  · simpa [t,s3,s2,s1,s0] using hd
  · simp [t]
  · simp [t,s3,fwRounds]
    ring
  · intro k hk
    have h11 : k≠11 := by omega
    have h12 : k≠12 := by omega
    have h13 : k≠13 := by omega
    have h14 : k≠14 := by omega
    simpa [t,s3,s2,s1,s0,h12,h13] using hdta k h11 h14

end FWRAM
end Geometry
end LinearProgramming
end Optimization
end OAI
