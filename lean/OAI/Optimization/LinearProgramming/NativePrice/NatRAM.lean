import OAI.Optimization.LinearProgramming.NativePrice.Scan
import OAI.Optimization.LinearProgramming.NativePrice.Horner

/-! Decode the canonical interleaved natural and advance the shared packet cursor. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace NativePrice

open RAM OracleSpec

def natBlock : Block :=
  .seq (.op (.addrCopy 5 3)) <| .seq scanBlock <| .seq (.op (.addrCopy 4 3)) <|
    .seq (.op (.incr 3 3)) hornerBlock

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

theorem natBlock_spec (P : K → Prop) (n : ℕ) (s : Memory K) (c : ℕ) (hc : s.index 3=c)
    (hbase : 9 ≤ c) (hw : WordAt s c (encodeNat n)) (hm : s.AllData P)
    (hP : ∀ v : ℕ, v≤2^n.bits.length → P (v:K)) :
    ∃ t k, k≤16*(encodeNat n).length+16 ∧ Block.Eval (Memory.AllData P) natBlock s k t ∧
      t.data 3=(n:K) ∧ t.index 3=c+(encodeNat n).length ∧
      (∀ j, j<3 ∨ 6<j → t.data j=s.data j) ∧
      ∀ j, j<3 ∨ 6<j → t.index j=s.index j := by
  let a := s.putIndex 5 (s.index 3)
  have ea := Block.Eval.op_addrCopy s 5 3 hm hm
  have h0 : P (0:K) := by simpa using hP 0 (Nat.zero_le _)
  obtain ⟨z,ez,pos,df,af⟩ := scanBlock_spec P a c n.bits (by simpa [a] using hc) hbase hw
    ea.safe_end h0
  let b := z.putIndex 4 (z.index 3)
  let u := b.putIndex 3 (b.index 3+1)
  have eb := Block.Eval.op_addrCopy z 4 3 ez.safe_end ez.safe_end
  have eu := Block.Eval.op_incr b 3 3 eb.safe_end eb.safe_end
  have hstart : u.index 5=c := by simpa [u,b,a,hc] using af 5 (by decide)
  have hend : u.index 4=c+2*n.bits.length := by simpa [u,b] using pos
  have tape : WordAt u c (frame n.bits) :=
    hw.of_data (fun j hj _ => df j (by omega) (by omega))
  obtain ⟨t,et,acc,fd,fi⟩ := hornerBlock_spec P u c n.bits hstart hend hbase tape eu.safe_end hP
  refine ⟨t,_,?_,ea.seq (ez.seq (eb.seq (eu.seq et))),?_,?_,?_,?_⟩
  · simp only [encodeNat,frameLen]
    omega
  · simpa [value_bits] using acc
  · rw [fi 3 (by decide)]
    simp [u,b,pos,encodeNat,frameLen,Nat.add_assoc]
  · intro j hj
    exact (fd j (by omega) (by omega)).trans (df j (by omega) (by omega))
  · intro j hj
    rw [fi j (by omega)]
    simp only [u,b,Memory.putIndex_ne _ (show j≠3 by omega),Memory.putIndex_ne _ (show j≠4 by omega)]
    have h := af j (by omega)
    simpa [a,show j≠5 by omega] using h

end NativePrice
end LinearProgramming
end Optimization
end OAI
