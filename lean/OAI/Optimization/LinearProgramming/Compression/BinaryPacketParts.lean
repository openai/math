import OAI.Optimization.LinearProgramming.Compression.SignWireField
import OAI.Optimization.LinearProgramming.NativePrice.RatRAM

/-! Read the two canonical integer components of a rational directly from its
flat bit packet. They occupy the input cells of the canonical word publisher. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression

open RAM NativePrice OracleSpec

def packetRationalParts : Block :=
  .seq (.op (.const 8 0)) <| .seq SignWire.signedFieldBlock <| .seq (.op (.copy 0 3)) <|
    .seq natBlock (.op (.copy 1 3))

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

theorem packetRationalParts_spec (P : K → Prop) (q : ℚ) (m : Memory K) (c : ℕ)
    (hc : m.index 3=c) (hc9 : 9 ≤ c) (wire : WordAt m c (encodeRat q)) (hm : m.AllData P)
    (safeNat : ∀ v : ℕ, v ≤ 2^(max q.num.natAbs.bits.length q.den.bits.length) → P (v:K))
    (safeNum : P (q.num:K)) :
    ∃ t k, k ≤ 16*(encodeRat q).length+27 ∧ Block.Eval (Memory.AllData P) packetRationalParts m k t ∧
      t.data 0=(q.num:K) ∧ t.data 1=(q.den:K) ∧ t.index 3=c+(encodeRat q).length ∧
      (∀ i, i=2 ∨ 8 < i → t.data i=m.data i) ∧ (∀ i, i < 3 ∨ 6 < i → t.index i=m.index i) := by
  let num := SignWire.fieldWord q.num
  let den := encodeNat q.den
  have encoding : encodeRat q=num++den := rfl
  obtain ⟨numWord,denWord⟩ := wordAt_append.mp (encoding ▸ wire : WordAt m c (num++den))
  let z := m.putData 8 0
  have p0 : P 0 := by simpa using safeNat 0 (Nat.zero_le _)
  have start : Block.Eval (Memory.AllData P) (.op (.const 8 0)) m 1 z := by
    simpa [z] using Block.Eval.op_const m 8 0 hm (by simpa using hm.putData 8 p0)
  have nword : WordAt z c num := numWord.of_data (by
    intro i hi _
    exact Memory.putData_ne m (by omega) _)
  obtain ⟨u,kn,hn,numRun,val,cur,ns,ni⟩ := SignWire.signedFieldBlock_spec P q.num z c
    start.safe_end hc hc9 (by simp [z]) nword
    (fun v hv => safeNat _ (hv.trans (Nat.pow_le_pow_right (by decide) (Nat.le_max_left _ _)))) safeNum
  let s := u.putData 0 (u.data 3)
  have save := Block.Eval.op_copy (safe := Memory.AllData P) u 0 3 numRun.safe_end
    (numRun.safe_end.putData 0 (numRun.safe_end 3))
  have dword : WordAt s (c+num.length) den := denWord.of_data (by
    intro i hi _
    exact (Memory.putData_ne u (show i ≠ 0 by omega) _).trans
      ((ns i (.inr (by omega))).trans (Memory.putData_ne m (by omega) _)))
  obtain ⟨v,kd,hd,denRun,dval,dcur,ds,di⟩ := natBlock_spec P q.den s (c+num.length)
    cur (by omega) dword save.safe_end
    (fun x hx => safeNat _ (hx.trans (Nat.pow_le_pow_right (by decide) (Nat.le_max_right _ _))))
  let t := v.putData 1 (v.data 3)
  have emit := Block.Eval.op_copy (safe := Memory.AllData P) v 1 3 denRun.safe_end
    (denRun.safe_end.putData 1 (denRun.safe_end 3))
  have len : (encodeRat q).length=num.length+den.length := by rw [encoding,List.length_append]
  have hkn : kn ≤ 16*num.length+8 := hn
  have hkd : kd ≤ 16*den.length+16 := hd
  refine ⟨t,1+(kn+(1+(kd+1))),by omega,start.seq (numRun.seq (save.seq (denRun.seq emit))),?_,
    (Memory.putData_same ..).trans dval,?_,?_,?_⟩
  · exact (Memory.putData_ne v (by decide : 0 ≠ 1) _).trans
      ((ds 0 (.inl (by decide))).trans ((Memory.putData_same u 0 _).trans val))
  · change v.index 3=_
    rw [dcur,len,Nat.add_assoc]
  · intro i hi
    exact (Memory.putData_ne v (by omega) _).trans ((ds i (by omega)).trans
      ((Memory.putData_ne u (by omega) _).trans ((ns i (by omega)).trans (Memory.putData_ne m (by omega) _))))
  · intro i hi
    exact (di i hi).trans (ni i hi)

/-- Every scalar constructed by the decoding stage has at most three bits
more than the wire length. Input scalars use their original bound. -/
theorem packetRationalParts_bits (q : ℚ) (m : Memory ℚ) (c B : ℕ)
    (hc : m.index 3=c) (hc9 : 9 ≤ c) (wire : WordAt m c (encodeRat q))
    (hm : m.AllData (fun v => ratBits v ≤ B)) :
    ∃ t k, k ≤ 16*(encodeRat q).length+27 ∧
      Block.Eval (Memory.AllData (fun v => ratBits v ≤ max B (3+(encodeRat q).length)))
        packetRationalParts m k t ∧
      t.data 0=(q.num:ℚ) ∧ t.data 1=(q.den:ℚ) ∧ t.index 3=c+(encodeRat q).length ∧
      (∀ i, i=2 ∨ 8 < i → t.data i=m.data i) ∧ (∀ i, i < 3 ∨ 6 < i → t.index i=m.index i) := by
  obtain ⟨hn,hs,_⟩ := ratBlock_bit_conditions q
  exact packetRationalParts_spec _ q m c hc hc9 wire (fun i => (hm i).trans (Nat.le_max_left ..))
    (fun v hv => (hn v hv).trans (Nat.le_max_right ..)) (hs.trans (Nat.le_max_right ..))

end Compression
end LinearProgramming
end Optimization
end OAI
