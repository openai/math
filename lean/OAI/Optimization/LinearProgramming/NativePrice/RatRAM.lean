import OAI.Optimization.LinearProgramming.NativePrice.NatRAM
import OAI.Optimization.LinearProgramming.NativePrice.PacketBits
import Mathlib.Tactic.NormNum

/-! The signed rational reader for a native arithmetic-RAM tape of scalar bits. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace NativePrice

open RAM RAM.Block OracleSpec

private def signBlock : Block :=
  .branch (.scalarLT 4 7) (.op (.sub 8 4 8)) (.op (.copy 8 8))

/-- Read a sign bit and two framed little-endian naturals. The cursor in address
register 3 advances past the denominator. Scalar register 3 receives the quotient. -/
def ratBlock : Block :=
  .seq (.op (.load 7 3)) <| .seq (.op (.incr 3 3)) <| .seq natBlock <|
    .seq (.op (.copy 8 3)) <| .seq natBlock <| .seq (.op (.const 4 0)) <|
    .seq signBlock (.op (.div 3 8 3))

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

private theorem signBlock_spec (P : K → Prop) (a : ℤ) (s : Memory K) (hm : s.AllData P)
    (hzero : s.data 4=0) (hsign : s.data 7=((decide (a<0)).toNat:K))
    (hmag : s.data 8=(a.natAbs:K)) (hP : P (a:K)) :
    ∃ k ≤ 3, Eval (Memory.AllData P) signBlock s k (s.putData 8 (a:K)) := by
  have ht := hm.putData 8 hP
  have absCast : (a.natAbs:K)=|(a:K)| := by rw [Nat.cast_natAbs,Int.cast_abs]
  by_cases h : a<0
  · have ha : (a:K)<0 := Int.cast_lt_zero.mpr h
    have hi : s.data 4-s.data 8=(a:K) := by rw [hzero,hmag,absCast,abs_of_neg ha]; simp
    have test : (Cond.scalarLT 4 7).test s = true := by simp [Cond.test,hzero,hsign,h]
    refine ⟨3,by decide,Eval.branchTrue (k:=1) test ?_⟩
    simpa only [hi] using Eval.op_sub s 8 4 8 hm (by rw [hi]; exact ht)
  · have ha : 0≤(a:K) := by exact_mod_cast (show 0 ≤ a by omega)
    have hi : s.data 8=(a:K) := by rw [hmag,absCast,abs_of_nonneg ha]
    have test : (Cond.scalarLT 4 7).test s = false := by simp [Cond.test,hzero,hsign,h]
    refine ⟨2,by decide,Eval.branchFalse (k:=1) test ?_⟩
    simpa only [hi] using Eval.op_copy s 8 8 hm (by rw [hi]; exact ht)

theorem ratBlock_spec (P : K → Prop) (q : ℚ) (s : Memory K) (c : ℕ) (hc : s.index 3=c)
    (hbase : 9 ≤ c) (hw : WordAt s c (encodeRat q)) (hm : s.AllData P)
    (hPnat : ∀ v : ℕ, v ≤ 2^(max q.num.natAbs.bits.length q.den.bits.length) → P (v:K))
    (hPneg : P (q.num:K)) (hPq : P (q:K)) :
    ∃ t k, k ≤ 24*(encodeRat q).length+40 ∧ Eval (Memory.AllData P) ratBlock s k t ∧
      t.data 3=(q:K) ∧ t.index 3=c+(encodeRat q).length ∧
      (∀ j, j<3 ∨ 8<j → t.data j=s.data j) ∧
      (∀ j, j<3 ∨ 6<j → t.index j=s.index j) := by
  let N := q.num.natAbs
  let D := q.den
  have hword : WordAt s c (decide (q.num<0)::(encodeNat N ++ encodeNat D)) := hw
  obtain ⟨sgn,rem⟩ := wordAt_cons.mp hword
  obtain ⟨num,den⟩ := wordAt_append.mp rem
  let a := s.putData 7 (s.data c)
  let b := a.putIndex 3 (c+1)
  have ha : a.AllData P := hm.putData 7 (hm c)
  have ea : Eval (Memory.AllData P) (.op (.load 7 3)) s 1 a := by
    simpa only [hc,a] using Eval.op_load s 7 3 hm (by simpa only [hc] using ha)
  have eb : Eval (Memory.AllData P) (.op (.incr 3 3)) a 1 b := by
    simpa only [a,b,Memory.putData_index,hc] using Eval.op_incr a 3 3 ha ha
  have wnum : WordAt b (c+1) (encodeNat N) := num.of_data (by
    intro j hj _
    exact Memory.putData_ne s (by omega) _)
  have wden : WordAt b (c+1+(encodeNat N).length) (encodeNat D) := den.of_data (by
    intro j hj _
    exact Memory.putData_ne s (by omega) _)
  obtain ⟨un,kn,hkn,en,nval,ncur,ndat,nidx⟩ := natBlock_spec P N b (c+1) (by simp [b])
    (by omega) wnum ha (fun v hv => hPnat _ (hv.trans
      (Nat.pow_le_pow_right (by decide) (Nat.le_max_left _ _))))
  let f := un.putData 8 (N:K)
  have hf : f.AllData P := en.safe_end.putData 8 (nval ▸ en.safe_end 3)
  have ef : Eval (Memory.AllData P) (.op (.copy 8 3)) un 1 f := by
    simpa only [f,nval] using Eval.op_copy un 8 3 en.safe_end (by rw [nval]; exact hf)
  have denInput : WordAt f (c+1+(encodeNat N).length) (encodeNat D) :=
    wden.of_data (by
      intro j hj _
      exact (Memory.putData_ne un (show j≠8 by omega) _).trans (ndat _ (.inr (by omega))))
  obtain ⟨ud,kd,hkd,ed,dval,dcur,ddat,didx⟩ :=
    natBlock_spec P D f (c+1+(encodeNat N).length) ncur (by omega) denInput hf
      (fun v hv => hPnat _ (hv.trans
        (Nat.pow_le_pow_right (by decide) (Nat.le_max_right _ _))))
  let z := ud.putData 4 0
  have zeroSafe : P (0:K) := by simpa using hPnat 0 (Nat.zero_le _)
  have hz : z.AllData P := ed.safe_end.putData _ zeroSafe
  have ez : Eval (Memory.AllData P) (.op (.const 4 0)) ud 1 z := by
    simpa [z] using Eval.op_const ud 4 0 ed.safe_end (by simpa using hz)
  have zsgn : z.data 7=((decide (q.num<0)).toNat:K) := by
    calc
      z.data 7 = ud.data 7 := by simp [z]
      _ = f.data 7 := ddat _ (.inr (by decide))
      _ = un.data 7 := by simp [f]
      _ = b.data 7 := ndat _ (.inr (by decide))
      _ = _ := by simpa [b,a] using sgn
  have zmag : z.data 8=(q.num.natAbs:K) := by
    calc
      z.data 8 = ud.data 8 := by simp [z]
      _ = f.data 8 := ddat _ (.inr (by decide))
      _ = _ := by simp [f,N]
  let signed := z.putData 8 (q.num:K)
  obtain ⟨kg,hkg,eg⟩ := signBlock_spec P q.num z hz (by simp [z]) zsgn zmag hPneg
  have val3 : signed.data 3=(q.den:K) := by simpa [signed,z,D] using dval
  have val8 : signed.data 8=(q.num:K) := Memory.putData_same _ _ _
  have hden : signed.data 3 ≠ 0 := by rw [val3]; exact Nat.cast_ne_zero.mpr q.den_ne_zero
  have quot : signed.data 8 / signed.data 3 = (q:K) := by
    rw [val8,val3]
    exact (Rat.cast_def q).symm
  let t := signed.putData 3 (q:K)
  have ht : t.AllData P := eg.safe_end.putData _ hPq
  have et : Eval (Memory.AllData P) (.op (.div 3 8 3)) signed 1 t := by
    simpa only [t,quot] using Eval.op_div signed 3 8 3 hden eg.safe_end (by rw [quot]; exact ht)
  have hlen : (encodeRat q).length = (encodeNat N).length+(encodeNat D).length+1 := by
    simp [encodeRat,N,D]
  refine ⟨t,1+(1+(kn+(1+(kd+(1+(kg+1)))))),by omega,
    ea.seq (eb.seq (en.seq (ef.seq (ed.seq (ez.seq (eg.seq et)))))),by simp [t],?_,?_,?_⟩
  · change ud.index 3=_
    rw [dcur,hlen]
    omega
  · intro j hj
    have j3 : j≠3 := by omega
    have j4 : j≠4 := by omega
    have j7 : j≠7 := by omega
    have j8 : j≠8 := by omega
    calc
      t.data j = ud.data j := by simp [t,signed,z,j3,j4,j8]
      _ = f.data j := ddat _ (by omega)
      _ = un.data j := by simp [f,j8]
      _ = b.data j := ndat _ (by omega)
      _ = s.data j := by simp [b,a,j7]
  · intro j hj
    have j3 : j≠3 := by omega
    exact (didx j hj).trans ((nidx j hj).trans (by simp [b,a,j3]))

/-- The input length bounds both natural Horner accumulators, the signed numerator
and the reduced quotient. -/
theorem ratBlock_bit_conditions (q : ℚ) :
    (∀ v : ℕ, v ≤ 2^(max q.num.natAbs.bits.length q.den.bits.length) →
      RAM.ratBits (v:ℚ) ≤ 3+(encodeRat q).length) ∧
    RAM.ratBits (q.num:ℚ) ≤ 3+(encodeRat q).length ∧
    RAM.ratBits q ≤ 3+(encodeRat q).length := by
  have hw := field_width q
  constructor
  · intro v hv
    have h := Compression.ratBits_signed_integer_of_le_pow (v:ℤ)
      (max q.num.natAbs.bits.length q.den.bits.length) (by simpa using hv)
    have h' : RAM.ratBits (v:ℚ) ≤ max q.num.natAbs.bits.length q.den.bits.length+3 := by
      simpa using h
    omega
  constructor
  · have h := Compression.ratBits_signed_integer_of_le_pow q.num q.num.natAbs.bits.length
      (by have hv := value_lt q.num.natAbs.bits; rw [value_bits] at hv; exact hv.le)
    omega
  · simpa [Nat.add_comm] using ratBits_field q

/-- An actual arithmetic-RAM decoding run whose step count and new register width are
both linear in the length of the wire representation. -/
theorem ratBlock_rational (q : ℚ) (s : Memory ℚ) (c B : ℕ) (hc : s.index 3=c)
    (hbase : 9 ≤ c) (hw : WordAt s c (encodeRat q))
    (hm : s.AllData (fun v => RAM.ratBits v ≤ B)) :
    ∃ t k, k ≤ 24*(encodeRat q).length+40 ∧
      Eval (Memory.AllData (fun v => RAM.ratBits v ≤ max B (3+(encodeRat q).length))) ratBlock s k t ∧
      t.data 3=q ∧ t.index 3=c+(encodeRat q).length ∧
      (∀ j, j<3 ∨ 8<j → t.data j=s.data j) ∧
      ∀ j, j<3 ∨ 6<j → t.index j=s.index j := by
  obtain ⟨hn,hs,hq⟩ := ratBlock_bit_conditions q
  have hB := Nat.le_max_left B (3+(encodeRat q).length)
  have hW := Nat.le_max_right B (3+(encodeRat q).length)
  exact ratBlock_spec _ q s c hc hbase hw (fun k => (hm k).trans hB)
    (fun v hv => (hn v hv).trans hW) (hs.trans hW) (hq.trans hW)

end NativePrice
end LinearProgramming
end Optimization
end OAI
