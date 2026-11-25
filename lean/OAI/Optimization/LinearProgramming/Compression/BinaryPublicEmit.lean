import OAI.Optimization.LinearProgramming.Compression.BinaryPublicDenominator
import OAI.Optimization.LinearProgramming.Compression.BinaryCanonical

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression

open RAM OracleSpec.MinorLog

private def putPublicSign : Block := .branch (.scalarLT 7 6) (.op (.addrConst 2 0))
  (.seq (.op (.addrConst 2 1)) (.op (.addrCopy 2 2)))

private theorem putPublicSign_spec (m : Memory ℚ) (v : ℤ) {P : ℚ → Prop}
    (safe : m.AllData P) (sign : m.data 7 = if v < 0 then 1 else 0) (one : m.data 6 = 1) :
    ∃ t, Block.Eval (Memory.AllData P) putPublicSign m 3 t ∧ t.index 2 = (decide (v < 0)).toNat ∧
      t.data=m.data ∧ ∀ i, i ≠ 2 → t.index i=m.index i := by
  by_cases h : v < 0
  · let z := m.putIndex 2 1
    have e := Block.Eval.op_addrConst m 2 1 safe (safe.putIndex 2 1)
    have f := Block.Eval.op_addrCopy z 2 2 e.safe_end (e.safe_end.putIndex 2 (z.index 2))
    refine ⟨_,Block.Eval.branchFalse (by simp [Cond.test,sign,one,h]) (e.seq f),?_,rfl,?_⟩
    · simp [z,h]
    · intro i hi; simp [z,hi]
  · have e := Block.Eval.op_addrConst m 2 0 safe (safe.putIndex 2 0)
    refine ⟨_,Block.Eval.branchTrue (by simp [Cond.test,sign,one,h]) e,by simp [h],rfl,?_⟩
    intro i hi; simp [hi]

private def completePublicHeader : Block := .seq (headerToAddress 1 0) <| .seq (headerToAddress 2 1) <|
  .seq (.op (.const 6 1)) (.seq putPublicSign (.op (.copy 0 9)))

private theorem completePublicHeader_spec (m : Memory ℚ) (q : ℚ) (k : ℕ) {P : ℚ → Prop}
    (safe : m.AllData P) (words : WordsPublished m q)
    (wn : width q.num.natAbs ≤ k) (wd : width q.den ≤ k)
    (small : ∀ z : ℕ, z ≤ k+10 → P (z:ℚ)) :
    ∃ s t, Block.Eval (Memory.AllData P) completePublicHeader m s t ∧ s ≤ 8*k+13 ∧
      explicitValue (t.atPC 0) q := by
  have h1 : P (1:ℚ) := by simpa using small 1 (by omega)
  obtain ⟨a,ea,an,ai,ad⟩ := headerToAddress_spec P m 1 0 (width q.num.natAbs) (by decide) (by decide)
    words.numeratorWidth safe h1 (fun _ hj => small _ (by omega))
  obtain ⟨b,eb,bd,bi,bdata⟩ := headerToAddress_spec P a 2 1 (width q.den) (by decide) (by decide)
    ((ad 2 (by decide) (by decide)).trans words.denominatorWidth) ea.safe_end h1 (fun _ hj => small _ (by omega))
  have scalarInvariant : (fun s : Memory ℚ => ∀ i, P (s.data i)) = Memory.AllData P := by
    funext s
    rfl
  rw [scalarInvariant] at ea eb
  let c := b.putData 6 1
  have bs : b.AllData P := eb.safe_end
  have ec := Block.Eval.op_const (safe := Memory.AllData P) b 6 1 bs (bs.putData 6 h1)
  have hsign : c.data 7 = (if q.num < 0 then 1 else 0) :=
    (bdata 7 (by decide) (by decide)).trans ((ad 7 (by decide) (by decide)).trans words.sign)
  obtain ⟨d,ed,bit,dd,di⟩ := putPublicSign_spec c q.num ec.safe_end hsign (by simp [c])
  let z := d.putData 0 (d.data 9)
  have ez := Block.Eval.op_copy (safe := Memory.AllData P) d 0 9 ed.safe_end (ed.safe_end.putData _ (ed.safe_end 9))
  have dq : d.data 9 = q := by rw [dd]; exact (bdata 9 (by decide) (by decide)).trans ((ad 9 (by decide) (by decide)).trans words.value)
  have unaffected (i : ℕ) (hi : 3 ≤ i) : z.index i = m.index i :=
    (di i (by omega)).trans ((bi i (by omega)).trans (ai i (by omega)))
  refine ⟨_,z,ea.seq (eb.seq (ec.seq (ed.seq ez))),by omega,?_,?_,?_,bit,?_,?_⟩
  · change (d.putData 0 (d.data 9)).data 0 = q
    exact (Memory.putData_same d 0 (d.data 9)).trans dq
  · exact (di 0 (by decide)).trans ((bi 0 (by decide)).trans an)
  · exact (di 1 (by decide)).trans bd
  · intro j hj; exact (unaffected _ (by omega)).trans ((words.numerator j hj).trans (integerDigit_testBit _ _))
  · intro j hj; exact (unaffected _ (by omega)).trans ((words.denominator j hj).trans (integerDigit_testBit _ _))

/-- Translate the padded scalar reply into the exact sealed service reply in physical
address registers: both canonical lengths, the sign, and the two unpadded bit words. -/
def publicReplyBlock : Block :=
  .seq sizePublicWords (.seq publishNumerator (.seq publishDenominator completePublicHeader))

theorem publicReplyBlock_spec (m : Memory ℚ) (q : ℚ) (k : ℕ) {P : ℚ → Prop}
    (safe : m.AllData P) (hk : m.index 0=k) (bounded : q.num.natAbs < 2^k ∧ q.den < 2^k)
    (buffer : PaddedReply m q k) (small : ∀ z : ℕ, z ≤ k+10 → P (z:ℚ)) :
    ∃ s t, Block.Eval (Memory.AllData P) publicReplyBlock m s t ∧ s ≤ 48*k+82 ∧
      explicitValue (t.atPC 0) q := by
  have kp : 0 < k := by
    by_cases h : k=0
    · have impossible := bounded.2
      rw [h,pow_zero] at impossible
      exact ((Nat.not_lt_of_ge q.pos) impossible).elim
    · exact Nat.pos_of_ne_zero h
  have wn := width_of_lt_pow bounded.1 kp
  have wd := width_of_lt_pow bounded.2 kp
  obtain ⟨a,ea,sized⟩ := sizePublicWords_spec m q k safe hk bounded buffer (fun z h => small z (by omega))
  obtain ⟨sn,b,eb,cb,num⟩ := publishNumerator_spec a q k ea.safe_end sized wn small
  obtain ⟨sd,c,ec,cc,both⟩ := publishDenominator_spec b q k eb.safe_end num wd small
  obtain ⟨sf,t,ef,cf,out⟩ := completePublicHeader_spec c q k ec.safe_end both wn wd small
  exact ⟨_,t,ea.seq (eb.seq (ec.seq ef)),by omega,out⟩

theorem smallPublicationBits (k z : ℕ) (hz : z ≤ k+10) : ratBits (z:ℚ) ≤ 2*k+7 := by
  have grow : k+1 ≤ 2^k := Nat.lt_two_pow_self
  have pow : z ≤ 2^(k+4) := by
    rw [pow_add,show (2:ℕ)^4=16 from rfl]
    exact (show z ≤ (k+1)*16 by omega).trans (Nat.mul_le_mul_right 16 grow)
  have h := ratBits_signed_integer_of_le_pow (z:ℤ) (k+4) (by simpa using pow)
  simpa only [Int.cast_natCast] using h.trans (show k+4+3 ≤ 2*k+7 by omega)

theorem explicitValue_of_memory {t : State ℚ} {m : Memory ℚ} {q : ℚ}
    (hm : t.memory = m) (h : explicitValue (m.atPC 0) q) : explicitValue t q := by
  obtain ⟨v,n,d,s,b,c⟩ := h
  have rd (i : ℕ) : t.data i = m.data i := congrArg (fun z : Memory ℚ => z.data i) hm
  have ri (i : ℕ) : t.index i = m.index i := congrArg (fun z : Memory ℚ => z.index i) hm
  exact ⟨(rd 0).trans v,(ri 0).trans n,(ri 1).trans d,(ri 2).trans s,
    fun j hj => (ri _).trans (b j hj),fun j hj => (ri _).trans (c j hj)⟩

end Compression
end LinearProgramming
end Optimization
end OAI
