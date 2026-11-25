import OAI.Optimization.LinearProgramming.Compression.BinaryDivisionBlock

/-! Composable serialization of constructed integer scalars into ordinary, separately
addressable, least-significant-bit-first RAM cells. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression

open RAM Finset
open scoped BigOperators

def integerDigit (a j : ℕ) := a / 2^j % 2

/-- The first n low-order digits give the residue modulo 2ⁿ. -/
theorem sum_integerDigits (a n : ℕ) :
    (∑ j ∈ range n, integerDigit a j * 2^j) = a % 2^n := by
  induction n with
  | zero => simp [Nat.mod_one]
  | succ n ih => rw [sum_range_succ, ih, Nat.mod_pow_succ]; simp [integerDigit, mul_comm]

private def serializeBitBody : Block := .seq quotientRemainderBlock <| .seq (.op (.store 2 0)) <|
  .seq (.op (.copy 0 3)) (.op (.incr 2 2))

/-- Data register 0 supplies a bounded natural, index 0 supplies its bit width and
index 2 supplies the output address. This block can be called repeatedly. -/
def serializeNaturalBlock : Block :=
  .seq (.op (.const 1 2)) (.forRange 3 0 serializeBitBody)

private structure DigitInv {P : ℚ → Prop} (m : Memory ℚ) (a k base j : ℕ) (s : Memory ℚ) : Prop where
  safe : s.AllData P
  value : s.data 0 = ((a / 2^j : ℕ) : ℚ)
  divisor : s.data 1 = 2
  size : s.index 0 = k
  count : s.index 3 = j
  cursor : s.index 2 = base+j
  savedIndex : ∀ i, i ≠ 1 → i ≠ 2 → i ≠ 3 → s.index i = m.index i
  savedData : ∀ i, 6 ≤ i → (i < base ∨ base+j ≤ i) → s.data i = m.data i
  digits : ∀ h < j, s.data (base+h) = ((integerDigit a h : ℕ) : ℚ)

/-- The exact digits, range of changed memory, step bound and invariant on every scalar
are preserved when the caller embeds the serializer in a larger RAM program. -/
theorem serializeNaturalBlock_spec (m : Memory ℚ) (a k base : ℕ) {P : ℚ → Prop}
    (hm : m.AllData P) (ha : m.data 0 = (a : ℚ)) (hk : m.index 0 = k)
    (hb : m.index 2 = base) (hbase : 6 ≤ base) (haK : a < 2^k)
    (hP : ∀ v : ℕ, v ≤ 2^(2*k+2) → P (v : ℚ)) :
    ∃ (steps : ℕ) (z : Memory ℚ), Block.Eval (Memory.AllData P) serializeNaturalBlock m steps z ∧
      steps ≤ k*(16*k+18)+3 ∧ z.index 2=base+k ∧
      (∀ j < k, z.data (base+j) = ((integerDigit a j : ℕ) : ℚ)) ∧
      (∀ i, 6 ≤ i → (i < base ∨ base+k ≤ i) → z.data i=m.data i) ∧
      (∀ i, i ≠ 1 → i ≠ 2 → i ≠ 3 → z.index i=m.index i) := by
  let m1 := m.putData 1 2
  have htwo : P (2 : ℚ) := by
    apply hP 2
    simpa only [pow_one] using Nat.pow_le_pow_right (n := 2) (by decide) (show 1≤2*k+2 by omega)
  have init := Block.Eval.op_const m 1 2 hm (hm.putData 1 htwo)
  have startInv : DigitInv (P := P) m a k base 0 (m1.putIndex 3 0) := by
    refine ⟨init.safe_end, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by simp⟩
    · simpa [m1] using ha
    · simp [m1]
    · simp [m1,hk]
    · simp
    · simp [m1,hb]
    · intro i _ _ hi; simp [m1,hi]
    · intro i hi _; simp [m1,show i ≠ 1 by omega]
  have advance (j : ℕ) (hj : j < k) (s : Memory ℚ) (hs : DigitInv (P := P) m a k base j s) :
      ∃ t n, n ≤ 16*k+15 ∧ Block.Eval (Memory.AllData P) serializeBitBody s n t ∧
        DigitInv (P := P) m a k base (j+1) (t.putIndex 3 (t.index 3+1)) := by
    have ha' : a/2^j < 2^k := (Nat.div_le_self ..).trans_lt haK
    have hpow : 2 ≤ 2^k := by
      simpa only [pow_one] using Nat.pow_le_pow_right (n := 2) (by decide) (show 1≤k by omega)
    obtain ⟨n,z,he,hn,hr,hd,hq,hmem,hidx⟩ := quotientRemainderBlock_spec s (a/2^j) 2 k
      hs.safe hs.value hs.divisor hs.size ha' (by decide) hpow hP
    have cur : z.index 2=base+j := (hidx 2 (by decide)).trans hs.cursor
    have count : z.index 3=j := (hidx 3 (by decide)).trans hs.count
    let v := z.putData (z.index 2) (z.data 0)
    let w := v.putData 0 (v.data 3)
    let t := w.putIndex 2 (w.index 2+1)
    have store := Block.Eval.op_store z 2 0 he.safe_end (he.safe_end.putData (z.index 2) (he.safe_end 0))
    have copy := Block.Eval.op_copy v 0 3 store.safe_end (store.safe_end.putData 0 (store.safe_end 3))
    have inc := Block.Eval.op_incr w 2 2 copy.safe_end (copy.safe_end.putIndex _ _)
    refine ⟨t, _, by omega, he.seq (store.seq (copy.seq inc)), ?_⟩
    have hW : 6 ≤ z.index 2 := by omega
    have hr' : z.data 0 = ((integerDigit a j : ℕ) : ℚ) := hr
    have hq' : z.data 3 = ((a/2^(j+1) : ℕ) : ℚ) := by
      simpa [Nat.div_div_eq_div_mul, pow_succ] using hq
    refine ⟨inc.safe_end, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa [t,w,v,show 3 ≠ z.index 2 by omega] using hq'
    · simpa [t,w,v,show 1 ≠ z.index 2 by omega] using hd
    · simpa [t,w,v] using (hidx 0 (by decide)).trans hs.size
    · simp [t,w,v,count]
    · simp [t,w,v,cur,Nat.add_assoc]
    · intro i hi1 hi2 hi3
      simpa [t,w,v,hi2,hi3] using (hidx i hi1).trans (hs.savedIndex i hi1 hi2 hi3)
    · intro i hi hout
      have hne : i ≠ z.index 2 := by omega
      have hprev : i < base ∨ base+j ≤ i := by omega
      simpa [t,w,v,hne,show i≠0 by omega] using (hmem i hi).trans (hs.savedData i hi hprev)
    · intro h hlt
      by_cases hh : h=j
      · subst h
        change ((z.putData (z.index 2) (z.data 0)).putData 0 _).data (base+j) = _
        rw [Memory.putData_ne _ (show base+j ≠ 0 by omega) _, ← cur, Memory.putData_same]
        exact hr'
      · have hprev : h<j := by omega
        have hne : base+h ≠ z.index 2 := by omega
        change ((z.putData (z.index 2) (z.data 0)).putData 0 _).data (base+h) = _
        rw [Memory.putData_ne _ (show base+h ≠ 0 by omega) _, Memory.putData_ne _ hne _]
        exact (hmem (base+h) (by omega)).trans (hs.digits h hprev)
  obtain ⟨z,n,hn,he,hs⟩ := Block.Eval.forRange_invariant 3 0 k (16*k+15)
    (DigitInv (P := P) m a k base) m1 init.safe_end startInv
    (fun _ _ h => ⟨h.safe,h.count,h.size⟩) advance
  rw [show k*(16*k+15+3) = k*(16*k+18) by ring] at hn
  exact ⟨_,z,init.seq he,by omega,hs.cursor,hs.digits,hs.savedData,hs.savedIndex⟩

end Compression
end LinearProgramming
end Optimization
end OAI
