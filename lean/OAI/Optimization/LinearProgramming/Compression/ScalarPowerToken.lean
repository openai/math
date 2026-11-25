import OAI.Optimization.LinearProgramming.Compression.ScalarPowerWidth
import OAI.Optimization.LinearProgramming.Compression.ScalarPowerDigits
import OAI.Optimization.LinearProgramming.Compression.ScalarPowerMarkers

/-! A fixed RAM block taking one signed scalar to the literal, canonical
address-bank representation required by the power-product comparator. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression

open RAM

/-- The output cursor is address register 34. The digit scratch base in
address register 2 is restored, so the next exponent can reuse that page. -/
def scalarExponentTokenBlock : Block :=
  .seq prepareExponentSignBlock (.seq scalarWidthBlock (.seq serializeNaturalBlock
    (.seq (.op (.addrConst 39 0)) (.seq (appendPowerMarker 39)
      (.seq copyPowerDigitsBlock (appendPowerMarker 37))))))

@[simp] theorem exponentTokens_length (x : ℤ) : (exponentTokens x).length = x.natAbs.size+2 := by
  simp [exponentTokens,Nat.size_eq_bits_len]

private theorem exponentToken_digit (x : ℤ) (i : Fin x.natAbs.size) :
    (exponentTokens x)[i.val+1]'(by rw [exponentTokens_length];omega) =
      .bit (x.natAbs.testBit (x.natAbs.size-1-i.val)) := by
  simp only [exponentTokens,List.getElem_cons_succ]
  rw [List.getElem_append_left (by simp [Nat.size_eq_bits_len]),List.getElem_map]
  have h := congrArg (fun (l : List Bool) => l[i.val]?) (reverse_bits_eq_testBit x.natAbs)
  have hi : i.val < x.natAbs.bits.reverse.length := by simp [Nat.size_eq_bits_len]
  rw [List.getElem?_eq_getElem hi,List.getElem?_eq_getElem (by simp)] at h
  simpa using Option.some.inj h

private theorem exponentToken_finish (x : ℤ) :
    (exponentTokens x)[x.natAbs.size+1]'(by rw [exponentTokens_length];omega) =
      .finish (decide (x < 0)) := by
  simp [exponentTokens,Nat.size_eq_bits_len]

private theorem integerDigit_testBit (a j : ℕ) : integerDigit a j = (a.testBit j).toNat := by
  rw [Nat.testBit_eq_decide_div_mod_eq]
  have h : a / 2^j % 2 < 2 := Nat.mod_lt _ (by decide)
  by_cases he : a / 2^j % 2=1
  · simp [integerDigit,he]
  · simp [integerDigit,show a / 2^j % 2 = 0 by omega]

set_option maxHeartbeats 800000 in
/-- Construct the signed integer tape from its scalar value. The width occurs
only in the proof and in the scratch allocation bound. The program discovers
the exact canonical numeral length, handles zero and both signs, and counts
all address operations as well as scalar operations. -/
theorem scalarExponentTokenBlock_spec (m : Memory ℚ) (x : ℤ) (w base out : ℕ)
    {P : ℚ → Prop} (hm : m.AllData P) (hx : m.data 0=(x:ℚ))
    (hb : m.index 2=base) (ho : m.index 34=out) (hbase : 41 < base) (hout : 42 < out)
    (hw : x.natAbs < 2^w) (hP : ∀ v : ℕ, v ≤ 2^(2*w+2) → P (v:ℚ)) :
    ∃ s time, time ≤ w*(16*w+32)+32 ∧ Block.Eval (Memory.AllData P) scalarExponentTokenBlock m time s ∧
      s.index 2=base ∧ s.index 34=out+(exponentTokens x).length ∧
      (∀ i : Fin (exponentTokens x).length, s.index (out+i.val)=((exponentTokens x)[i.val]).code) ∧
      (∀ i, 6 ≤ i → i ≠ 40 → i ≠ 41 → (i < base ∨ base+w ≤ i) → s.data i=m.data i) ∧
      (∀ i, 3 < i → i ≠ 34 → i ≠ 37 → i ≠ 39 → i ≠ 42 → (i < out ∨ out+(exponentTokens x).length ≤ i) →
        s.index i=m.index i) := by
  let a := x.natAbs
  let K := a.size
  let bits (i : Fin K) := a.testBit (K-1-i.val)
  have hKw : K ≤ w := Nat.size_le.mpr hw
  have hwide : (2:ℕ)^w ≤ 2^(2*w+2) := Nat.pow_le_pow_right (by decide) (by omega)
  have hsmall (v : ℕ) (h : v ≤ 2^w) : P (v:ℚ) := hP v (h.trans hwide)
  have h0 : P 0 := by simpa using hsmall 0 (Nat.zero_le _)
  have h1 : P 1 := by simpa using hsmall 1 (Nat.one_le_pow _ _ (by decide))
  obtain ⟨u,k₀,hk₀,e₀,uval,usign,ud,ui⟩ :=
    prepareExponentSignBlock_spec m x hm hx h0 (hsmall _ hw.le)
  obtain ⟨v,e₁,vsize,vd,vi⟩ := scalarWidthBlock_spec u a w e₀.safe_end uval hw hsmall
  have vval : v.data 0=(a:ℚ) := (vd _ (by decide) (by decide)).trans uval
  have vbase : v.index 2=base := (vi _ (by decide)).trans ((ui _ (by decide)).trans hb)
  obtain ⟨k₂,z,e₂,hk₂,zbase,zdigits,zd,zi⟩ :=
    serializeNaturalBlock_spec v a K base e₁.safe_end vval vsize vbase (by omega)
      (Nat.lt_size_self a) (fun n hn => hP _ (hn.trans (Nat.pow_le_pow_right (by decide) (by omega))))
  have z34 : z.index 34=out := (zi _ (by decide) (by decide) (by decide)).trans
    ((vi _ (by decide)).trans ((ui _ (by decide)).trans ho))
  let z₁ := z.putIndex 39 0
  have hz₁ : z₁.AllData P := e₂.safe_end
  have ez₁ := Block.Eval.op_addrConst z 39 0 e₂.safe_end hz₁
  obtain ⟨t,e₃,tout,tbegin,ti,td⟩ := appendPowerMarker_spec z₁ 39 hz₁ (by simp [z₁,z34];omega)
  have z₁out : z₁.index 34=out := by simp [z₁,z34]
  have tsz : t.index 0=K := by
    rw [ti _ (by decide) (by rw [z₁out];omega)]
    simpa [z₁] using (zi 0 (by decide) (by decide) (by decide)).trans vsize
  have tb : t.index 2=base+K := by
    rw [ti _ (by decide) (by rw [z₁out];omega)]; simpa [z₁] using zbase
  have digit (i : Fin K) : t.data (base+(K-1-i.val)) = ((bits i).toNat : ℚ) := by
    rw [td]
    change z.data _ = _
    rw [zdigits _ (by have := i.isLt;omega),integerDigit_testBit]
  obtain ⟨f,k₄,hk₄,e₄,fbase,fout,fcodes,fd,fi⟩ :=
    copyPowerDigitsBlock_spec bits t base (out+1) e₃.safe_end h1 tsz tb
      (by simpa [z₁out] using tout) hbase (by omega) digit
  have fptr : f.index 34=out+1+K := fout
  have outside (i : ℕ) (h₂ : i ≠ 2) (h34 : i ≠ 34) (h39 : i ≠ 39) (h42 : i ≠ 42)
      (hr : i < out+1 ∨ out+1+K ≤ i) : f.index i = t.index i := fi i h₂ h34 h39 h42 hr
  have fsign : f.index 37=(PowerToken.finish (decide (x < 0))).code := by
    rw [outside 37 (by decide) (by decide) (by decide) (by decide) (by omega),
      ti _ (by decide) (by rw [z₁out];omega)]
    simpa [z₁] using (zi 37 (by decide) (by decide) (by decide)).trans
      ((vi _ (by decide)).trans usign)
  obtain ⟨s,e₅,sout,send,si,sd⟩ := appendPowerMarker_spec f 37 e₄.safe_end (by rw [fptr];omega)
  have slen : (exponentTokens x).length = K+2 := exponentTokens_length x
  have sz : s.index 2=base := (si 2 (by decide) (by rw [fptr];omega)).trans fbase
  have starget : s.index 34=out+(exponentTokens x).length := by rw [sout,fptr,slen];omega
  refine ⟨s,k₀+((4*K+4)+(k₂+(1+(2+(k₄+2))))),?_,e₀.seq (e₁.seq (e₂.seq
    (ez₁.seq (e₃.seq (e₄.seq e₅))))),sz,starget,?_,?_,?_⟩
  · have hmul : K*(16*K+18) ≤ w*(16*w+18) := Nat.mul_le_mul hKw (by omega)
    nlinarith
  · intro i
    have hi : i.val < K+2 := slen ▸ i.isLt
    by_cases hfirst : i.val=0
    · have hc : ((exponentTokens x)[i.val]).code = 0 := by simp [hfirst,exponentTokens,PowerToken.code]
      rw [hc,hfirst,Nat.add_zero,si _ (by omega) (by rw [fptr];omega),
        outside _ (by omega) (by omega) (by omega) (by omega) (by omega)]
      simpa [z₁,z34] using tbegin
    · by_cases hlast : i.val=K+1
      · have hc : (exponentTokens x)[i.val] = .finish (decide (x < 0)) := by
          simpa only [hlast] using exponentToken_finish x
        rw [hc,show out+i.val=f.index 34 by rw [fptr];omega,send,fsign]
      · let j : Fin K := ⟨i.val-1,by omega⟩
        have hij : i.val=j.val+1 := by dsimp [j];omega
        have hc : (exponentTokens x)[i.val]=.bit (bits j) := by
          simpa only [hij] using exponentToken_digit x j
        rw [hc,si _ (by omega) (by rw [fptr];omega),show out+i.val=out+1+j.val by omega]
        exact fcodes j
  · intro i h₆ h40 h41 hr
    rw [sd,fd i h40 h41,td]
    exact (zd i h₆ (by omega)).trans ((vd _ h40 h41).trans (ud _ (by omega) h41))
  · intro i h₃ h34 h37 h39 h42 hr
    have hr' : i < out ∨ out+(K+2) ≤ i := by simpa only [slen] using hr
    rw [si i h34 (by rw [fptr];omega),outside _ (by omega) h34 h39 h42 (by omega),
      ti _ h34 (by rw [z₁out];omega)]
    simpa [z₁,h39] using (zi i (by omega) (by omega) (by omega)).trans
      ((vi _ (by omega)).trans (ui _ h37))

end Compression
end LinearProgramming
end Optimization
end OAI
