import OAI.Optimization.LinearProgramming.Compression.BinarySerialization
import OAI.Optimization.LinearProgramming.Compression.BinaryReducedScalars

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression

open RAM

private def signAndMagnitude : Block :=
  .branch (.scalarLT 0 8) (.seq (.op (.const 7 1)) (.op (.sub 0 8 0))) (.op (.const 7 0))

private theorem signAndMagnitude_spec (m : Memory ℚ) (v : ℤ) {P : ℚ → Prop}
    (hs : m.AllData P) (hv : m.data 0 = (v : ℚ)) (hz : m.data 8 = 0)
    (hmag : P (v.natAbs : ℚ)) (h1 : P 1) (h0 : P 0) :
    ∃ steps z, Block.Eval (Memory.AllData P) signAndMagnitude m steps z ∧ steps ≤ 4 ∧
      z.data 0=(v.natAbs:ℚ) ∧ z.data 7 = (if v < 0 then 1 else 0) ∧
      z.data 6=m.data 6 ∧ z.data 9=m.data 9 ∧ z.index=m.index := by
  have eqabs : (v.natAbs : ℚ) = |(v:ℚ)| := by
    rw [← Int.cast_abs, ← Int.natCast_natAbs, Int.cast_natCast]
  by_cases h : v < 0
  · have hq : (v:ℚ)<0 := by exact_mod_cast h
    have test : Cond.test (.scalarLT 0 8) m = true := by simpa [Cond.test,hv,hz] using hq
    let u := m.putData 7 1
    let z := u.putData 0 (u.data 8-u.data 0)
    have heq : u.data 8-u.data 0=(v.natAbs:ℚ) := by simp [u,hz,hv,eqabs,abs_of_neg hq]
    have setSign := Block.Eval.op_const m 7 1 hs (hs.putData 7 h1)
    have sub := Block.Eval.op_sub u 0 8 0 setSign.safe_end (setSign.safe_end.putData _ (heq ▸ hmag))
    refine ⟨4,z,.branchTrue test (setSign.seq sub),by decide,?_,?_,?_,?_,rfl⟩
    · simpa [z] using heq
    · simp [z,u,h]
    · simp [z,u]
    · simp [z,u]
  · have hq : (0:ℚ)≤v := by exact_mod_cast le_of_not_gt h
    have test : Cond.test (.scalarLT 0 8) m = false := by simpa [Cond.test,hv,hz] using not_lt_of_ge hq
    let z := m.putData 7 0
    refine ⟨2,z,.branchFalse test (Block.Eval.op_const m 7 0 hs (hs.putData _ h0)),by decide,?_,?_,?_,?_,rfl⟩
    · simp [z,hv,eqabs,abs_of_nonneg hq]
    · simp [z,h]
    · simp [z]
    · simp [z]

/-- Normalize a signed integer pair, then write the sign, the k least-significant-first
bits of the canonical numerator magnitude, and the k bits of the canonical denominator. -/
def canonicalRationalBitsBlock : Block :=
  .seq reducedScalarPairBlock <| .seq (.op (.div 6 0 1)) <| .seq (.op (.copy 9 1)) <| .seq (.op (.const 8 0)) <|
  .seq signAndMagnitude <| .seq (.op (.addrConst 2 10)) <| .seq serializeNaturalBlock <|
  .seq (.op (.copy 0 9)) serializeNaturalBlock

/-- The rational value is returned in scalar cell 6, with its canonical sign in cell 7 (negative sign), cells 10 through 10+k−1
(numerator), and the next k cells (denominator). Padding consists of high zero digits.
No bit of an input scalar is a machine operation. -/
theorem canonicalRationalBitsBlock_spec (m : Memory ℚ) (p : ℤ) (q k : ℕ) {P : ℚ → Prop}
    (hm : m.AllData P) (hp : m.data 0 = (p:ℚ)) (hqv : m.data 1 = (q:ℚ)) (hk : m.index 0=k)
    (hq : 0 < q) (hpK : p.natAbs < 2^k) (hqK : q < 2^k)
    (hP : ∀ v : ℤ, v.natAbs ≤ 2^(2*k+2) → P (v:ℚ)) (hF : P ((p:ℚ)/(q:ℚ))) :
    let v := (p:ℚ)/(q:ℚ)
    ∃ steps z, Block.Eval (Memory.AllData P) canonicalRationalBitsBlock m steps z ∧
      steps ≤ 2*k*(16*k+17) + 2*k*(16*k+18) + 28 ∧
      z.index 0 = k ∧ z.data 6 = v ∧ z.data 7 = (if v.num < 0 then 1 else 0) ∧
      (∀ i < k, z.data (10+i) = ((integerDigit v.num.natAbs i : ℕ) : ℚ)) ∧
      (∀ i < k, z.data (10+k+i) = ((integerDigit v.den i : ℕ) : ℚ)) := by
  dsimp only
  let v := (p:ℚ)/(q:ℚ)
  have hheight := reduced_fraction_height p (q:ℤ) (by exact_mod_cast hq.ne')
  have hmagK : v.num.natAbs < 2^k := (by simpa [v] using hheight.1 : v.num.natAbs ≤ p.natAbs).trans_lt hpK
  have hdenK : v.den < 2^k := (by simpa [v] using hheight.2 : v.den ≤ q).trans_lt hqK
  have hPN (x : ℕ) (hx : x ≤ 2^(2*k+2)) : P (x:ℚ) := by
    simpa only [Int.cast_natCast] using hP (x:ℤ) (by simpa using hx)
  have h0 : P (0:ℚ) := by simpa using hPN 0 (Nat.zero_le _)
  have h1 : P (1:ℚ) := by simpa using hPN 1 Nat.one_le_two_pow
  have hMag : P (v.num.natAbs:ℚ) := hPN _ (hmagK.le.trans (Nat.pow_le_pow_right (by decide) (by omega)))
  obtain ⟨n,z,hn,hcost,hnum,hden,_,hidx⟩ := reducedScalarPairBlock_spec m p q k hm hp hqv hk hq hpK hqK hP
  have zDen : z.data 1 ≠ 0 := by
    rw [hden]; exact_mod_cast Rat.den_nz _
  have zVal : z.data 0 / z.data 1 = v := by
    rw [hnum,hden]; exact Rat.num_div_den v
  let f := z.putData 6 (z.data 0/z.data 1)
  have scalar := Block.Eval.op_div z 6 0 1 zDen hn.safe_end (hn.safe_end.putData _ (zVal ▸ hF))
  let z1 := f.putData 9 (f.data 1)
  let z2 := z1.putData 8 0
  have save := Block.Eval.op_copy f 9 1 scalar.safe_end (scalar.safe_end.putData _ (scalar.safe_end 1))
  have guard := Block.Eval.op_const z1 8 0 save.safe_end (save.safe_end.putData 8 h0)
  have hnum' : z2.data 0 = (v.num:ℚ) := by simpa [z2,z1,f,v] using hnum
  obtain ⟨g,u,sg,cg,hu0,hus,hu6,hu9,hui⟩ := signAndMagnitude_spec z2 v.num guard.safe_end hnum'
    (by simp [z2]) hMag h1 h0
  let u1 := u.putIndex 2 10
  have ptr := Block.Eval.op_addrConst u 2 10 sg.safe_end (sg.safe_end.putIndex 2 10)
  have uk : u1.index 0=k := by simpa [u1,hui,z2,z1,f] using (hidx 0 (by decide)).trans hk
  obtain ⟨l,w,hw,hl,wptr,wb,wd,wi⟩ := serializeNaturalBlock_spec u1 v.num.natAbs k 10
    ptr.safe_end hu0 uk (by simp [u1]) (by decide) hmagK hPN
  have wd9 : w.data 9=(v.den:ℚ) := by
    rw [wd 9 (by decide) (Or.inl (by decide))]
    change u.data 9 = _
    rw [hu9]
    simpa [z2,z1,f,v] using hden
  let w1 := w.putData 0 (w.data 9)
  have cp := Block.Eval.op_copy w 0 9 hw.safe_end (hw.safe_end.putData _ (hw.safe_end 9))
  have wk : w1.index 0 = k := (wi 0 (by decide) (by decide) (by decide)).trans uk
  obtain ⟨j,last,lastEval,hj,_,hdigits,hkeep,lastIndex⟩ := serializeNaturalBlock_spec w1 v.den k (10+k)
    cp.safe_end (by simpa [w1] using wd9) wk wptr (by omega) hdenK hPN
  refine ⟨_,last,hn.seq (scalar.seq (save.seq (guard.seq (sg.seq (ptr.seq (hw.seq (cp.seq lastEval))))))),?_,(lastIndex 0 (by decide) (by decide) (by decide)).trans wk,?_,?_,?_,hdigits⟩
  · rw [show 2*k*(16*k+18) = 2*(k*(16*k+18)) by ring]
    omega
  · rw [hkeep 6 (by decide) (Or.inl (by omega))]
    have h := wd 6 (by decide) (Or.inl (by decide))
    simpa [w1,h,u1,hu6,z2,z1,f] using zVal
  · rw [hkeep 7 (by decide) (Or.inl (by omega))]
    have h := wd 7 (by decide) (Or.inl (by decide))
    simpa [w1,h,u1] using hus
  · intro i hi
    rw [hkeep (10+i) (by omega) (Or.inl (by omega))]
    simpa [w1,show 10+i≠0 by omega] using wb i hi

/-- Integer-valued scalar registers carry a sign and the ordinary length of their magnitude. -/
theorem ratBits_signed_integer_of_le_pow (v : ℤ) (width : ℕ) (hv : v.natAbs ≤ 2^width) :
    ratBits (v : ℚ) ≤ width+3 := by
  have hlog : v.natAbs.log2 ≤ width := by
    by_cases hz : v.natAbs=0
    · simp [hz]
    · exact Nat.le_of_lt_succ ((Nat.log2_lt hz).mpr (hv.trans_lt
        (Nat.pow_lt_pow_right (by decide) (Nat.lt_succ_self _))))
  simp only [ratBits,Rat.num_intCast,Rat.den_intCast,show (1:ℕ).log2=0 from rfl,Nat.add_zero]
  omega

theorem ratBits_bounded_fraction (p : ℤ) (q k : ℕ) (hq : 0 < q)
    (hpK : p.natAbs < 2^k) (hqK : q < 2^k) : ratBits ((p : ℚ)/(q : ℚ)) ≤ 2*k+5 := by
  let r := (p : ℚ)/(q : ℚ)
  have height : r.num.natAbs ≤ p.natAbs ∧ r.den ≤ q := by
    simpa only [r,Int.cast_natCast,Int.natAbs_natCast] using
      reduced_fraction_height p (q : ℤ) (by exact_mod_cast hq.ne')
  have logBound (x : ℕ) (hx : x < 2^k) : x.log2 ≤ k := by
    by_cases hz : x=0
    · simp [hz]
    · exact (Nat.log2_lt hz).mpr hx |>.le
  have hN := logBound r.num.natAbs (height.1.trans_lt hpK)
  have hD := logBound r.den (height.2.trans_lt hqK)
  change 3+r.num.natAbs.log2+r.den.log2 ≤ 2*k+5
  omega

/-- Standalone uniform serializer from raw signed numerator, positive denominator and a
known width. Its register bound also applies during gcd, multiplication, subtraction,
canonicalization and every output write. -/
def canonicalRationalBitsProgram : Program := canonicalRationalBitsBlock.compile 0 ++ [.halt 0]

theorem canonicalRationalBitsProgram_trace (p : ℤ) (q k : ℕ) (hq : 0<q)
    (hpK : p.natAbs<2^k) (hqK : q<2^k) :
    let v := (p:ℚ)/(q:ℚ)
    ∃ (steps : ℕ) (t : Fin (steps+1) → State ℚ),
      steps ≤ 2*k*(16*k+17) + 2*k*(16*k+18) + 29 ∧
      Trace canonicalRationalBitsProgram (start [k] [(p:ℚ),(q:ℚ)]) steps t ∧
      (t (Fin.last _)).output = some 0 ∧
      (t (Fin.last _)).data 6 = v ∧ (t (Fin.last _)).data 7 = (if v.num<0 then 1 else 0) ∧
      (∀ i<k, (t (Fin.last _)).data (10+i) = ((integerDigit v.num.natAbs i : ℕ) : ℚ)) ∧
      (∀ i<k, (t (Fin.last _)).data (10+k+i) = ((integerDigit v.den i : ℕ) : ℚ)) ∧
      ∀ i, scalarBound (2*k+5) (t i) := by
  dsimp only
  let m := (start [k] [(p:ℚ),(q:ℚ)]).memory
  let P := fun x : ℚ => ratBits x ≤ 2*k+5
  have hP (v : ℤ) (hv : v.natAbs ≤ 2^(2*k+2)) : P (v:ℚ) := by
    exact ratBits_signed_integer_of_le_pow v (2*k+2) hv
  have hcap : 2^k ≤ 2^(2*k+2) := Nat.pow_le_pow_right (by decide) (by omega)
  have hm : m.AllData P := by
    intro i
    match i with
    | 0 => exact hP p (hpK.le.trans hcap)
    | 1 =>
      change P (q : ℚ)
      simpa only [Int.cast_natCast] using hP (q:ℤ) (by simpa only [Int.natAbs_natCast] using hqK.le.trans hcap)
    | _+2 =>
      change P 0
      simpa only [Int.cast_zero] using hP 0 (by simp)
  obtain ⟨n,z,he,hn,_,hV,hs,hN,hD⟩ := canonicalRationalBitsBlock_spec m p q k hm rfl rfl rfl hq hpK hqK hP (ratBits_bounded_fraction p q k hq hpK hqK)
  obtain ⟨t,ht,hhalt,hmem,hsafe⟩ := he.halted_trace (tag := 0)
  have atEnd (j : ℕ) : (t (Fin.last _)).data j=z.data j :=
    congrArg (fun s : Memory ℚ => s.data j) hmem
  exact ⟨n+1,t,by omega,ht,hhalt,(atEnd 6).trans hV,(atEnd 7).trans hs,
    fun i hi => (atEnd _).trans (hN i hi), fun i hi => (atEnd _).trans (hD i hi), hsafe⟩

end Compression
end LinearProgramming
end Optimization
end OAI
