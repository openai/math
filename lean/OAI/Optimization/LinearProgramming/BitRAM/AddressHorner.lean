import OAI.Optimization.LinearProgramming.RAM.RAMArithmetic
import OAI.Optimization.LinearProgramming.RAM.RAMFrame
import OAI.Optimization.LinearProgramming.Compression.ParameterPolynomialRAM
import OAI.Optimization.LinearProgramming.Compression.BitBudget

/-! Fixed natural-coefficient polynomials evaluated entirely in the address bank. This
produces the bit exponent used by PCG without writing an exponential address or scalar. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace BitRAM
namespace AddressHorner

open OAI.Optimization.LinearProgramming.RAM RAM.Block RAM.Tape OAI.Optimization.LinearProgramming.Compression Polynomial

/-- The input dimension is in 7; accumulator and arithmetic scratch occupy 8--12. -/
def stages : List Nat → Block
  | [] => .op (.addrConst 8 0)
  | c::cs => .seq (stages cs) (.seq (.op (.addrCopy 9 7)) (.seq (multiply 8)
      (.seq (.op (.addrConst 9 c)) (addSub true 8))))

/-- The list is fixed by program text. The runtime argument is read from `source`
before any of the low registers are used for arithmetic. -/
def coefficientBlock (source : Nat) (cs : List Nat) : Block := .seq (.op (.addrCopy 7 source)) (stages cs)

noncomputable def block (source : Nat) (p : Polynomial Nat) : Block := coefficientBlock source (parameterCoefficients p)

private noncomputable def valuePolynomial : List Nat → Polynomial Nat
  | [] => 0
  | c::cs => valuePolynomial cs*X+C c

private theorem valuePolynomial_eval (cs : List Nat) (n : Nat) :
    (valuePolynomial cs).eval n = parameterCoefficientValue cs n := by
  induction cs with
  | nil => simp [valuePolynomial,parameterCoefficientValue]
  | cons c cs ih => simp only [valuePolynomial,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_X,
      Polynomial.eval_C,ih,parameterCoefficientValue,List.foldr_cons]

noncomputable def stageTime : List Nat → Polynomial Nat
  | [] => 1
  | c::cs => stageTime cs+8+(5+4*valuePolynomial cs)*X+4*C c

noncomputable def timePolynomial (p : Polynomial Nat) : Polynomial Nat := 1+stageTime (parameterCoefficients p)

private theorem stages_low (cs : List Nat) : (stages cs).indexWritesBelow 13=true := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    change ((stages cs).indexWritesBelow 13 && true) = true
    exact Bool.and_eq_true_iff.mpr ⟨ih,rfl⟩

theorem block_writes_below (source : Nat) (p : Polynomial Nat) : (block source p).indexWritesBelow 13=true := by
  change (true && (stages (parameterCoefficients p)).indexWritesBelow 13) = true
  exact Bool.and_eq_true_iff.mpr ⟨rfl,stages_low ..⟩

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

private theorem stages_eval (cs : List Nat) (n : Nat) (m : Memory K) {P : K → Prop} (hm : Good P m)
    (hn : m.index 7=n) :
    ∃ k t, Eval (Good P) (stages cs) m k t ∧ k ≤ (stageTime cs).eval n ∧
      t.index 8=parameterCoefficientValue cs n ∧ t.data=m.data ∧ ∀ i<8,t.index i=m.index i := by
  induction cs generalizing m with
  | nil =>
    refine ⟨1,_,eval_constI m hm 8 0,?_,?_,rfl,?_⟩
    · simp [stageTime]
    · simp [parameterCoefficientValue]
    · intro i hi; simp [show i ≠ 8 by omega]
  | cons c cs ih =>
    obtain ⟨j,a,previous,hj,value,ad,alow⟩ := ih m hm hn
    let x := a.putIndex 9 (a.index 7)
    have copy : Eval (Good P) (.op (.addrCopy 9 7)) a 1 x := eval_copyI a previous.safe_end 9 7
    obtain ⟨km,b,prod,hkm,bd,blow,bval⟩ := multiply_correct 8 x copy.safe_end
    let y := b.putIndex 9 c
    have constant : Eval (Good P) (.op (.addrConst 9 c)) b 1 y := eval_constI b prod.safe_end 9 c
    obtain ⟨ka,t,finish,hka,td,tlow,tval⟩ := addSub_correct true 8 y constant.safe_end
    have x8 : x.index 8=parameterCoefficientValue cs n := by simpa [x] using value
    have x9 : x.index 9=n := by simp [x,alow 7 (by decide),hn]
    have y8 : y.index 8=parameterCoefficientValue cs n*n := by
      simpa only [y,Memory.putIndex_ne _ (by decide : 8 ≠ 9),x8,x9] using bval
    have y9 : y.index 9=c := by simp [y]
    refine ⟨j+(1+(km+(1+ka))),t,previous.seq (copy.seq (prod.seq (constant.seq finish))),?_,?_,td.trans (bd.trans ad),?_⟩
    · change km ≤ 4+(5+4*x.index 8)*x.index 9 at hkm
      change ka ≤ 2+4*y.index 9 at hka
      rw [x8,x9] at hkm
      rw [y9] at hka
      simp only [stageTime,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_X,Polynomial.eval_C,
        Polynomial.eval_ofNat,valuePolynomial_eval]
      omega
    · change t.index 8 = parameterCoefficientValue cs n*n+c
      exact tval.trans (by simp [y8,y9])
    · intro i hi
      have ne : i ≠ 9 := by omega
      exact (tlow i hi).trans ((Memory.putIndex_ne b ne c).trans ((blow i hi).trans
        ((Memory.putIndex_ne a ne (a.index 7)).trans (alow i hi))))

/-- Polynomial instruction count, exact address accumulator, unchanged scalar data, and
preservation of both the low caller registers and every register above the fixed scratch. -/
theorem block_eval_frame (source : Nat) (p : Polynomial Nat) (n : Nat) (m : Memory K) {P : K → Prop}
    (hm : Good P m) (hn : m.index source=n) :
    ∃ k t, Eval (Good P) (block source p) m k t ∧ k ≤ (timePolynomial p).eval n ∧
      t.index 8=p.eval n ∧ t.data=m.data ∧ ∀ i, i<7 ∨ 13 ≤ i → t.index i=m.index i := by
  let a := m.putIndex 7 (m.index source)
  have copy : Eval (Good P) (.op (.addrCopy 7 source)) m 1 a := eval_copyI m hm 7 source
  obtain ⟨k,t,body,bound,answer,data,low⟩ := stages_eval (parameterCoefficients p) n a copy.safe_end (by simpa [a] using hn)
  have run : Eval (Good P) (block source p) m (1+k) t := copy.seq body
  refine ⟨1+k,t,run,?_,answer.trans (parameterCoefficientValue_canonical p n),data,?_⟩
  · simpa only [timePolynomial,Polynomial.eval_add,Polynomial.eval_one] using Nat.add_le_add_left bound 1
  · intro i hi
    rcases hi with before|after
    · exact (low i (by omega)).trans (Memory.putIndex_ne m (by omega) _)
    · exact run.index_frame (block_writes_below source p) after

theorem block_eval (source : Nat) (p : Polynomial Nat) (n : Nat) (m : Memory K) {P : K → Prop}
    (hm : Good P m) (hn : m.index source=n) :
    ∃ k t, Eval (Good P) (block source p) m k t ∧ k ≤ (timePolynomial p).eval n ∧ t.index 8=p.eval n ∧
      t.data=m.data ∧ ∀ i, 13 ≤ i → t.index i=m.index i := by
  obtain ⟨k,t,h,kb,v,hd,fi⟩ := block_eval_frame source p n m hm hn
  exact ⟨k,t,h,kb,v,hd,fun i hi => fi i (.inr hi)⟩

theorem onlineBit_eval (source n : Nat) (m : Memory K) {P : K → Prop} (hm : Good P m) (hn : m.index source=n) :
    ∃ k t, Eval (Good P) (block source onlineMinorBitPolynomial) m k t ∧
      k ≤ (timePolynomial onlineMinorBitPolynomial).eval n ∧ t.index 8=onlineMinorBitPolynomial.eval n ∧
      t.data=m.data ∧ ∀ i, 13 ≤ i → t.index i=m.index i := block_eval source onlineMinorBitPolynomial n m hm hn

/-- Return the dimension polynomial in address zero for a resident memory-window reservation. -/
noncomputable def toZero (source : Nat) (p : Polynomial Nat) : Block :=
  .seq (block source p) (.op (.addrCopy 0 8))

theorem toZero_eval (source : Nat) (p : Polynomial Nat) (n : Nat) (m : Memory K) {P : K → Prop}
    (hm : Good P m) (hn : m.index source=n) :
    ∃ k t, Eval (Good P) (toZero source p) m k t ∧ k ≤ (timePolynomial p+1).eval n ∧ t.index 0=p.eval n ∧
      t.data=m.data ∧ ∀ i, 13 ≤ i → t.index i=m.index i := by
  obtain ⟨k,t,run,bound,value,data,frame⟩ := block_eval source p n m hm hn
  refine ⟨k+1,_,run.seq (eval_copyI t run.safe_end 0 8),?_,?_,data,?_⟩
  · rw [Polynomial.eval_add,Polynomial.eval_one]; omega
  · simpa only [Memory.putIndex_same] using value
  · intro i hi
    exact (Memory.putIndex_ne t (by omega : i≠0) _).trans (frame i hi)

end AddressHorner
end BitRAM
end LinearProgramming
end Optimization
end OAI
