import OAI.Optimization.LinearProgramming.Compression.ParameterPowerRAM
import OAI.Optimization.LinearProgramming.Compression.ParameterPolynomialRAM
import OAI.Optimization.LinearProgramming.RAM.NatCast
import OAI.Optimization.LinearProgramming.RAM.Footprint
import OAI.Optimization.LinearProgramming.RAM.RAMPolynomial
import Mathlib.Algebra.Polynomial.Eval.Defs

/-! ## Initialization of the dimensions and cutoffs on the scalar/address RAM

The only input is the dimension in address register zero. For any prescribed fixed
natural polynomial `p` the same instruction list works for all dimensions. The initialized
registers contain the radius `B`, the grid denominator `2^(B+7)`, and `2^(p(N))`.
Both powers are also written as ordinary binary digit streams. No scalar bits are read.
-/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression

open RAM Polynomial

/-- The radius in Section 3 as a fixed natural polynomial. -/
noncomputable def parameterRadiusPolynomial : Polynomial ℕ := 100*(X+1)^3

noncomputable def parameterGridExponent : Polynomial ℕ := parameterRadiusPolynomial+7

@[simp] theorem parameterRadiusPolynomial_eval (n : ℕ) : parameterRadiusPolynomial.eval n = 100*(n+1)^3 := by
  simp [parameterRadiusPolynomial]

@[simp] theorem parameterGridExponent_eval (n : ℕ) : parameterGridExponent.eval n = 100*(n+1)^3+7 := by
  simp [parameterGridExponent]

/-- A prescribed polynomial is supplied in ascending coefficient order. These two
fixed lists are the binomial expansions of `100*(X+1)^3` and `100*(X+1)^3+7`. -/
def radiusCoefficients : List ℕ := [100,300,300,100]

def gridExponentCoefficients : List ℕ := [107,300,300,100]

private theorem radiusCoefficients_value (n : ℕ) :
    parameterCoefficientValue radiusCoefficients n = parameterRadiusPolynomial.eval n := by
  simp [parameterCoefficientValue,radiusCoefficients]; ring

private theorem gridExponentCoefficients_value (n : ℕ) :
    parameterCoefficientValue gridExponentCoefficients n = parameterGridExponent.eval n := by
  simp [parameterCoefficientValue,gridExponentCoefficients]; ring

/-- The mathematical polynomial denoted by a concrete ascending list. This is used
only for the complexity proof. Trailing zeros are allowed. -/
noncomputable def parameterListPolynomial : List ℕ → Polynomial ℕ
  | [] => 0
  | c::cs => (parameterListPolynomial cs)*X+C c

theorem parameterListPolynomial_eval (cs : List ℕ) (n : ℕ) :
    parameterCoefficientValue cs n = (parameterListPolynomial cs).eval n := by
  induction cs with
  | nil => simp [parameterCoefficientValue,parameterListPolynomial]
  | cons c cs ih =>
    simpa only [parameterCoefficientValue,List.foldr_cons,parameterListPolynomial,eval_add,eval_mul,
      eval_X,eval_C] using congrArg (fun z : ℕ => z*n+c) ih

/-- Scalar 0 receives the dimension, 1 holds one, 2 holds the radius, 3 and 4 hold
both exponents, and 5 and 6 hold both powers. After evaluating the polynomials, both
power loops reuse scalar 0 as their counter. The two address digit streams start at 8,
and address register 2 finishes just beyond the last digit. -/
def parameterBlockFromCoefficients (cs : List ℕ) : Block :=
  .seq (natCastBlock 0 1 1 0) <|
  .seq (parameterCoefficientBlock 0 1 2 radiusCoefficients) <|
  .seq (parameterCoefficientBlock 0 1 3 gridExponentCoefficients) <|
  .seq (parameterCoefficientBlock 0 1 4 cs) <|
  .seq (.op (.addrConst 2 8)) <|
  .seq (parameterPowerBlock 3 1 5 0) (parameterPowerBlock 4 1 6 0)

/-- The fully executable compiler from a fixed coefficient list to primitive code. -/
def parameterProgramFromCoefficients (cs : List ℕ) : Program :=
  (parameterBlockFromCoefficients cs).compile 0 ++ [.halt 0]

noncomputable def parameterBlock (p : Polynomial ℕ) : Block := parameterBlockFromCoefficients (parameterCoefficients p)

noncomputable def parameterProgram (p : Polynomial ℕ) : Program := parameterProgramFromCoefficients (parameterCoefficients p)

/-- Exact primitive step count before halt, including both doubling loops. -/
def parameterStepsFromCoefficients (cs : List ℕ) (n : ℕ) : ℕ :=
  (4*n+4) + (parameterCoefficientSteps radiusCoefficients +
    (parameterCoefficientSteps gridExponentCoefficients + (parameterCoefficientSteps cs +
    (1 + ((6*(100*(n+1)^3+7)+7) + (6*parameterCoefficientValue cs n+7))))))

noncomputable def parameterBlockSteps (p : Polynomial ℕ) (n : ℕ) : ℕ :=
  parameterStepsFromCoefficients (parameterCoefficients p) n

/-- An explicit natural bound for every counter and every polynomial-evaluation intermediate.
The dyadic scalars themselves have at most this many doublings. -/
noncomputable def parameterCounterCap (p : Polynomial ℕ) (n : ℕ) : ℕ :=
  1+n + parameterRadiusPolynomial.eval (n+1) + parameterGridExponent.eval (n+1) +
    p.eval (n+1) + parameterGridExponent.eval n + p.eval n

noncomputable def parameterBits (p : Polynomial ℕ) (n : ℕ) : ℕ := 3+4*parameterCounterCap p n

/-- All returned values and the two binary streams. Digits are in most-significant-first order. -/
structure ParameterOutput {K : Type*} [Field K] (p : Polynomial ℕ) (n : ℕ) (t : Memory K) : Prop where
  radius : t.data 2 = ((100*(n+1)^3:ℕ):K)
  gridExponent : t.data 3 = ((100*(n+1)^3+7:ℕ):K)
  cutoffExponent : t.data 4 = ((p.eval n : ℕ) : K)
  grid : t.data 5 = (2:K)^(100*(n+1)^3+7)
  cutoff : t.data 6 = (2:K)^(p.eval n)
  gridDigits : ∀ r≤parameterGridExponent.eval n, t.index (8+r) = if r=0 then 1 else 0
  cutoffDigits : ∀ r≤p.eval n, t.index ((8+parameterGridExponent.eval n+1)+r) = if r=0 then 1 else 0
  tapeEnd : t.index 2 = (8+parameterGridExponent.eval n+1)+p.eval n+1

/-- The initializer can run with live input scalars above its scratch registers. Only
address registers 1–3 and the two output tapes can change in the address bank. -/
structure ParameterFrame {K : Type*} (p : Polynomial ℕ) (n : ℕ) (entry finish : Memory K) : Prop where
  scalarsFromSeven : ∀ i, 7 ≤ i → finish.data i=entry.data i
  addresses : ∀ i, i≠1 → i≠2 → i≠3 → (i < 8 ∨ (8+parameterGridExponent.eval n+1)+p.eval n+1 ≤ i) →
    finish.index i=entry.index i

theorem parameter_nat_bits (j : ℕ) : ratBits (j:ℚ) ≤ 3+j := by
  simp only [ratBits, Rat.num_natCast, Int.natAbs_natCast, Rat.den_natCast]
  rw [show Nat.log2 1=0 by decide, Nat.add_zero]
  exact Nat.add_le_add_left (Nat.log2_le_self j) _

theorem parameter_pow_bits (j : ℕ) : ratBits ((2:ℚ)^j) ≤ 3+4*j := by
  have cast : ((2 ^ j : ℕ) : ℚ) = (2 : ℚ) ^ j := Nat.cast_pow 2 j
  rw [← cast]
  simp only [ratBits, Rat.num_natCast, Int.natAbs_natCast, Rat.den_natCast, Nat.log2_two_pow]
  change 3 + j + 0 ≤ 3 + 4 * j
  omega

/-- The original high-register frame is also available directly to existing callers. -/
theorem ParameterFrame.scalars {K : Type*} {p n} {entry finish : Memory K} (h : ParameterFrame p n entry finish)
    (i : ℕ) (hi : 8 ≤ i) : finish.data i=entry.data i := h.scalarsFromSeven i (by omega)

/-- The physical parameter initializer uses only ordered-field arithmetic. A supplied scalar
policy can bound intermediate integers and dyadic powers independently of the data word type. -/
theorem parameterBlockFromCoefficients_generic {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (cs : List ℕ) (p : Polynomial ℕ) (hev : ∀ n, parameterCoefficientValue cs n = p.eval n)
    (m : Memory K) (n : ℕ) (hdim : m.index 0=n) (P : K → Prop) (hm : m.AllData P)
    (hn : ∀ j≤parameterCounterCap p n, P (j:K)) (hp : ∀ j≤parameterCounterCap p n, P ((2:K)^j)) :
    ∃ t, Block.Eval (Memory.AllData P) (parameterBlockFromCoefficients cs) m (parameterStepsFromCoefficients cs n) t ∧
      ParameterOutput p n t ∧ ParameterFrame p n m t := by
  let cap := parameterCounterCap p n
  have hnN : n ≤ cap := by dsimp [cap,parameterCounterCap]; omega
  have hB : parameterRadiusPolynomial.eval (n+1) ≤ cap := by dsimp [cap,parameterCounterCap]; omega
  have hG : parameterGridExponent.eval (n+1) ≤ cap := by dsimp [cap,parameterCounterCap]; omega
  have hP : p.eval (n+1) ≤ cap := by dsimp [cap,parameterCounterCap]; omega
  have hge : parameterGridExponent.eval n ≤ cap := by dsimp [cap,parameterCounterCap]; omega
  have hpe : p.eval n ≤ cap := by dsimp [cap,parameterCounterCap]; omega
  obtain ⟨s,e₀,h₀,h₁,_,is₀,fs₀⟩ := natCastBlock_correct P m 0 1 1 0 n (by decide) (by decide) hdim hm
    (by simpa using hn 1 (by dsimp [cap,parameterCounterCap]; omega)) (fun j hj => hn j (hj.trans hnN))
  obtain ⟨a,e₁,ha,ia,fa⟩ := parameterCoefficientBlock_spec P s 0 1 2 n radiusCoefficients
    (by decide) (by decide) h₀ h₁ e₀.safe_end (fun j hj => hn j ((hj.trans_eq (radiusCoefficients_value _)).trans hB))
  obtain ⟨b,e₂,hb,ib,fb⟩ := parameterCoefficientBlock_spec P a 0 1 3 n gridExponentCoefficients
    (by decide) (by decide) ((fa 0 (by decide)).trans h₀) ((fa 1 (by decide)).trans h₁)
    e₁.safe_end (fun j hj => hn j ((hj.trans_eq (gridExponentCoefficients_value _)).trans hG))
  obtain ⟨c,e₃,hc,ic,fc⟩ := parameterCoefficientBlock_spec P b 0 1 4 n cs
    (by decide) (by decide) ((fb 0 (by decide)).trans ((fa 0 (by decide)).trans h₀))
    ((fb 1 (by decide)).trans ((fa 1 (by decide)).trans h₁))
    e₂.safe_end (fun j hj => hn j ((hj.trans_eq (hev _)).trans hP))
  rw [radiusCoefficients_value] at ha
  rw [gridExponentCoefficients_value] at hb
  rw [hev] at hc
  let v := c.putIndex 2 8
  have e₄ : Block.Eval (Memory.AllData P) (.op (.addrConst 2 8)) c 1 v :=
    Block.Eval.op_addrConst c 2 8 e₃.safe_end e₃.safe_end
  have h1c : v.data 1 = 1 := (fc 1 (by decide)).trans ((fb 1 (by decide)).trans ((fa 1 (by decide)).trans h₁))
  obtain ⟨d,e₅,hE,_,hdcur,fd,id₅,dd⟩ := parameterPowerBlock_spec P v 8 3 1 5 0 _
    (by decide) (by simp [v]) ((fc 3 (by decide)).trans hb) h1c (by decide) (by decide)
    (by decide) (by decide) (by decide) e₄.safe_end (fun j hj => hp j (hj.trans hge))
    (fun j hj => hn j (hj.trans hge))
  obtain ⟨t,e₆,hcut,_,htcur,ft,fi,dt⟩ := parameterPowerBlock_spec P d _ 4 1 6 0 _
    (by omega : 4 ≤ 8+parameterGridExponent.eval n+1) hdcur ((fd 4 (by decide) (by decide)).trans hc)
    ((fd 1 (by decide) (by decide)).trans h1c) (by decide) (by decide) (by decide)
    (by decide) (by decide) e₅.safe_end (fun j hj => hp j (hj.trans hpe)) (fun j hj => hn j (hj.trans hpe))
  refine ⟨t,?_,⟨?_,?_,?_,?_,hcut,?_,dt,htcur⟩,?_,?_⟩
  · change Block.Eval (fun s => ∀ j, P (s.data j)) (parameterBlockFromCoefficients cs) m
        (parameterStepsFromCoefficients cs n) t
    simpa only [parameterBlockFromCoefficients,parameterStepsFromCoefficients,hev,parameterGridExponent_eval]
      using e₀.seq (e₁.seq (e₂.seq (e₃.seq (e₄.seq (e₅.seq e₆)))))
  · simpa using (ft 2 (by decide) (by decide)).trans ((fd 2 (by decide) (by decide)).trans
      ((fc 2 (by decide)).trans ((fb 2 (by decide)).trans ha)))
  · simpa using (ft 3 (by decide) (by decide)).trans ((fd 3 (by decide) (by decide)).trans
      ((fc 3 (by decide)).trans hb))
  · exact (ft 4 (by decide) (by decide)).trans ((fd 4 (by decide) (by decide)).trans hc)
  · simpa using (ft 5 (by decide) (by decide)).trans hE
  · intro r hr
    exact (fi _ (by omega) (by omega) (Or.inl (by omega))).trans (dd r hr)
  · intro i hi
    rw [ft i (by omega) (by omega), fd i (by omega) (by omega)]
    change c.data i = m.data i
    rw [fc i (by omega),fb i (by omega),fa i (by omega),fs₀ i (by omega) (by omega)]
  · intro i h₁i h₂i h₃i hfar
    rw [fi i h₂i h₃i (by omega), id₅ i h₂i h₃i (by omega)]
    change (c.putIndex 2 8).index i=m.index i
    rw [Memory.putIndex_ne _ h₂i _,ic,ib,ia,is₀ i h₁i]

/-- Correctness and a register-bit invariant at every primitive step of initialization. -/
theorem parameterBlockFromCoefficients_spec (cs : List ℕ) (p : Polynomial ℕ)
    (hev : ∀ n, parameterCoefficientValue cs n = p.eval n)
    (m : Memory ℚ) (n : ℕ) (hdim : m.index 0=n) (ambient : ℕ) (hambient : parameterBits p n ≤ ambient)
    (hm : m.AllData (fun x => ratBits x ≤ ambient)) :
    ∃ t, Block.Eval (Memory.AllData fun x => ratBits x ≤ ambient)
      (parameterBlockFromCoefficients cs) m (parameterStepsFromCoefficients cs n) t ∧
        ParameterOutput p n t ∧ ParameterFrame p n m t := by
  apply parameterBlockFromCoefficients_generic cs p hev m n hdim (fun x => ratBits x ≤ ambient) hm
  · intro j hj
    exact (parameter_nat_bits j).trans (by unfold parameterBits at hambient; omega)
  · intro j hj
    exact (parameter_pow_bits j).trans (by unfold parameterBits at hambient; omega)

/-- A full halted trace from a single dimension address. Each address value and every
rational register on the whole trace has a dimension-polynomial bound. -/
theorem parameterProgramFromCoefficients_trace (cs : List ℕ) (p : Polynomial ℕ)
    (hev : ∀ n, parameterCoefficientValue cs n = p.eval n) (n : ℕ) :
    let steps := parameterStepsFromCoefficients cs n+1
    ∃ t : Fin (steps+1) → State ℚ, Trace (parameterProgramFromCoefficients cs) (start [n] []) steps t ∧
      (t (Fin.last steps)).output = some 0 ∧ ParameterOutput p n (t (Fin.last steps)).memory ∧
      (∀ i, scalarBound (parameterBits p n) (t i)) ∧
      (∀ i j, (t i).index j ≤ addressBudget (parameterProgramFromCoefficients cs)+n+1+steps) := by
  let m := (start [n] ([] : List ℚ)).memory
  have hdim : m.index 0=n := rfl
  have hs : m.AllData (fun x => ratBits x ≤ parameterBits p n) := by
    intro j
    change ratBits 0 ≤ _
    have h : ratBits 0=3 := by decide
    rw [h,parameterBits]; omega
  obtain ⟨last,run,hlast,_⟩ := parameterBlockFromCoefficients_spec cs p hev m n hdim _ le_rfl hs
  obtain ⟨t,ht,ho,hm,hall⟩ := run.halted_trace (tag := 0)
  refine ⟨t,ht,ho,hm ▸ hlast,hall,?_⟩
  intro i j
  let B := addressBudget (parameterProgramFromCoefficients cs)+n+1
  have hfoot : Footprint B (start [n] ([]:List ℚ)) := by
    apply Footprint.initial
    · simp
    · simp [B]
    · intro a ha
      have heq : a=n := by simpa using ha
      subst a; dsimp [B]; omega
  have hi := (trace_footprint (p := parameterProgramFromCoefficients cs) (by dsimp [B]; omega) hfoot ht i).address j
  have hil := i.isLt
  dsimp only [B] at hi
  omega

/-- Every concrete list, including an empty list or a list ending in zeros, yields a
fixed program with the claimed meanings for both output tapes and registers. -/
theorem explicitParameterProgram_trace (cs : List ℕ) (n : ℕ) :
    let p := parameterListPolynomial cs
    let steps := parameterStepsFromCoefficients cs n+1
    ∃ t : Fin (steps+1) → State ℚ, Trace (parameterProgramFromCoefficients cs) (start [n] []) steps t ∧
      (t (Fin.last steps)).output = some 0 ∧ ParameterOutput p n (t (Fin.last steps)).memory ∧
      (∀ i, scalarBound (parameterBits p n) (t i)) ∧
      (∀ i j, (t i).index j ≤ addressBudget (parameterProgramFromCoefficients cs)+n+1+steps) :=
  parameterProgramFromCoefficients_trace cs _ (parameterListPolynomial_eval cs) n

/-- Mathematical-polynomial presentation of the same certified executable program. -/
theorem parameterProgram_trace (p : Polynomial ℕ) (n : ℕ) :
    let steps := parameterBlockSteps p n+1
    ∃ t : Fin (steps+1) → State ℚ, Trace (parameterProgram p) (start [n] []) steps t ∧
      (t (Fin.last steps)).output = some 0 ∧ ParameterOutput p n (t (Fin.last steps)).memory ∧
      (∀ i, scalarBound (parameterBits p n) (t i)) ∧
      (∀ i j, (t i).index j ≤ addressBudget (parameterProgram p)+n+1+steps) :=
  parameterProgramFromCoefficients_trace _ p (parameterCoefficientValue_canonical p) n

/-- A polynomial that covers the exact time, all intermediate rational encodings, and
all address values. Its coefficients include the actual fixed program and branch overhead. -/
noncomputable def parameterResourcePolynomialFromCoefficients (cs : List ℕ) (p : Polynomial ℕ) : Polynomial ℕ :=
  let t := (4*X+4) + (C (parameterCoefficientSteps radiusCoefficients) +
    (C (parameterCoefficientSteps gridExponentCoefficients) + (C (parameterCoefficientSteps cs) +
    (1 + ((6*parameterGridExponent+7) + (6*p+7)))))) + 1
  let totals := 1+X + parameterRadiusPolynomial.comp (X+1) + parameterGridExponent.comp (X+1) +
    p.comp (X+1) + parameterGridExponent + p
  t + (3+4*totals) + C (addressBudget (parameterProgramFromCoefficients cs)) + X + 1

noncomputable def parameterResourcePolynomial (p : Polynomial ℕ) : Polynomial ℕ :=
  parameterResourcePolynomialFromCoefficients (parameterCoefficients p) p

theorem parameterListResourcePolynomial_eval (cs : List ℕ) (p : Polynomial ℕ)
    (hev : ∀ n, parameterCoefficientValue cs n = p.eval n) (n : ℕ) :
    (parameterResourcePolynomialFromCoefficients cs p).eval n = (parameterStepsFromCoefficients cs n+1) +
      parameterBits p n + addressBudget (parameterProgramFromCoefficients cs)+n+1 := by
  unfold parameterResourcePolynomialFromCoefficients parameterStepsFromCoefficients parameterBits parameterCounterCap
  dsimp only
  simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X,
    Polynomial.eval_one,Polynomial.eval_ofNat,Polynomial.eval_comp,parameterGridExponent_eval,hev]

theorem explicit_parameter_polynomial_resources (cs : List ℕ) :
    ∃ c d : ℕ, ∀ n, parameterStepsFromCoefficients cs n+1 ≤ polyBound c d n ∧
      parameterBits (parameterListPolynomial cs) n ≤ polyBound c d n ∧
      addressBudget (parameterProgramFromCoefficients cs)+n+1+(parameterStepsFromCoefficients cs n+1) ≤
        polyBound c d n := by
  let q := parameterResourcePolynomialFromCoefficients cs (parameterListPolynomial cs)
  refine ⟨q.eval 1,q.natDegree,?_⟩
  intro n
  have ht := polynomial_eval_le_polyBound q n
  rw [show q.eval n = _ from parameterListResourcePolynomial_eval cs _ (parameterListPolynomial_eval cs) n] at ht
  omega

theorem parameterResourcePolynomial_eval (p : Polynomial ℕ) (n : ℕ) :
    (parameterResourcePolynomial p).eval n = (parameterBlockSteps p n+1) +
      parameterBits p n + addressBudget (parameterProgram p)+n+1 := by
  exact parameterListResourcePolynomial_eval (parameterCoefficients p) p (parameterCoefficientValue_canonical p) n

/-- The exact-cost implementation fits a single dimension-polynomial RAM envelope,
including the binary digits explicitly written for its two powers. -/
theorem parameter_polynomial_resources (p : Polynomial ℕ) :
    ∃ c d : ℕ, ∀ n, parameterBlockSteps p n+1 ≤ polyBound c d n ∧
      parameterBits p n ≤ polyBound c d n ∧
      addressBudget (parameterProgram p)+n+1+(parameterBlockSteps p n+1) ≤ polyBound c d n := by
  refine ⟨(parameterResourcePolynomial p).eval 1,(parameterResourcePolynomial p).natDegree,?_⟩
  intro n
  have ht := polynomial_eval_le_polyBound (parameterResourcePolynomial p) n
  rw [parameterResourcePolynomial_eval] at ht
  omega

/-- One fixed primitive program for an explicitly prescribed polynomial. The same
monomial bounds the step count, every intermediate rational encoding, and the binary
length of every address word for every dimension. -/
theorem explicitParameterProgram_uniform (cs : List ℕ) :
    ∃ c d : ℕ, ∀ n, ∃ k ≤ polyBound c d n, ∃ t : Fin (k+1) → State ℚ,
      Trace (parameterProgramFromCoefficients cs) (start [n] []) k t ∧
      (t (Fin.last k)).output = some 0 ∧ ParameterOutput (parameterListPolynomial cs) n (t (Fin.last k)).memory ∧
      ∀ i, scalarBound (polyBound c d n) (t i) ∧ ∀ j, ((t i).index j).log2+1 ≤ polyBound c d n := by
  obtain ⟨c,d,h⟩ := explicit_parameter_polynomial_resources cs
  refine ⟨c+1,d,fun n => ?_⟩
  have extra : polyBound c d n + 1 ≤ polyBound (c+1) d n := by
    unfold polyBound
    rw [Nat.add_mul, Nat.one_mul]
    exact Nat.add_le_add_left (Nat.pow_pos (Nat.succ_pos n)) _
  obtain ⟨ht,hb,ha⟩ := h n
  obtain ⟨t,tr,done,vals,sc,idx⟩ := explicitParameterProgram_trace cs n
  have weak := (Nat.le_succ _).trans extra
  refine ⟨_,ht.trans weak,t,tr,done,vals,fun i => ⟨fun j => (sc i j).trans (hb.trans weak),?_⟩⟩
  intro j
  exact (Nat.add_le_add_right (((t i).index j).log2_le_self.trans ((idx i j).trans ha)) 1).trans extra

end Compression
end LinearProgramming
end Optimization
end OAI
