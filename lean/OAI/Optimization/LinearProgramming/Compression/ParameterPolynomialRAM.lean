import OAI.Optimization.LinearProgramming.RAM.SmallScalarLiterals
import OAI.Optimization.LinearProgramming.RAM.Array
import OAI.Optimization.LinearProgramming.RAM.RAMPolynomial
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Data.Nat.BitIndices

/-! Counted Horner evaluation of the fixed natural polynomials in the minor service.
The coefficients determine a finite block before any input is supplied. Successive doublings of one
construct each binary power used by a coefficient. The caller supplies a scalar register containing one. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression

open RAM

private def doubleToPower (reg : ℕ) : ℕ → Block
  | 0 => .skip
  | k+1 => .seq (doubleToPower reg k) (.op (.add reg reg reg))

private def addPowers (dst one : ℕ) : List ℕ → Block
  | [] => .skip
  | k::ks => .seq (doubleToPower one k) (.seq (.op (.add dst dst one))
      (.seq (.op (.const one 1)) (addPowers dst one ks)))

private def addUnits (dst one c : ℕ) : Block := addPowers dst one c.bitIndices

private def powerSteps (ks : List ℕ) : ℕ := (ks.map (fun k => k+2)).sum

private def fixedCoefficientSteps (c : ℕ) : ℕ := powerSteps c.bitIndices

/-- One doubling per preceding bit position and two instructions per set bit
suffice to add a fixed coefficient. -/
private theorem fixedCoefficientSteps_bound (c : ℕ) :
    fixedCoefficientSteps c ≤ (c.log2+1)*(c.log2+2) := by
  have hi (i : ℕ) (h : i ∈ c.bitIndices) : i ≤ c.log2 := by
    have hc : c ≠ 0 := by rintro rfl; simp at h
    exact (Nat.le_log2 hc).2 (Nat.two_pow_le_of_mem_bitIndices h)
  have hc : c.bitIndices.length ≤ c.log2+1 := by
    rw [← List.toFinset_card_of_nodup Nat.bitIndices_nodup]
    apply (Finset.card_le_card (t := Finset.range (c.log2+1)) ?_).trans_eq (Finset.card_range _)
    intro i hm
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (hi i (List.mem_toFinset.mp hm)))
  have hsum := (c.bitIndices.map (fun i => i+2)).sum_le_length_nsmul (c.log2+2) (by
    intro x hx
    obtain ⟨i,him,rfl⟩ := List.mem_map.mp hx
    exact Nat.add_le_add_right (hi i him) 2)
  exact (by simpa [fixedCoefficientSteps,powerSteps,nsmul_eq_mul] using hsum :
    fixedCoefficientSteps c ≤ c.bitIndices.length*(c.log2+2)).trans
      (Nat.mul_le_mul_right _ hc)

private def hornerBlock (input one dst : ℕ) : ℕ → (ℕ → ℕ) → Block
  | 0, _ => .op (.const dst 0)
  | k+1, a => .seq (hornerBlock input one dst k (fun i => a (i+1)))
      (.seq (.op (.mul dst dst input)) (addUnits dst one (a 0)))

private def hornerSteps : ℕ → (ℕ → ℕ) → ℕ
  | 0, _ => 1
  | k+1, a => hornerSteps k (fun i => a (i+1)) + (1 + fixedCoefficientSteps (a 0))

private def hornerValue : ℕ → (ℕ → ℕ) → ℕ → ℕ
  | 0, _, _ => 0
  | k+1, a, n => hornerValue k (fun i => a (i+1)) n * n + a 0

private theorem hornerValue_sum (k : ℕ) (a : ℕ → ℕ) (n : ℕ) :
    hornerValue k a n = ∑ i ∈ Finset.range k, a i * n^i := by
  induction k generalizing a with
  | zero => simp [hornerValue]
  | succ k ih => rw [hornerValue, ih, Finset.sum_mul, Finset.sum_range_succ']; simp [pow_succ, mul_assoc]

private theorem hornerValue_mono (k : ℕ) (a : ℕ → ℕ) {n m : ℕ} (hn : n ≤ m) :
    hornerValue k a n ≤ hornerValue k a m := by
  rw [hornerValue_sum, hornerValue_sum]
  exact Finset.sum_le_sum fun i _ => Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hn i)

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

private theorem doubleToPower_spec (P : K → Prop) (m : Memory K) (reg k : ℕ)
    (hs : m.AllData P) (h₁ : m.data reg = 1) (hval : ∀ j : ℕ, j ≤ 2^k → P (j:K)) :
    ∃ t, Block.Eval (Memory.AllData P) (doubleToPower reg k) m k t ∧
      t.data reg = ((2^k:ℕ):K) ∧ t.index = m.index ∧ ∀ j, j≠reg → t.data j = m.data j := by
  induction k with
  | zero => exact ⟨m, .skip hs, by simpa using h₁, rfl, fun _ _ => rfl⟩
  | succ k ih =>
    have hh : (2:ℕ)^k ≤ 2^(k+1) := Nat.pow_le_pow_right (by decide) (Nat.le_succ k)
    obtain ⟨s, run, sd, si, sf⟩ := ih (fun j hj => hval j (hj.trans hh))
    have he : s.data reg + s.data reg = ((2^(k+1):ℕ):K) := by rw [sd, pow_succ]; push_cast; ring
    have st : (s.putData reg (s.data reg+s.data reg)).AllData P :=
      run.safe_end.putData _ (he ▸ hval _ le_rfl)
    refine ⟨_,run.seq (Block.Eval.op_add s reg reg reg run.safe_end st), ?_, si, ?_⟩
    · simpa using he
    · intro j hj; exact (Memory.putData_ne _ hj _).trans (sf j hj)

private def powerSum (ks : List ℕ) : ℕ := (ks.map (fun k => 2^k)).sum

private theorem addPowers_spec (P : K → Prop) (m : Memory K) (dst one x : ℕ) (ks : List ℕ)
    (ho : one ≠ dst) (hs : m.AllData P) (hd : m.data dst = (x:K)) (h₁ : m.data one = 1)
    (hval : ∀ j ≤ x+powerSum ks, P (j:K)) :
    ∃ t, Block.Eval (Memory.AllData P) (addPowers dst one ks) m (powerSteps ks) t ∧
      t.data dst = ((x+powerSum ks:ℕ):K) ∧ t.index = m.index ∧ ∀ j, j≠dst → t.data j=m.data j := by
  induction ks generalizing m x with
  | nil => exact ⟨m, .skip hs, by simpa [powerSum] using hd, rfl, fun _ _ => rfl⟩
  | cons k ks ih =>
    have hsum : powerSum (k::ks) = 2^k + powerSum ks := by simp [powerSum]
    have cap : 2^k ≤ x+powerSum (k::ks) := by rw [hsum]; omega
    obtain ⟨s,run,sd,si,sf⟩ := doubleToPower_spec P m one k hs h₁
      (fun j hj => hval j (hj.trans cap))
    have he : s.data dst + s.data one = ((x + 2^k:ℕ):K) := by
      rw [sd, sf _ ho.symm, hd, Nat.cast_add]
    let u := s.putData dst (s.data dst + s.data one)
    have hu : u.AllData P := run.safe_end.putData _ (he ▸ hval _ (by rw [hsum]; omega))
    let v := u.putData one 1
    have hv : v.AllData P := hu.putData _ (h₁ ▸ hs one)
    have ea := Block.Eval.op_add s dst dst one run.safe_end hu
    have ec : Block.Eval (Memory.AllData P) (.op (.const one 1)) u 1 v := by
      simpa using Block.Eval.op_const u one 1 hu (by simpa using hv)
    have vd : v.data dst = ((x+2^k:ℕ):K) := by simp [v,u,Memory.putData_ne _ ho.symm,he]
    obtain ⟨t,tail,td,ti,tf⟩ := ih v (x+2^k) hv vd (by simp [v])
      (fun j hj => hval j (by rw [hsum]; omega))
    refine ⟨t,?_,?_,ti.trans si,?_⟩
    · have cost : powerSteps (k::ks) = k+(1+(1+powerSteps ks)) := by
        simp only [powerSteps,List.map_cons,List.sum_cons]; omega
      rw [cost]
      exact run.seq (ea.seq (ec.seq tail))
    · simpa [hsum, Nat.add_assoc] using td
    · intro j hj
      by_cases hj₁ : j=one
      · subst j; rw [tf one ho]; simpa [v] using h₁.symm
      · exact (tf _ hj).trans ((Memory.putData_ne _ hj₁ _).trans
          ((Memory.putData_ne _ hj _).trans (sf _ hj₁)))

private theorem addUnits_spec (P : K → Prop) (m : Memory K) (dst one k x : ℕ)
    (ho : one ≠ dst) (hs : m.AllData P) (hd : m.data dst = (x:K)) (h₁ : m.data one = 1)
    (hval : ∀ j ≤ x+k, P (j:K)) :
    ∃ t, Block.Eval (Memory.AllData P) (addUnits dst one k) m (fixedCoefficientSteps k) t ∧
      t.data dst = ((x+k:ℕ):K) ∧ t.index=m.index ∧ ∀ j, j≠dst → t.data j=m.data j := by
  simpa only [addUnits,fixedCoefficientSteps,powerSum,Nat.sum_map_two_pow_bitIndices] using
    addPowers_spec P m dst one x k.bitIndices ho hs hd h₁ (by simpa [powerSum] using hval)

private theorem hornerBlock_spec (P : K → Prop) (m : Memory K) (input one dst n k : ℕ)
    (a : ℕ → ℕ) (hi : input ≠ dst) (ho : one ≠ dst) (hin : m.data input = (n:K))
    (hone : m.data one = 1) (hs : m.AllData P)
    (hval : ∀ j ≤ hornerValue k a (n+1), P (j:K)) :
    ∃ t, Block.Eval (Memory.AllData P) (hornerBlock input one dst k a) m (hornerSteps k a) t ∧
      t.data dst = (hornerValue k a n:K) ∧ t.index = m.index ∧ ∀ j, j≠dst → t.data j=m.data j := by
  induction k generalizing a with
  | zero =>
    have hzero : P (0:K) := by simpa using hval 0 (Nat.zero_le _)
    refine ⟨m.putData dst 0, ?_, by simp [hornerValue], rfl, fun j hj => Memory.putData_ne _ hj _⟩
    simpa [hornerBlock,hornerSteps] using Block.Eval.op_const m dst 0 hs (by simpa using hs.putData dst hzero)
  | succ k ih =>
    let tail := fun i => a (i+1)
    have cap : hornerValue k tail (n+1) ≤ hornerValue (k+1) a (n+1) :=
      (Nat.le_mul_of_pos_right _ (Nat.succ_pos n)).trans (Nat.le_add_right ..)
    obtain ⟨s, run, sd, si, sf⟩ := ih tail (fun j hj => hval j (hj.trans cap))
    have he : s.data dst * s.data input = ((hornerValue k tail n * n : ℕ):K) := by
      rw [sd, sf input hi, hin, Nat.cast_mul]
    have hprod : hornerValue k tail n * n + a 0 ≤ hornerValue (k+1) a (n+1) :=
      Nat.add_le_add_right (Nat.mul_le_mul (hornerValue_mono k tail (Nat.le_succ n)) (Nat.le_succ n)) _
    let u := s.putData dst (s.data dst*s.data input)
    have hu : u.AllData P := run.safe_end.putData _ (he ▸ hval _ ((Nat.le_add_right ..).trans hprod))
    have hmul := Block.Eval.op_mul s dst dst input run.safe_end hu
    obtain ⟨t,adds,td,ti,tf⟩ := addUnits_spec P u dst one (a 0) (hornerValue k tail n*n) ho hu
      (by simpa [u] using he) ((Memory.putData_ne _ ho _).trans ((sf _ ho).trans hone))
      (fun j hj => hval j (hj.trans hprod))
    refine ⟨t,run.seq (hmul.seq adds), td, ti.trans si, ?_⟩
    intro j hj; exact (tf _ hj).trans ((Memory.putData_ne _ hj _).trans (sf _ hj))

/-- A single fixed instruction block for `p`, independent of the runtime input. -/
noncomputable def parameterPolynomialBlock (input one dst : ℕ) (p : Polynomial ℕ) : Block :=
  hornerBlock input one dst (p.natDegree+1) p.coeff

/-- Exact cost, including every addition used to materialize polynomial coefficients. -/
noncomputable def parameterPolynomialSteps (p : Polynomial ℕ) : ℕ := hornerSteps (p.natDegree+1) p.coeff

/-- Input-independent program text from coefficients in ascending degree order.
The list is supplied to the compiler, not to the running machine. -/
def parameterCoefficientBlock (input one dst : ℕ) (coeffs : List ℕ) : Block :=
  hornerBlock input one dst coeffs.length (fun i => coeffs[i]?.getD 0)

/-- The statically known execution length for an explicit coefficient list. -/
def parameterCoefficientSteps (coeffs : List ℕ) : ℕ :=
  hornerSteps coeffs.length (fun i => coeffs[i]?.getD 0)

/-- The number denoted by a list of coefficients in ascending degree order. -/
def parameterCoefficientValue (coeffs : List ℕ) (n : ℕ) : ℕ :=
  coeffs.foldr (fun c r => r*n+c) 0

private theorem hornerValue_list (cs : List ℕ) (n : ℕ) :
    hornerValue cs.length (fun i => cs[i]?.getD 0) n = parameterCoefficientValue cs n := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    simp only [List.length_cons,hornerValue,List.getElem?_cons_succ,List.getElem?_cons_zero,
      Option.getD_some,ih,parameterCoefficientValue,List.foldr_cons]

/-- Counted execution of the executable coefficient-list entry point. -/
theorem parameterCoefficientBlock_spec (P : K → Prop) (m : Memory K) (input one dst n : ℕ)
    (coeffs : List ℕ) (hi : input ≠ dst) (ho : one ≠ dst)
    (hin : m.data input = (n:K)) (hone : m.data one = 1) (hs : ∀ j, P (m.data j))
    (hval : ∀ j ≤ parameterCoefficientValue coeffs (n+1), P (j:K)) :
    ∃ t, Block.Eval (Memory.AllData P) (parameterCoefficientBlock input one dst coeffs)
      m (parameterCoefficientSteps coeffs) t ∧ t.data dst = ((parameterCoefficientValue coeffs n : ℕ):K) ∧
      t.index = m.index ∧ ∀ j, j≠dst → t.data j=m.data j := by
  simpa only [parameterCoefficientBlock,parameterCoefficientSteps,hornerValue_list] using
    hornerBlock_spec P m input one dst n coeffs.length (fun i => coeffs[i]?.getD 0)
      hi ho hin hone hs (fun j hj => hval j (hj.trans_eq (hornerValue_list ..)))

private theorem hornerBlock_congr (input one dst k : ℕ) (a b : ℕ → ℕ)
    (h : ∀ i < k, a i = b i) :
    hornerBlock input one dst k a = hornerBlock input one dst k b ∧
      hornerSteps k a = hornerSteps k b := by
  induction k generalizing a b with
  | zero => exact ⟨rfl,rfl⟩
  | succ k ih =>
    obtain ⟨hb,hs⟩ := ih (fun i => a (i+1)) (fun i => b (i+1)) (fun i hi => h (i+1) (by omega))
    simp only [hornerBlock,hornerSteps,hb,hs,h 0 (Nat.zero_lt_succ _),and_self]

/-- Select the finite list for a fixed mathematical polynomial. -/
noncomputable def parameterCoefficients (p : Polynomial ℕ) : List ℕ :=
  List.ofFn fun i : Fin (p.natDegree+1) => p.coeff i

/-- The canonical coefficient list represents the supplied mathematical polynomial. -/
theorem parameterCoefficientValue_canonical (p : Polynomial ℕ) (n : ℕ) :
    parameterCoefficientValue (parameterCoefficients p) n = p.eval n := by
  rw [← hornerValue_list,hornerValue_sum,Polynomial.eval_eq_sum_range,parameterCoefficients,List.length_ofFn]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [List.getElem?_ofFn, dite_eq_left (Finset.mem_range.mp hi), Option.getD_some]

/-- Both the emitted instructions and the exact step count agree with the executable
list-based compiler. -/
theorem parameterPolynomialBlock_eq_coefficients (input one dst : ℕ) (p : Polynomial ℕ) :
    parameterPolynomialBlock input one dst p = parameterCoefficientBlock input one dst (parameterCoefficients p) ∧
      parameterPolynomialSteps p = parameterCoefficientSteps (parameterCoefficients p) := by
  unfold parameterPolynomialBlock parameterPolynomialSteps parameterCoefficientBlock
    parameterCoefficientSteps parameterCoefficients
  simp only [List.length_ofFn]
  apply hornerBlock_congr
  intro i hi
  simp only [List.getElem?_ofFn, dite_eq_left hi, Option.getD_some]

/-- Polynomial text size in the degree and the bit size of the largest coefficient. -/
theorem parameterPolynomialSteps_bound (p : Polynomial ℕ) (b : ℕ)
    (h : ∀ i ≤ p.natDegree, (p.coeff i).log2 ≤ b) :
    parameterPolynomialSteps p ≤ 1 + (p.natDegree+1)*(1 + (b+1)*(b+2)) := by
  have aux (k : ℕ) (a : ℕ → ℕ) (ha : ∀ i<k, (a i).log2 ≤ b) :
      hornerSteps k a ≤ 1+k*(1+(b+1)*(b+2)) := by
    induction k generalizing a with
    | zero => simp [hornerSteps]
    | succ k ih =>
      have ht := ih (fun i => a (i+1)) (fun i hi => ha (i+1) (by omega))
      have h₀ := ha 0 (Nat.zero_lt_succ _)
      have he := (fixedCoefficientSteps_bound (a 0)).trans
        (Nat.mul_le_mul (Nat.add_le_add_right h₀ 1) (Nat.add_le_add_right h₀ 2))
      rw [hornerSteps,Nat.succ_mul]
      omega
  exact aux _ _ (fun i hi => h i (by omega))

/-- All intermediate computed scalars are natural numbers bounded by `p.eval (n+1)`.
Only `dst` differs at the end. All addresses are preserved. -/
theorem parameterPolynomialBlock_spec (P : K → Prop) (m : Memory K) (input one dst n : ℕ)
    (p : Polynomial ℕ) (hi : input ≠ dst) (ho : one ≠ dst)
    (hin : m.data input = (n:K)) (hone : m.data one = 1) (hs : ∀ j, P (m.data j))
    (hval : ∀ j ≤ p.eval (n+1), P (j:K)) :
    ∃ t, Block.Eval (Memory.AllData P) (parameterPolynomialBlock input one dst p)
      m (parameterPolynomialSteps p) t ∧ t.data dst = ((p.eval n : ℕ):K) ∧
      t.index = m.index ∧ ∀ j, j≠dst → t.data j=m.data j := by
  have hEval (x : ℕ) : hornerValue (p.natDegree+1) p.coeff x = p.eval x :=
    (hornerValue_sum ..).trans (Polynomial.eval_eq_sum_range x).symm
  simpa only [parameterPolynomialBlock, parameterPolynomialSteps, hEval] using
    hornerBlock_spec P m input one dst n (p.natDegree+1) p.coeff hi ho hin hone hs
      (fun j hj => hval j (hj.trans_eq (hEval _)))

/-- A numerical bound on the lengths of all written rationals in a complete block evaluation. -/
theorem parameterPolynomialBlock_bits (m : Memory ℚ) (input one dst n H : ℕ) (p : Polynomial ℕ)
    (hi : input ≠ dst) (ho : one ≠ dst) (hin : m.data input = n) (hone : m.data one = 1)
    (hs : ∀ j, ratBits (m.data j) ≤ H) :
    let bound := H + 3 + polyBound (p.eval 1) p.natDegree (n+1)
    ∃ t, Block.Eval (fun s => ∀ j, ratBits (s.data j) ≤ bound)
      (parameterPolynomialBlock input one dst p) m (parameterPolynomialSteps p) t ∧
      t.data dst = ((p.eval n : ℕ):ℚ) ∧ t.index = m.index ∧ ∀ j, j≠dst → t.data j=m.data j := by
  dsimp only
  apply parameterPolynomialBlock_spec (fun z : ℚ => ratBits z ≤ H + 3 + polyBound (p.eval 1) p.natDegree (n+1)) m input one dst n p hi ho hin hone
  · intro j; exact (hs j).trans (by omega)
  · intro j hj
    have h := hj.trans (polynomial_eval_le_polyBound p (n+1))
    simp only [ratBits, Rat.num_natCast, Int.natAbs_natCast, Rat.den_natCast]
    change 3 + j.log2 + 0 ≤ H+3+_
    have := Nat.log2_le_self j
    omega

private theorem doubleToPower_smallLiterals (reg k : ℕ) : (doubleToPower reg k).SmallScalarLiterals := by
  induction k <;> simp_all [doubleToPower,Block.SmallScalarLiterals]

private theorem addPowers_smallLiterals (dst one : ℕ) (bits : List ℕ) :
    (addPowers dst one bits).SmallScalarLiterals := by
  induction bits with
  | nil => exact True.intro
  | cons k bits ih => exact ⟨doubleToPower_smallLiterals .., True.intro, Or.inr rfl, ih⟩

private theorem hornerBlock_smallLiterals (input one dst k : ℕ) (a : ℕ → ℕ) :
    (hornerBlock input one dst k a).SmallScalarLiterals := by
  induction k generalizing a with
  | zero => exact Or.inl rfl
  | succ k ih => exact ⟨ih _,True.intro,addPowers_smallLiterals ..⟩

/-- The executable compiler's only possible scalar literals are zero and one, including
when a coefficient contains many nonzero bits. -/
theorem parameterCoefficientBlock_smallLiterals (input one dst : ℕ) (cs : List ℕ) :
    (parameterCoefficientBlock input one dst cs).SmallScalarLiterals := hornerBlock_smallLiterals ..

theorem parameterPolynomialBlock_smallLiterals (input one dst : ℕ) (p : Polynomial ℕ) :
    (parameterPolynomialBlock input one dst p).SmallScalarLiterals := hornerBlock_smallLiterals ..

end Compression
end LinearProgramming
end Optimization
end OAI
