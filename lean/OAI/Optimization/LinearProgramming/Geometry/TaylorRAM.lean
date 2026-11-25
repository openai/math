import OAI.Optimization.LinearProgramming.Geometry.Exponential
import OAI.Optimization.LinearProgramming.RAM.Code
import OAI.Optimization.LinearProgramming.Compression.PowerBits

/-! A fixed arithmetic-RAM loop for the two finite series in the geometric oracle. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Geometry
namespace TaylorRAM

open RAM Finset
open scoped BigOperators

/-- A term sequence whose ratio is a scalar times a ratio of affine counters. -/
structure Recurrence where
  factor : ℚ
  numStep : ℚ
  denStep : ℚ
  numerator : ℕ → ℚ
  denominator : ℕ → ℚ
  term : ℕ → ℚ
  num_succ : ∀ i, numerator i + numStep = numerator (i + 1)
  den_succ : ∀ i, denominator i + denStep = denominator (i + 1)
  term_succ : ∀ i, term i * factor * numerator i / denominator i = term (i + 1)
  den_ne : ∀ i, denominator i ≠ 0

def Recurrence.prefix (r : Recurrence) (i : ℕ) : ℚ := ∑ j ∈ range i, r.term j

/-- Both kernels run the same seven instructions per iteration. Registers 0 through
6 hold the sum, current term, multiplier, numerator, denominator and two increments. -/
def body : Block :=
  .seq (.op (.add 0 0 1)) <| .seq (.op (.mul 1 1 2)) <| .seq (.op (.mul 1 1 3)) <|
  .seq (.op (.div 1 1 4)) <| .seq (.op (.add 3 3 5)) <| .seq (.op (.add 4 4 6)) <|
  .op (.incr 0 0)

def kernel : Block := .loop (.addrLT 0 1) body

/-- State invariant at the head of a loop iteration. -/
structure AtHead (r : Recurrence) (M i : ℕ) (m : Memory ℚ) : Prop where
  counter : m.index 0 = i
  limit : m.index 1 = M
  sum : m.data 0 = r.prefix i
  term : m.data 1 = r.term i
  factor : m.data 2 = r.factor
  numerator : m.data 3 = r.numerator i
  denominator : m.data 4 = r.denominator i
  numStep : m.data 5 = r.numStep
  denStep : m.data 6 = r.denStep

/-- Values actually read or produced by the arithmetic instructions, including
the two products before division. -/
def registers (r : Recurrence) (i : ℕ) : List ℚ :=
  [0, r.prefix i, r.term i, r.factor, r.numerator i, r.denominator i, r.numStep,
    r.denStep, r.term i * r.factor, r.term i * r.factor * r.numerator i]

private def Safe (P : ℚ → Prop) (m : Memory ℚ) : Prop := ∀ j, P (m.data j)

private theorem put_safe {m : Memory ℚ} {P : ℚ → Prop} {q : ℚ} {d : ℕ}
    (hm : Safe P m) (hq : P q) : Safe P (m.putData d q) := by
  intro j
  by_cases h : j = d
  · subst j
    simpa [Memory.putData] using hq
  · simpa [Memory.putData, h] using hm j

private theorem eval_add {m : Memory ℚ} {P : ℚ → Prop} (d a b : ℕ) (q : ℚ)
    (hm : Safe P m) (hq : P q) (h : m.data a + m.data b = q) :
    Block.Eval (Safe P) (.op (.add d a b)) m 1 (m.putData d q) := by
  subst q
  exact .op hm (put_safe hm hq) (fun _ => rfl)

private theorem eval_mul {m : Memory ℚ} {P : ℚ → Prop} (d a b : ℕ) (q : ℚ)
    (hm : Safe P m) (hq : P q) (h : m.data a * m.data b = q) :
    Block.Eval (Safe P) (.op (.mul d a b)) m 1 (m.putData d q) := by
  subst q
  exact .op hm (put_safe hm hq) (fun _ => rfl)

private theorem eval_div {m : Memory ℚ} {P : ℚ → Prop} (d a b : ℕ) (q : ℚ)
    (hm : Safe P m) (hq : P q) (hn : m.data b ≠ 0) (h : m.data a / m.data b = q) :
    Block.Eval (Safe P) (.op (.div d a b)) m 1 (m.putData d q) := by
  subst q
  refine .op hm (put_safe hm hq) (fun pc => ?_)
  simp [execInstr, Memory.atPC, State.putData, Memory.putData, hn]

private theorem eval_incr {m : Memory ℚ} {P : ℚ → Prop} (a : ℕ) (i : ℕ)
    (hm : Safe P m) (h : m.index a = i) :
    Block.Eval (Safe P) (.op (.incr a a)) m 1 (m.putIndex a (i+1)) := by
  subst i
  exact .op hm hm (fun _ => rfl)

/-- The loop modifies only its low scratch registers and its own address counter. -/
structure Frame (m n : Memory ℚ) : Prop where
  data : ∀ j, 7 ≤ j → n.data j = m.data j
  index : ∀ j, j ≠ 0 → n.index j = m.index j

private theorem iteration {r : Recurrence} {M i : ℕ} {m : Memory ℚ} {P : ℚ → Prop}
    (hi : i < M) (hh : AtHead r M i m) (hm : Safe P m)
    (hP : ∀ k ≤ M, ∀ q ∈ registers r k, P q) :
    ∃ m', Block.Eval (Safe P) body m 7 m' ∧ AtHead r M (i+1) m' ∧ Frame m m' := by
  let m₁ := m.putData 0 (r.prefix (i+1))
  let m₂ := m₁.putData 1 (r.term i * r.factor)
  let m₃ := m₂.putData 1 (r.term i * r.factor * r.numerator i)
  let m₄ := m₃.putData 1 (r.term (i+1))
  let m₅ := m₄.putData 3 (r.numerator (i+1))
  let m₆ := m₅.putData 4 (r.denominator (i+1))
  let m₇ := m₆.putIndex 0 (i+1)
  have e₁ : Block.Eval (Safe P) (.op (.add 0 0 1)) m 1 m₁ :=
    eval_add _ _ _ _ hm (hP _ hi _ (by simp [registers]))
      (by rw [hh.sum, hh.term]; exact (sum_range_succ _ _).symm)
  have e₂ : Block.Eval (Safe P) (.op (.mul 1 1 2)) m₁ 1 m₂ :=
    eval_mul _ _ _ _ e₁.safe_end (hP _ hi.le _ (by simp [registers])) (by
      simp [m₁, Memory.putData, hh.term, hh.factor])
  have e₃ : Block.Eval (Safe P) (.op (.mul 1 1 3)) m₂ 1 m₃ :=
    eval_mul _ _ _ _ e₂.safe_end (hP _ hi.le _ (by simp [registers])) (by
      simp [m₂, m₁, Memory.putData, hh.numerator])
  have hd : m₃.data 4 = r.denominator i := by simp [m₃,m₂,m₁,Memory.putData,hh.denominator]
  have e₄ : Block.Eval (Safe P) (.op (.div 1 1 4)) m₃ 1 m₄ :=
    eval_div _ _ _ _ e₃.safe_end (hP _ hi _ (by simp [registers])) (hd ▸ r.den_ne i) (by
      rw [hd]; simpa [m₃, Memory.putData] using r.term_succ i)
  have e₅ : Block.Eval (Safe P) (.op (.add 3 3 5)) m₄ 1 m₅ :=
    eval_add _ _ _ _ e₄.safe_end (hP _ hi _ (by simp [registers])) (by
      simpa [m₄,m₃,m₂,m₁,Memory.putData,hh.numStep,hh.numerator] using r.num_succ i)
  have e₆ : Block.Eval (Safe P) (.op (.add 4 4 6)) m₅ 1 m₆ :=
    eval_add _ _ _ _ e₅.safe_end (hP _ hi _ (by simp [registers])) (by
      simpa [m₅,m₄,m₃,m₂,m₁,Memory.putData,hh.denStep,hh.denominator] using r.den_succ i)
  have e₇ : Block.Eval (Safe P) (.op (.incr 0 0)) m₆ 1 m₇ :=
    eval_incr _ _ e₆.safe_end hh.counter
  refine ⟨m₇, .seq e₁ (.seq e₂ (.seq e₃ (.seq e₄ (.seq e₅ (.seq e₆ e₇))))), ?_, ?_⟩
  · constructor <;> simp [m₇,m₆,m₅,m₄,m₃,m₂,m₁,Memory.putData,Memory.putIndex,
      hh.limit, hh.factor, hh.numStep, hh.denStep]
  · constructor
    · intro j hj
      have h₀ : j ≠ 0 := by omega
      have h₁ : j ≠ 1 := by omega
      have h₃ : j ≠ 3 := by omega
      have h₄ : j ≠ 4 := by omega
      simp [m₇,m₆,m₅,m₄,m₃,m₂,m₁,Memory.putData,Memory.putIndex,h₀,h₁,h₃,h₄]
    · intro j hj
      simp [m₇,m₆,m₅,m₄,m₃,m₂,m₁,Memory.putData,Memory.putIndex,hj]

/-- A complete execution, charging both loop tests and back jumps. The scalar
invariant is preserved at every intermediate instruction. -/
theorem run_kernel {r : Recurrence} {M i : ℕ} {m : Memory ℚ} {P : ℚ → Prop}
    (hi : i ≤ M) (hh : AtHead r M i m) (hm : ∀ j, P (m.data j))
    (hP : ∀ k ≤ M, ∀ q ∈ registers r k, P q) :
    ∃ m', Block.Eval (fun v => ∀ j, P (v.data j)) kernel m (9*(M-i)+1) m' ∧
      AtHead r M M m' ∧ Frame m m' := by
  generalize hleft : M - i = d
  induction d generalizing i m with
  | zero =>
    have heq : i = M := by omega
    subst i
    exact ⟨m, .loopFalse (by simp [Cond.test, hh.counter, hh.limit]) hm, hh, ⟨fun _ _ => rfl, fun _ _ => rfl⟩⟩
  | succ d ih =>
    have hlt : i < M := by omega
    obtain ⟨m₁, first, head, frame⟩ := iteration hlt hh hm hP
    obtain ⟨m₂, rest, final, frame'⟩ := ih hlt head first.safe_end (by omega)
    refine ⟨m₂, ?_, final, ⟨fun j hj => (frame'.data j hj).trans (frame.data j hj),
      fun j hj => (frame'.index j hj).trans (frame.index j hj)⟩⟩
    have hcond : (Cond.addrLT 0 1).test m = true := by
      simp [Cond.test, hh.counter, hh.limit, hlt]
    exact (show 1+7+1+(9*d+1) = 9*(d+1)+1 by omega) ▸
      Block.Eval.loopTrue hcond first rest


/-- Registers and counters at entry to the fixed code block. -/
def initial (r : Recurrence) (M : ℕ) : State ℚ :=
  start [0, M] [0, r.term 0, r.factor, r.numerator 0, r.denominator 0, r.numStep, r.denStep]

private theorem initial_head (r : Recurrence) (M : ℕ) : AtHead r M 0 (initial r M).memory := by
  constructor <;> simp [initial, start, State.memory, Recurrence.prefix]

private theorem initial_admits {r : Recurrence} {M : ℕ} {P : ℚ → Prop}
    (hP : ∀ k ≤ M, ∀ q ∈ registers r k, P q) (j : ℕ) : P ((initial r M).data j) := by
  apply hP 0 (Nat.zero_le _)
  by_cases hj : j < 7
  · interval_cases j <;> simp [initial, start, registers]
  · have hlen : [0, r.term 0, r.factor, r.numerator 0, r.denominator 0,
        r.numStep, r.denStep][j]? = none := List.getElem?_eq_none (by simp; omega)
    simp [initial, start, hlen, registers]

/-- The assembled kernel returns its series through scalar register zero.
Every instruction is included, including the final unsuccessful guard and halt. -/
theorem kernel_trace (r : Recurrence) (M : ℕ) (P : ℚ → Prop)
    (hP : ∀ i ≤ M, ∀ q ∈ registers r i, P q) :
    ∃ t : Fin (9 * M + 2 + 1) → State ℚ,
      Trace (kernel.compile 0 ++ [.halt 0]) (initial r M) (9 * M + 2) t ∧
      (t (Fin.last (9 * M + 2))).output = some 0 ∧
      (t (Fin.last (9 * M + 2))).data 0 = r.prefix M ∧ ∀ i j, P ((t i).data j) := by
  obtain ⟨m, he, hh, _⟩ := run_kernel (i := 0) (Nat.zero_le M) (initial_head r M)
    (initial_admits hP) hP
  simp only [Nat.sub_zero] at he
  obtain ⟨t, ht, ho, heq, hp⟩ := he.halted_trace (tag := 0)
  refine ⟨t, ht, ho, ?_, hp⟩
  exact (congrArg (fun mm : Memory ℚ => mm.data 0) heq).trans hh.sum

/-- Exponential Taylor terms obey the common ratio recurrence. -/
def expSeries (x : ℚ) : Recurrence where
  factor := x
  numStep := 0
  denStep := 1
  numerator := fun _ => 1
  denominator := fun i => (i : ℚ) + 1
  term := fun i => x ^ i / i.factorial
  num_succ := by simp
  den_succ := by simp
  term_succ := by
    intro i
    simp only [mul_one, Nat.factorial_succ, Nat.cast_mul, Nat.cast_succ, pow_succ,
      div_eq_mul_inv, _root_.mul_inv_rev]
    ring
  den_ne := by intro i; positivity

@[simp] theorem expSeries_prefix (x : ℚ) (m : ℕ) :
    (expSeries x).prefix m = expTruncation x m := rfl

/-- Odd series for `log 2`. The factor `2` is included in the initial term. -/
def logTwoSeries : Recurrence where
  factor := 1/9
  numStep := 2
  denStep := 2
  numerator := fun i => 2 * (i : ℚ) + 1
  denominator := fun i => 2 * (i : ℚ) + 3
  term := fun i => 2 * (1/3 : ℚ) ^ (2*i+1) / (2*(i : ℚ)+1)
  num_succ := by intro i; push_cast; ring
  den_succ := by intro i; push_cast; ring
  term_succ := by
    intro i
    have hn : 2*(i : ℚ)+1 ≠ 0 := by positivity
    rw [show 2 * (i+1) + 1 = (2*i+1)+2 by omega, pow_add]
    push_cast
    field_simp
    ring
  den_ne := by intro i; positivity

@[simp] theorem logTwoSeries_prefix (m : ℕ) :
    logTwoSeries.prefix m = Compression.logTruncation (2 : ℚ) m := by
  unfold Recurrence.prefix Compression.logTruncation
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  change 2 * (1/3 : ℚ) ^ (2*i+1) / (2 * (i : ℚ)+1) = _
  rw [show ((2 : ℚ)-1)/(2+1) = 1/3 by norm_num]
  ring


private theorem log2_le_size (n : ℕ) : n.log2 ≤ n.size := by
  rcases Nat.eq_zero_or_pos n with rfl | h
  · decide
  · exact ((Nat.log2_lt h.ne').2 (Nat.lt_size_self n)).le

theorem size_le_bits (x : ℚ) : x.den.size ≤ ratBits x := by
  have h : x.den.size ≤ x.den.log2 + 1 := Nat.size_le.mpr Nat.lt_log2_self
  unfold ratBits
  omega

theorem bits_of_size {x : ℚ} {w : ℕ}
    (hd : x.den.size ≤ w) (hn : x.num.natAbs.size ≤ w) : ratBits x ≤ 3 + 2*w := by
  unfold ratBits
  have h₁ := log2_le_size x.den
  have h₂ := log2_le_size x.num.natAbs
  omega

private theorem int_bits (n : ℕ) : ratBits (n : ℚ) = 3 + n.log2 := by
  simp [ratBits, show Nat.log2 1 = 0 by rfl]

private theorem factorial_bits (n : ℕ) : ratBits (n.factorial : ℚ) ≤ 3 + n*n := by
  rw [int_bits]
  apply Nat.add_le_add_left
  have h : n.factorial ≤ 2^(n*n) := by
    rw [pow_mul]
    exact (Nat.factorial_le_pow n).trans (Nat.pow_le_pow_left Nat.lt_two_pow_self.le _)
  apply Nat.le_of_lt_succ
  apply (Nat.log2_lt (Nat.factorial_ne_zero _)).2
  exact h.trans_lt (Nat.pow_lt_pow_right (by decide) (Nat.lt_succ_self _))

private theorem div_bits (x y : ℚ) : ratBits (x/y) ≤ ratBits x + ratBits y := by
  rw [div_eq_mul_inv]
  simpa only [Compression.ratBits_inv_eq] using Compression.ratBits_mul_le_add x y⁻¹

/-- All scalar values of the exponential loop (including temporarily enlarged
terms before the division instruction) lie under one input-size polynomial. -/
theorem exp_register_bits {x : ℚ} (hx : 0 ≤ x) (hx' : x ≤ 1) {i M : ℕ} (hi : i ≤ M)
    (q : ℚ) (hq : q ∈ registers (expSeries x) i) :
    ratBits q ≤ 100 * (M + ratBits x + 10)^2 := by
  let U := 100 * (M + ratBits x + 10)^2
  have hd := size_le_bits x
  have hbits := expTruncation_bitSize hx hx' hi
  have hpartial := bits_of_size hbits.1 hbits.2
  have hm₁ := Nat.mul_le_mul_left M hd
  have hp₀ : ratBits (expTruncation x i) ≤ U := by dsimp only [U]; nlinarith only [hpartial, hm₁, Nat.zero_le (M*M), Nat.zero_le (M*ratBits x)]
  have hcounter : ratBits ((i : ℚ) + 1) ≤ U := by
    norm_cast
    rw [int_bits]; dsimp only [U]; nlinarith only [Nat.log2_le_self (i+1), hi, Nat.zero_le (M*M), Nat.zero_le (M*ratBits x)]
  have ht := div_bits (x^i) (i.factorial : ℚ)
  have ht' := Compression.ratBits_natPow_le x i
  have hfac := factorial_bits i
  have hMM := Nat.mul_le_mul hi hi
  have hxM := Nat.mul_le_mul_right (ratBits x) hi
  have hp₁ : ratBits (x^i / (i.factorial : ℚ)) ≤ U := by dsimp only [U]; nlinarith only [ht, ht', hfac, hMM, hxM, Nat.zero_le (M*M), Nat.zero_le (M*ratBits x)]
  have hp₂ : ratBits (x^i / (i.factorial : ℚ) * x) ≤ U := by
    have h := Compression.ratBits_mul_le_add (x^i / (i.factorial : ℚ)) x
    dsimp only [U]
    nlinarith only [h, ht, ht', hfac, hMM, hxM, Nat.zero_le (M*M), Nat.zero_le (M*ratBits x)]
  have hxBit : ratBits x ≤ U := by dsimp only [U]; nlinarith only [Nat.zero_le M, Nat.zero_le (ratBits x), Nat.zero_le (M*ratBits x)]
  have hsmall : 3 ≤ U := by dsimp only [U]; nlinarith only [Nat.zero_le M, Nat.zero_le (ratBits x), Nat.zero_le (M*ratBits x)]
  change ratBits q ≤ U
  rw [registers, expSeries_prefix] at hq
  simp only [expSeries, mul_one, List.mem_cons, List.not_mem_nil,
    or_false] at hq
  rcases hq with e|e|e|e|e|e|e|e|e|e <;> subst q
  · exact hsmall
  · exact hp₀
  · exact hp₁
  · exact hxBit
  · exact hsmall
  · exact hcounter
  · exact hsmall
  · exact hsmall
  · exact hp₂
  · exact hp₂

private theorem logTwo_den_size : (((2 : ℚ)-1)/(2+1)).den.size = 2 := by
  rw [show ((2 : ℚ)-1)/(2+1) = 1/3 by norm_num]
  have hd : (1 / 3 : ℚ).den = 3 := by
    rw [one_div, Rat.den_inv_of_ne_zero (by norm_num : (3 : ℚ) ≠ 0)]
    norm_num
  rw [hd]
  apply Nat.le_antisymm (Nat.size_le.mpr (by decide))
  by_contra! h
  have hh := Nat.size_le.mp (show (3 : ℕ).size ≤ 1 by omega)
  norm_num at hh

/-- The fixed odd logarithm series works entirely with polynomial-bit scalars. -/
theorem log_register_bits {i M : ℕ} (hi : i ≤ M) (q : ℚ)
    (hq : q ∈ registers logTwoSeries i) : ratBits q ≤ 100*(M+10)^2 := by
  let U := 100*(M+10)^2
  have hbits := Compression.logTruncation_bitSize (z := 2) (by norm_num) hi
  simp only [logTwo_den_size] at hbits
  have hp₀ : ratBits (Compression.logTruncation 2 i) ≤ U := by
    have h := bits_of_size hbits.1 hbits.2
    dsimp only [U]
    nlinarith
  have hb₁ : ratBits (2*(i : ℚ)+1) ≤ 3+(2*i+1) := by
    norm_cast
    rw [int_bits]; exact Nat.add_le_add_left (Nat.log2_le_self _) 3
  have hb₃ : ratBits (2*(i : ℚ)+3) ≤ 3+(2*i+3) := by
    norm_cast
    rw [int_bits]; exact Nat.add_le_add_left (Nat.log2_le_self _) 3
  let t := 2 * (1/3 : ℚ)^(2*i+1) / (2*(i : ℚ)+1)
  have hth := div_bits (2 * (1/3 : ℚ)^(2*i+1)) (2*(i : ℚ)+1)
  have ht₁ := Compression.ratBits_mul_le_add 2 ((1/3 : ℚ)^(2*i+1))
  have ht₂ := Compression.ratBits_natPow_le (1/3) (2*i+1)
  have c2 : ratBits 2 = 4 := by rfl
  have c3 : ratBits (1/3) = 4 := by
    rw [one_div, Compression.ratBits_inv_eq]
    rfl
  have c9 : ratBits (1/9) = 6 := by
    rw [one_div, Compression.ratBits_inv_eq]
    rfl
  rw [c3] at ht₂
  rw [c2] at ht₁
  change ratBits t ≤ _ at hth
  have hm₁ := Compression.ratBits_mul_le_add t (1/9)
  have hm₂ := Compression.ratBits_mul_le_add (t*(1/9)) (2*(i:ℚ)+1)
  rw [c9] at hm₁
  have hshort : 30*i+100 ≤ U := by dsimp only [U]; nlinarith only [hi, Nat.zero_le (M*M)]
  have ht : ratBits t ≤ 12*i+30 := by linarith only [hth, ht₁, ht₂, hb₁]
  have hprod1 : ratBits (t*(1/9)) ≤ 12*i+36 := by omega
  have hprod2 : ratBits (t*(1/9)*(2*(i:ℚ)+1)) ≤ 20*i+50 := by omega
  change ratBits q ≤ U
  rw [registers, logTwoSeries_prefix] at hq
  simp only [logTwoSeries, List.mem_cons, List.not_mem_nil,
    or_false] at hq
  rcases hq with h|h|h|h|h|h|h|h|h|h <;> subst q
  · change 3 ≤ U; omega
  · exact hp₀
  · change ratBits t ≤ U; omega
  · rw [c9]; omega
  · omega
  · omega
  · rw [c2]; omega
  · rw [c2]; omega
  · change ratBits (t*(1/9)) ≤ U; omega
  · change ratBits (t*(1/9)*(2*(i:ℚ)+1)) ≤ U; omega

end TaylorRAM
end Geometry
end LinearProgramming
end Optimization
end OAI
