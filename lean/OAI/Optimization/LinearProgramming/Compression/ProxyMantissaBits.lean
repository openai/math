import OAI.Optimization.LinearProgramming.Compression.ProxyMantissaProgram
import OAI.Optimization.LinearProgramming.Compression.ProxyBoundedRun
import OAI.Optimization.LinearProgramming.Compression.ProxySeriesBits
import OAI.Optimization.LinearProgramming.Compression.ProxyGridBits

/-! Polynomial rational encoding lengths throughout the full normalized
small-logarithm computation, including its series and grid stages. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression

open OAI.Optimization.LinearProgramming.RAM OAI.Optimization.LinearProgramming.FieldTransfer

private theorem bounded_series_region {z : ℚ} (hz : 1 ≤ z) (M B : ℕ) {a u : State ℚ}
    (hp : a.pc = 9) (ho : a.output = none) (hd : a.data 0 = z) (hm : a.index 0 = M)
    (hb : scalarBound B a) (hu : runExactly mantissaProgram a (9+7*M+2) = some u) :
    RegisterBoundedRun mantissaProgram a (9+7*M+2) u (10^9 * seriesRegisterBase B M) := by
  let s := {a with pc := 0}
  have reset : stateAt 9 s = a := by cases a; simp_all [s, stateAt]
  obtain ⟨v, hv, _, hlive, _⟩ := series_run_until_halt hz M s rfl ho hd hm
  have localRun : RegisterBoundedRun logSeriesProgram s (9+7*M+2) v
      (10^9 * seriesRegisterBase B M) :=
    ⟨hv, fun j hj t ht => logSeriesProgram_scalarBound hz M B s rfl ho hd hm hb (by omega) ht⟩
  have embedded := localRun.relocate 9 false series_lookup (Or.inr hlive)
  rw [reset] at embedded
  have he := Option.some.inj (embedded.execution.symm.trans hu)
  simpa only [he] using embedded

private theorem bounded_grid_region (q : ℚ) (M B : ℕ) {a u : State ℚ}
    (hp : a.pc = 35) (ho : a.output = none) (hd : a.data 0 = q) (hm : a.index 0 = M)
    (hb : scalarBound B a) (hu : runExactly mantissaProgram a (7+13*M+2) = some u) :
    RegisterBoundedRun mantissaProgram a (7+13*M+2) u (10^13 * (12+4*(B+M+3))) := by
  let s := {a with pc := 0}
  have reset : stateAt 35 s = a := by cases a; simp_all [s, stateAt]
  obtain ⟨v, hv, _, _, _, _, _⟩ := grid_run_until_halt q M s rfl ho hd hm
  have localRun : RegisterBoundedRun dyadicGridProgram s (7+13*M+2) v
      (10^13 * (12+4*(B+M+3))) :=
    ⟨hv, fun j hj t ht => dyadicGridProgram_scalarBound q M B s rfl ho hd hm hb (by omega) ht⟩
  have embedded := localRun.relocate 35 true grid_lookup (Or.inl rfl)
  rw [reset] at embedded
  have he := Option.some.inj (embedded.execution.symm.trans hu)
  simpa only [he] using embedded

/-- Bound by a polynomial in the initial binary encoding bound and the
precision counter. Each `let` is the bound after a fixed program stage. -/
def mantissaRegisterBound (B k : ℕ) : ℕ :=
  let B₀ := 10^9 * (B+4)
  let B₁ := 10^9 * seriesRegisterBase B₀ (k+6)
  let B₂ := 10^5 * (B₁+4)
  let B₃ := 10^9 * seriesRegisterBase B₂ (k+6)
  let B₄ := 10^5 * (B₃+4)
  let B₅ := 10^13 * (12+4*(B₄+(k+2)+3))
  B₀ + B₁ + B₂ + B₃ + B₄ + B₅ + 10*(B₅+4)

private theorem mantissa_const_bits (d : ℕ) (r : ℚ) (h : Instr.const d r ∈ mantissaProgram) :
    ratBits r ≤ 4 := by
  let good : Instr → Bool
    | .const _ q => decide (ratBits q ≤ 4)
    | _ => true
  have hc : mantissaProgram.all good = true := by decide
  exact of_decide_eq_true (List.all_eq_true.mp hc (.const d r) h)

private theorem short_mantissa {a u : State ℚ} {n B : ℕ} (hb : scalarBound B a)
    (h : runExactly mantissaProgram a n = some u) :
    RegisterBoundedRun mantissaProgram a n u (10^n*(B+4)) :=
  RegisterBoundedRun.short (by omega) (fun d r hr => (mantissa_const_bits d r hr).trans (by omega))
    (fun j => (hb j).trans (by omega)) h

/-- Every register at every legal prefix of the fixed mantissa program, even
when entered with arbitrary bounded scratch memory, obeys the same polynomial
binary encoding bound. -/
theorem mantissaProgram_scalarBound {z : ℚ} (hz : 1 ≤ z) (k B : ℕ) (s : State ℚ)
    (hp : s.pc = 0) (ho : s.output = none) (hd : s.data 0 = z) (hm : s.index 0 = k)
    (hb : scalarBound B s) {n : ℕ} (hn : n ≤ 27*k+161) {v : State ℚ}
    (hv : runExactly mantissaProgram s n = some v) :
    scalarBound (mantissaRegisterBound B k) v := by
  let M := k+6
  let a := logTruncation z M
  let b := logTruncation (2 : ℚ) M
  have hb' : b ≠ 0 := by
    have H := two_thirds_le_logTruncation_two (M := M) (by dsimp [M]; omega)
    have hc := cast_logTruncation (2 : ℚ) M
    norm_num only [Rat.cast_ofNat] at hc
    rw [← hc] at H
    intro h
    change logTruncation (2 : ℚ) M = 0 at h
    rw [h] at H
    norm_num at H
  obtain ⟨u₀, e₀, pc₀, o₀, d₀, m₀, k₀, f₀, n₀, _⟩ := mantissa_setup z k s hp ho hd hm
  have R₀ := short_mantissa hb e₀
  obtain ⟨u₁, e₁, pc₁, o₁, d₁, _, k₁, f₁, n₁, m₁, _⟩ :=
    run_series_region z M hz u₀ pc₀ o₀ d₀ m₀
  have R₁ := bounded_series_region hz M _ pc₀ o₀ d₀ m₀ R₀.finalBound e₁
  obtain ⟨u₂, e₂, pc₂, o₂, d₂, s₂, m₂, k₂, f₂, n₂, _⟩ :=
    run_first_return u₁ k a pc₁ o₁ d₁ (k₁.trans k₀) (f₁.trans f₀) (n₁.trans n₀) (m₁.trans m₀)
  have R₂ := short_mantissa R₁.finalBound e₂
  obtain ⟨u₃, e₃, pc₃, o₃, d₃, s₃, k₃, f₃, n₃, _, _⟩ :=
    run_series_region 2 M (by norm_num) u₂ pc₂ o₂ d₂ m₂
  have R₃ := bounded_series_region (z := 2) (by norm_num) M _ pc₂ o₂ d₂ m₂ R₂.finalBound e₃
  obtain ⟨u₄, e₄, pc₄, o₄, d₄, m₄, _⟩ :=
    run_second_return u₃ k a b hb' pc₃ o₃ d₃ (s₃.trans s₂) (k₃.trans k₂) (f₃.trans f₂) (n₃.trans n₂)
  have R₄ := short_mantissa R₃.finalBound e₄
  obtain ⟨u₅, e₅, pc₅, o₅, _, _, _⟩ := run_grid_region (a/b) (k+2) u₄ pc₄ o₄ d₄ m₄
  have R₅ := bounded_grid_region (a/b) (k+2) _ pc₄ o₄ d₄ m₄ R₄.finalBound e₅
  let u₆ := {u₅ with output := some 0}
  have lastOp : mantissaProgram[59]? = some (.halt 0) := by decide
  have e₆ : runExactly mantissaProgram u₅ 1 = some u₆ := by
    simp [runExactly, step, pc₅, o₅, lastOp, execInstr, u₆]
  have R₆ := short_mantissa R₅.finalBound e₆
  have allRuns := (((((R₀.append R₁).append R₂).append R₃).append R₄).append R₅).append R₆
  have hlen : 9+(9+7*M+2)+5+(9+7*M+2)+5+(7+13*(k+2)+2)+1=27*k+161 := by
    dsimp [M]; omega
  exact allRuns.bound n (hlen ▸ hn) v hv

private theorem seriesRegisterBase_mono {b b' m m' : ℕ} (hb : b ≤ b') (hm : m ≤ m') :
    seriesRegisterBase b m ≤ seriesRegisterBase b' m' := by
  dsimp only [seriesRegisterBase]
  gcongr

attribute [local gcongr] seriesRegisterBase_mono

/-- A single cubic polynomial in input bits plus precision bounds the closed
register expression. Its coefficient is independent of the input and the precision. -/
theorem mantissaRegisterBound_le_polyBound (B k : ℕ) :
    mantissaRegisterBound B k ≤ RAM.polyBound (mantissaRegisterBound 1 1) 3 (B+k) := by
  let N := B+k+1
  have hb : B ≤ N := by dsimp [N]; omega
  have hk : k ≤ N := by dsimp [N]; omega
  have hpos : 0 < N := by dsimp [N]; omega
  have h0 : 1 ≤ N^3 := Nat.one_le_pow _ _ hpos
  have h1 : N ≤ N^3 := by
    simpa only [pow_one] using (Nat.pow_le_pow_right hpos (show 1 ≤ 3 by decide))
  have h2 : N^2 ≤ N^3 := Nat.pow_le_pow_right hpos (by decide)
  calc
    mantissaRegisterBound B k ≤ mantissaRegisterBound N N := by
      dsimp only [mantissaRegisterBound]
      gcongr
    _ ≤ mantissaRegisterBound 1 1 * N^3 := by
      unfold mantissaRegisterBound seriesRegisterBase
      ring_nf
      omega

/-- Accuracy, constructed bits, exact execution time and cubic rational register
bounds for a single run from the normalized mantissa input. -/
theorem mantissaProgram_spec {z : ℚ} (hz : 1 ≤ z) (hz' : z ≤ 2) (k : ℕ) :
    ∃ t : Fin (27*k+161+1) → State ℚ,
      Trace mantissaProgram (start [k] [z]) (27*k+161) t ∧
      (t (Fin.last _)).output = some 0 ∧
      (t (Fin.last _)).data 0 = ((mantissaGridNumerator z k).1 : ℚ) / 2^(k+2) ∧
      (∀ j < k+2, (t (Fin.last _)).data (8+j) =
        ((gridDigit (logTruncation z (k+6) / logTruncation (2 : ℚ) (k+6)) j).toNat : ℚ)) ∧
      |(((t (Fin.last _)).data 0 : ℚ) : ℝ) - Real.logb 2 (z : ℝ)| < (1/2 : ℝ)^k/2 ∧
      ∀ i, scalarBound (RAM.polyBound (mantissaRegisterBound 1 1) 3 (ratBits z+k)) (t i) := by
  obtain ⟨t, ht, hout, hv, hd, he⟩ := mantissaProgram_exec hz hz' k
  refine ⟨t, ht, hout, hv, hd, he, ?_⟩
  have hinit : scalarBound (ratBits z) (start [k] [z]) := by
    intro j
    cases j with
    | zero => exact le_rfl
    | succ j =>
      change ratBits 0 ≤ ratBits z
      rw [show ratBits 0 = 3 by decide]
      unfold ratBits; omega
  intro i a
  have hh := mantissaProgram_scalarBound hz k (ratBits z) (start [k] [z]) rfl rfl rfl rfl hinit
    (Nat.le_of_lt_succ i.isLt) (runExactly_of_trace ht i)
  exact (hh a).trans (mantissaRegisterBound_le_polyBound _ _)

end Compression
end LinearProgramming
end Optimization
end OAI
