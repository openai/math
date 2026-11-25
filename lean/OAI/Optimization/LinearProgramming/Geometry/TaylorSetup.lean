import OAI.Optimization.LinearProgramming.Geometry.TaylorRAM
import OAI.Optimization.LinearProgramming.RAM.Loops

/-! Composable logarithm and exponential blocks for the approximation routine. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Geometry
namespace TaylorRAM

open RAM

private abbrev all (W : ℕ) (m : Memory ℚ) := ∀ j, ratBits (m.data j) ≤ W

private theorem safe_write {m : Memory ℚ} {W : ℕ} (hm : all W m) (i : ℕ) (q : ℚ)
    (h : ratBits q ≤ W) : all W (m.putData i q) := by
  intro j
  by_cases e : j = i
  · simpa [e] using h
  · simpa [e] using hm j

private theorem const_op (i : ℕ) (q : ℚ) {m : Memory ℚ} {W : ℕ} (hm : all W m)
    (h : ratBits q ≤ W) : Block.Eval (all W) (.op (.const i q)) m 1 (m.putData i q) :=
  .op hm (safe_write hm i q h) (fun _ => rfl)

/-- Prepare all accumulators except the preloaded factor (scalar register 2)
and term count (address register 1). Only fixed rational constants are used
in concrete instances. -/
def seed (term num den numStep denStep : ℚ) : Block := Block.straight
  [.const 0 0, .const 1 term, .const 3 num, .const 4 den, .const 5 numStep,
   .const 6 denStep, .addrConst 0 0]

private theorem run_seed (r : Recurrence) (M W : ℕ) (m : Memory ℚ)
    (hM : m.index 1 = M) (hx : m.data 2 = r.factor) (hm : all W m)
    (hr : ∀ i ≤ M, ∀ q ∈ registers r i, ratBits q ≤ W) :
    ∃ m', Block.Eval (all W) (seed (r.term 0) (r.numerator 0) (r.denominator 0)
      r.numStep r.denStep) m 7 m' ∧ AtHead r M 0 m' ∧ Frame m m' := by
  let m₁ := m.putData 0 0
  let m₂ := m₁.putData 1 (r.term 0)
  let m₃ := m₂.putData 3 (r.numerator 0)
  let m₄ := m₃.putData 4 (r.denominator 0)
  let m₅ := m₄.putData 5 r.numStep
  let m₆ := m₅.putData 6 r.denStep
  let m₇ := m₆.putIndex 0 0
  have e₁ : Block.Eval (all W) (.op (.const 0 0)) m 1 m₁ :=
    const_op _ _ hm (hr 0 (Nat.zero_le _) _ (by simp [registers]))
  have e₂ : Block.Eval (all W) (.op (.const 1 (r.term 0))) m₁ 1 m₂ :=
    const_op _ _ e₁.safe_end (hr 0 (Nat.zero_le _) _ (by simp [registers]))
  have e₃ : Block.Eval (all W) (.op (.const 3 (r.numerator 0))) m₂ 1 m₃ :=
    const_op _ _ e₂.safe_end (hr 0 (Nat.zero_le _) _ (by simp [registers]))
  have e₄ : Block.Eval (all W) (.op (.const 4 (r.denominator 0))) m₃ 1 m₄ :=
    const_op _ _ e₃.safe_end (hr 0 (Nat.zero_le _) _ (by simp [registers]))
  have e₅ : Block.Eval (all W) (.op (.const 5 r.numStep)) m₄ 1 m₅ :=
    const_op _ _ e₄.safe_end (hr 0 (Nat.zero_le _) _ (by simp [registers]))
  have e₆ : Block.Eval (all W) (.op (.const 6 r.denStep)) m₅ 1 m₆ :=
    const_op _ _ e₅.safe_end (hr 0 (Nat.zero_le _) _ (by simp [registers]))
  have e₇ : Block.Eval (all W) (.op (.addrConst 0 0)) m₆ 1 m₇ :=
    .op e₆.safe_end e₆.safe_end (fun _ => rfl)
  refine ⟨m₇, .seq e₁ (.seq e₂ (.seq e₃ (.seq e₄ (.seq e₅ (.seq e₆
    (.seq e₇ (.skip e₇.safe_end))))))), ?_, ?_⟩
  · constructor <;> simp [m₇,m₆,m₅,m₄,m₃,m₂,m₁,hM,hx,Recurrence.prefix]
  · constructor
    · intro j hj
      have h₀ : j ≠ 0 := by omega
      have h₁ : j ≠ 1 := by omega
      have h₃ : j ≠ 3 := by omega
      have h₄ : j ≠ 4 := by omega
      have h₅ : j ≠ 5 := by omega
      have h₆ : j ≠ 6 := by omega
      simp [m₇,m₆,m₅,m₄,m₃,m₂,m₁,h₀,h₁,h₃,h₄,h₅,h₆]
    · intro j hj
      simp [m₇,m₆,m₅,m₄,m₃,m₂,m₁,hj]

/-- Fixed program fragment for the ordinary Taylor series; its argument is
already in scalar 2 and its term count in address 1. -/
def expBlock : Block := .seq (seed 1 1 1 0 1) kernel

/-- Fixed program fragment for the odd log-two series; the input term count is
in address 1 and the multiplier is embedded as the rational constant `1/9`. -/
def logBlock : Block := .seq (.op (.const 2 (1/9)))
  (.seq (seed (2/3) 1 3 2 2) kernel)

private theorem Frame.trans {m n p : Memory ℚ} (a : Frame m n) (b : Frame n p) : Frame m p :=
  ⟨fun j hj => (b.data j hj).trans (a.data j hj), fun j hj => (b.index j hj).trans (a.index j hj)⟩

theorem run_expBlock (m : Memory ℚ) (M W : ℕ) (x : ℚ) (hM : m.index 1 = M)
    (hx : m.data 2 = x) (hx₀ : 0 ≤ x) (hx₁ : x ≤ 1) (hm : ∀ j, ratBits (m.data j) ≤ W)
    (hW : 100*(M + ratBits x + 10)^2 ≤ W) :
    ∃ n, Block.Eval (fun v => ∀ j, ratBits (v.data j) ≤ W) expBlock m (9*M+8) n ∧
      n.data 0 = expTruncation x M ∧ Frame m n := by
  let r := expSeries x
  have hP : ∀ i ≤ M, ∀ q ∈ registers r i, ratBits q ≤ W :=
    fun i hi q hq => (exp_register_bits hx₀ hx₁ hi q hq).trans hW
  obtain ⟨m', hs, hh, hf⟩ := run_seed r M W m hM hx hm hP
  obtain ⟨n, h, out, hf'⟩ := run_kernel (Nat.zero_le _) hh hs.safe_end hP
  have hseed : seed (r.term 0) (r.numerator 0) (r.denominator 0) r.numStep r.denStep =
      seed 1 1 1 0 1 := by simp [r, expSeries]
  rw [hseed] at hs
  refine ⟨n, ?_, out.sum, hf.trans hf'⟩
  simpa only [expBlock, Nat.sub_zero, show 7+(9*M+1) = 9*M+8 by omega] using
    (Block.Eval.seq hs h)

theorem run_logBlock (m : Memory ℚ) (M W : ℕ) (hM : m.index 1 = M)
    (hm : ∀ j, ratBits (m.data j) ≤ W) (hW : 100*(M+10)^2 ≤ W) :
    ∃ n, Block.Eval (fun v => ∀ j, ratBits (v.data j) ≤ W) logBlock m (9*M+9) n ∧
      n.data 0 = Compression.logTruncation 2 M ∧ Frame m n := by
  have hP : ∀ i ≤ M, ∀ q ∈ registers logTwoSeries i, ratBits q ≤ W :=
    fun i hi q hq => (log_register_bits hi q hq).trans hW
  have hc : ratBits (1/9) ≤ W := hP 0 (Nat.zero_le _) _ (by simp [registers,logTwoSeries])
  let m₀ := m.putData 2 (1/9)
  have h₀ := const_op 2 (1/9) hm hc
  have hframe : Frame m m₀ := ⟨fun j hj => by simp [m₀, show j ≠ 2 by omega], fun _ _ => rfl⟩
  obtain ⟨m', hs, hh, hf⟩ := run_seed logTwoSeries M W m₀ hM (by simp [m₀,logTwoSeries])
    h₀.safe_end hP
  obtain ⟨n, h, out, hf'⟩ := run_kernel (Nat.zero_le _) hh hs.safe_end hP
  have hseed : seed (logTwoSeries.term 0) (logTwoSeries.numerator 0)
      (logTwoSeries.denominator 0) logTwoSeries.numStep logTwoSeries.denStep =
      seed (2/3) 1 3 2 2 := by norm_num [logTwoSeries]
  rw [hseed] at hs
  refine ⟨n, ?_, out.sum.trans (logTwoSeries_prefix M), (hframe.trans hf).trans hf'⟩
  simpa only [logBlock, Nat.sub_zero, show 1+(7+(9*M+1)) = 9*M+9 by omega]
    using (Block.Eval.seq h₀ (.seq hs h))

end TaylorRAM
end Geometry
end LinearProgramming
end Optimization
end OAI
