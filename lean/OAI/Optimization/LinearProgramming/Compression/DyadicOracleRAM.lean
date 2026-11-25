import OAI.Optimization.LinearProgramming.Lattice.Bisection
import OAI.Optimization.LinearProgramming.RAM.Array

/-! ## Costed RAM execution of dyadic bisection with a sign-query subroutine

Scalar register 0 holds the numerator and register 1 the denominator. The
callee returns +1 for a nonnegative query and -1 otherwise in register 2.
The address bank holds the precision in register 0 and the iteration in
register 1. The caller controls the layout of the form and its input buffers.
-/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression
namespace DyadicRAM

open RAM OAI.Optimization.LinearProgramming.Lattice

/-- These are the only private writes made by the bisection driver. -/
structure Stable (frame : Memory ℚ → Prop) : Prop where
  scalar : ∀ m, frame m → ∀ r ≤ 1, ∀ v, frame (m.putData r v)
  counter : ∀ m, frame m → ∀ v, frame (m.putIndex 1 v)

/-- Register values before the query for the next binary digit. -/
structure At {p : ℕ} (oracle : (Fin p → ℤ) → Bool) (a b : Fin p → ℤ)
    (precision : ℕ) (P : ℚ → Prop) (frame : Memory ℚ → Prop) (j : ℕ) (m : Memory ℚ) : Prop where
  safe : m.AllData P
  inputs : frame m
  limit : m.index 0 = precision
  cursor : m.index 1 = j
  numerator : m.data 0 = ((dyadicSearch oracle a b j).numerator : ℚ)
  denominator : m.data 1 = ((2 : ℤ)^j : ℚ)

def replyDigit {p : ℕ} (oracle : (Fin p → ℤ) → Bool) (a b : Fin p → ℤ) (j : ℕ) : ℤ :=
  if oracle (dyadicQuery a b j (dyadicSearch oracle a b j).numerator) then 1 else -1

/-- A callee must run on the actual input row of this iteration and return
its signed digit, preserving the caller's active state. -/
def Answers {p : ℕ} (call : Block) (oracle : (Fin p → ℤ) → Bool) (a b : Fin p → ℤ)
    (k B : ℕ) (P : ℚ → Prop) (frame : Memory ℚ → Prop) : Prop :=
  ∀ j < k, ∀ m, At oracle a b k P frame j m →
    ∃ t time, time ≤ B ∧ Block.Eval (Memory.AllData P) call m time t ∧
      At oracle a b k P frame j t ∧ t.data 2 = (replyDigit oracle a b j : ℚ)

def advance : Block :=
  .straight [.add 0 0 0, .add 0 0 2, .add 1 1 1]

/-- The same block is used for every dimension and precision. -/
def searchBlock (call : Block) : Block :=
  .seq (.straight [.const 0 0, .const 1 1])
    (.forRange 1 0 (.seq call advance))

theorem advance_eval {p k j : ℕ} (oracle : (Fin p → ℤ) → Bool) (a b : Fin p → ℤ)
    (hj : j < k) {P : ℚ → Prop} (hP : ∀ n : ℤ, |n| ≤ 2^k → P n)
    {frame : Memory ℚ → Prop} (hf : Stable frame) {m : Memory ℚ}
    (hm : At oracle a b k P frame j m) (hbit : m.data 2 = (replyDigit oracle a b j : ℚ)) :
    ∃ t, Block.Eval (Memory.AllData P) advance m 3 t ∧
      At oracle a b k P frame (j+1) (t.putIndex 1 (t.index 1+1)) := by
  let n := (dyadicSearch oracle a b j).numerator
  let n' := (dyadicSearch oracle a b (j+1)).numerator
  let x : ℤ := 2*n
  let y : ℤ := 2^(j+1)
  let t₁ := m.putData 0 (x : ℚ)
  let t₂ := t₁.putData 0 (n' : ℚ)
  let t₃ := t₂.putData 1 (y : ℚ)
  have hpow : (2 : ℤ)^(j+1) ≤ 2^k := pow_le_pow_right₀ (by decide) hj
  have hx : |x| ≤ 2^k := by
    apply le_trans _ hpow
    have hl := (dyadicSearch_numerator_lt oracle a b j).le
    dsimp [x,n]
    rw [abs_mul, pow_succ, abs_of_pos (by decide : (0 : ℤ) < 2)]
    linarith
  have hn : |n'| ≤ 2^k := (dyadicSearch_numerator_lt oracle a b (j+1)).le.trans hpow
  have hy : |y| ≤ 2^k := by simpa [y, abs_of_nonneg (pow_nonneg (by decide : (0:ℤ) ≤ 2) (j+1))] using hpow
  have s₁ : t₁.AllData P := hm.safe.putData 0 (hP x hx)
  have s₂ : t₂.AllData P := s₁.putData 0 (hP n' hn)
  have s₃ : t₃.AllData P := s₂.putData 1 (hP y hy)
  have v₁ : m.data 0 + m.data 0 = (x : ℚ) := by simp [hm.numerator, x, n, two_mul]
  have v₂ : t₁.data 0 + t₁.data 2 = (n' : ℚ) := by
    simp [t₁, x, n, n', dyadicSearch, hbit, replyDigit, Int.cast_ite]
  have v₃ : t₂.data 1 + t₂.data 1 = (y : ℚ) := by
    simp [t₂, t₁, y, hm.denominator, pow_succ, mul_two]
  have e₁ : Block.Eval (Memory.AllData P) (.op (.add 0 0 0)) m 1 t₁ := by
    simpa only [v₁] using Block.Eval.op_add m 0 0 0 hm.safe (v₁ ▸ s₁)
  have e₂ : Block.Eval (Memory.AllData P) (.op (.add 0 0 2)) t₁ 1 t₂ := by
    simpa only [v₂] using Block.Eval.op_add t₁ 0 0 2 s₁ (v₂ ▸ s₂)
  have e₃ : Block.Eval (Memory.AllData P) (.op (.add 1 1 1)) t₂ 1 t₃ := by
    simpa only [v₃] using Block.Eval.op_add t₂ 1 1 1 s₂ (v₃ ▸ s₃)
  have ff₁ : frame t₁ := hf.scalar m hm.inputs 0 (by decide) _
  have ff₂ : frame t₂ := hf.scalar t₁ ff₁ 0 (by decide) _
  have ff₃ : frame t₃ := hf.scalar t₂ ff₂ 1 (by decide) _
  refine ⟨t₃, .seq e₁ (.seq e₂ (.seq e₃ (.skip s₃))), ?_⟩
  constructor
  · exact s₃.putIndex 1 _
  · exact hf.counter t₃ ff₃ _
  · simpa [t₃,t₂,t₁] using hm.limit
  · simp [t₃,t₂,t₁,hm.cursor]
  · simp [t₃,t₂,n']
  · simp [t₃,y]

/-- The trace executes the loop from Appendix A, including the positive choice
at a zero comparison, and returns its exact numerator. The operation bound counts
every address update, signed-digit addition, back jump and guard. -/
theorem searchBlock_eval {p : ℕ} (oracle : (Fin p → ℤ) → Bool) (a b : Fin p → ℤ)
    (k B : ℕ) (P : ℚ → Prop) (hP : ∀ n : ℤ, |n| ≤ 2^k → P n)
    (frame : Memory ℚ → Prop) (hf : Stable frame) (call : Block)
    (hcall : Answers call oracle a b k B P frame) (m : Memory ℚ)
    (hm : m.AllData P) (hframe : frame m) (hprec : m.index 0 = k) :
    ∃ t time, time ≤ k*(B+6)+4 ∧ Block.Eval (Memory.AllData P) (searchBlock call) m time t ∧
      At oracle a b k P frame k t := by
  let m₀ := m.putData 0 0
  let m₁ := m₀.putData 1 1
  have hp₀ : P 0 := by simpa using hP 0 (by positivity)
  have hp₁ : P 1 := by simpa using hP 1 (by simp [one_le_pow₀ (by decide : (1:ℤ) ≤ 2)])
  have s₀ : m₀.AllData P := hm.putData 0 hp₀
  have s₁ : m₁.AllData P := s₀.putData 1 hp₁
  have f₀ : frame m₀ := hf.scalar m hframe 0 (by decide) 0
  have f₁ : frame m₁ := hf.scalar m₀ f₀ 1 (by decide) 1
  have init : At oracle a b k P frame 0 (m₁.putIndex 1 0) := by
    constructor
    · exact s₁.putIndex 1 _
    · exact hf.counter m₁ f₁ _
    · simpa [m₁,m₀] using hprec
    · simp
    · simp [m₁,m₀,dyadicSearch]
    · simp [m₁]
  obtain ⟨t,time,ht,he,hs⟩ := Block.Eval.forRange_invariant (body := .seq call advance)
    (safe := Memory.AllData P) 1 0 k (B+3) (At oracle a b k P frame) m₁ s₁ init
    (fun _ _ h => ⟨h.safe,h.cursor,h.limit⟩) (fun j hj s h => by
      obtain ⟨u,c,hc,ec,hu,hd⟩ := hcall j hj s h
      obtain ⟨t,ea,ht⟩ := advance_eval oracle a b hj hP hf hu hd
      exact ⟨t,c+3,by omega,ec.seq ea,ht⟩)
  have e₀ := Block.Eval.op_const m 0 0 hm s₀
  have e₁ := Block.Eval.op_const m₀ 1 1 s₀ s₁
  refine ⟨t,2+time,?_, (e₀.seq (e₁.seq (.skip s₁))).seq he, hs⟩
  rw [show B+3+3=B+6 by omega] at ht
  omega

end DyadicRAM
end Compression
end LinearProgramming
end Optimization
end OAI
