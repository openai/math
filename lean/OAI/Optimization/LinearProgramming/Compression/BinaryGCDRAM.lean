import OAI.Optimization.LinearProgramming.Compression.BinaryGCD
import OAI.Optimization.LinearProgramming.RAM.Array
import Mathlib.Tactic

/-! # Calling a quotient/remainder block from Euclid's algorithm

The loop rotates the dividend and remainder in three copies. All cells past
the divider's scratch area survive every iteration, including the caller’s
original integers and the zero used in the loop guard. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression

open RAM

/-- Move (remainder, previous divisor) into the order required at the next
Euclidean step. The third cell is scratch. -/
private def euclidRotate : Block :=
  .seq (.op (.copy 2 0)) (.seq (.op (.copy 0 1)) (.op (.copy 1 2)))

/-- The guard in scalar register 8 is zero and register 1 is the current divisor. -/
def euclidLoopWith (divide : Block) : Block :=
  .loop (.scalarLT 8 1) (.seq divide euclidRotate)

/-- A modular premise giving the exact effects needed from the division block. -/
structure EuclidRAMDivider (divide : Block) (P : ℚ → Prop) (k : ℕ) : Prop where
  eval (m : Memory ℚ) (a b : ℕ) (hm : m.AllData P)
      (ha : m.data 0 = (a : ℚ)) (hbv : m.data 1 = (b : ℚ)) (hk : m.index 0 = k)
      (haK : a < 2^k) (hb : 0 < b) (hbK : b ≤ 2^k) :
      ∃ (n : ℕ) (z : Memory ℚ), Block.Eval (Memory.AllData P) divide m n z ∧ n ≤ 16*k+12 ∧
        z.data 0 = (a % b : ℕ) ∧ z.data 1 = (b : ℚ) ∧
        (∀ i, 6 ≤ i → z.data i = m.data i) ∧ (∀ i, i ≠ 1 → z.index i = m.index i)

private theorem rotate_spec (m : Memory ℚ) {P : ℚ → Prop} (hm : m.AllData P) :
    ∃ z, Block.Eval (Memory.AllData P) euclidRotate m 3 z ∧
      z.data 0 = m.data 1 ∧ z.data 1 = m.data 0 ∧
      (∀ i, 3 ≤ i → z.data i = m.data i) ∧ z.index = m.index := by
  let m₁ := m.putData 2 (m.data 0)
  let m₂ := m₁.putData 0 (m₁.data 1)
  let m₃ := m₂.putData 1 (m₂.data 2)
  have e₁ := Block.Eval.op_copy m 2 0 hm (hm.putData 2 (hm 0))
  have h₁ : m₁.AllData P := e₁.safe_end
  have e₂ := Block.Eval.op_copy m₁ 0 1 h₁ (h₁.putData 0 (h₁ 1))
  have h₂ : m₂.AllData P := e₂.safe_end
  have e₃ := Block.Eval.op_copy m₂ 1 2 h₂ (h₂.putData 1 (h₂ 2))
  refine ⟨m₃, e₁.seq (e₂.seq e₃), ?_, ?_, ?_, rfl⟩
  · simp [m₃, m₂, m₁]
  · simp [m₃, m₂, m₁]
  · intro i hi
    simp [m₃, m₂, m₁, show i ≠ 0 by omega, show i ≠ 1 by omega, show i ≠ 2 by omega]

private theorem euclidLoop_trace {divide : Block} {P : ℚ → Prop} {k a b g calls}
    (D : EuclidRAMDivider divide P k) (t : EuclidTrace natEuclidDivider a b g calls)
    (m : Memory ℚ) (hm : m.AllData P) (ha : m.data 0 = (a : ℚ)) (hbv : m.data 1 = (b : ℚ))
    (hk : m.index 0 = k) (hz : m.data 8 = 0) (haK : a < 2^k) (hbK : b < 2^k) :
    ∃ (steps : ℕ) (z : Memory ℚ), Block.Eval (Memory.AllData P) (euclidLoopWith divide) m steps z ∧
      steps ≤ calls.length * (16*k+17) + 1 ∧ z.data 0 = (g : ℚ) ∧ z.data 1 = 0 ∧
      (∀ i, 6 ≤ i → z.data i = m.data i) ∧ (∀ i, i ≠ 1 → z.index i = m.index i) := by
  induction t generalizing m with
  | done a =>
    refine ⟨1, m, .loopFalse ?_ hm, by simp, ha, by simpa using hbv, fun _ _ => rfl, fun _ _ => rfl⟩
    simp [Cond.test, hz, hbv]
  | @next a b g calls hb tail ih =>
    obtain ⟨n, z, ez, hn, hr, hzb, hzframe, hzindex⟩ := D.eval m a b hm ha hbv hk haK hb hbK.le
    obtain ⟨m', eswap, h0, h1, hsframe, hsindex⟩ := rotate_spec z ez.safe_end
    have frame (i : ℕ) (hi : 6 ≤ i) : m'.data i = m.data i :=
      (hsframe i (by omega)).trans (hzframe i hi)
    have index (i : ℕ) (hi : i ≠ 1) : m'.index i = m.index i := (congrFun hsindex i).trans (hzindex i hi)
    obtain ⟨n', z', ez', hn', hzg, hz0, hzf, hzi⟩ := ih m' eswap.safe_end (h0.trans hzb)
      (h1.trans hr) ((index 0 (by decide)).trans hk) ((frame 8 (by decide)).trans hz)
      hbK ((Nat.mod_lt a hb).trans hbK)
    refine ⟨1+(n+3)+1+n', z', .loopTrue ?_ (ez.seq eswap) ez', ?_, hzg, hz0,
      fun i hi => (hzf i hi).trans (frame i hi), fun i hi => (hzi i hi).trans (index i hi)⟩
    · simp [Cond.test, hz, hbv, hb]
    · rw [List.length_cons, Nat.succ_mul calls.length (16*k+17)]
      omega

/-- The fixed loop performs at most `2*k` iterations. The bound includes the
loop's conditional branches, backwards jumps, copies, and the division calls. -/
theorem euclidLoopWith_spec {divide : Block} {P : ℚ → Prop} {k : ℕ}
    (D : EuclidRAMDivider divide P k) (m : Memory ℚ) (a b : ℕ) (hm : m.AllData P)
    (ha : m.data 0 = (a : ℚ)) (hbv : m.data 1 = (b : ℚ)) (hk : m.index 0 = k)
    (hz : m.data 8 = 0) (haK : a < 2^k) (hbK : b < 2^k) :
    ∃ (steps : ℕ) (z : Memory ℚ), Block.Eval (Memory.AllData P) (euclidLoopWith divide) m steps z ∧
      steps ≤ 2*k * (16*k+17) + 1 ∧ z.data 0 = (a.gcd b : ℕ) ∧ z.data 1 = 0 ∧
      (∀ i, 6 ≤ i → z.data i = m.data i) ∧ (∀ i, i ≠ 1 → z.index i = m.index i) := by
  let t := euclidRun_trace natEuclidDivider a b
  obtain ⟨steps, z, he, hsteps, hg, hzero, hd, hi⟩ := euclidLoop_trace D t m hm ha hbv hk hz haK hbK
  exact ⟨steps, z, he, hsteps.trans (Nat.add_le_add_right
    (Nat.mul_le_mul_right _ (t.length_le_twice_bits k hbK)) 1),
    t.result ▸ hg, hzero, hd, hi⟩

end Compression
end LinearProgramming
end Optimization
end OAI
