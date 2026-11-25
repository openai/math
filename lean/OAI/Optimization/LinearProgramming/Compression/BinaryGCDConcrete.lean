import OAI.Optimization.LinearProgramming.Compression.BinaryGCDRAM
import OAI.Optimization.LinearProgramming.Compression.BinaryDivisionBlock

/-! # Executing the Euclidean algorithm on the fixed arithmetic RAM -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression

open RAM

/-- Euclid's loop instantiated with its actual scalar quotient/remainder program. -/
def euclidGCDBlock : Block := euclidLoopWith quotientRemainderBlock

/-- The caller can retain its original operands in scalar registers 6 and 7
while this block runs. Scalar 8 is preinitialized to zero. -/
theorem euclidGCDBlock_spec (m : Memory ℚ) (a b k : ℕ) {P : ℚ → Prop} (hm : m.AllData P)
    (ha : m.data 0 = (a : ℚ)) (hbv : m.data 1 = (b : ℚ)) (hk : m.index 0 = k)
    (hz : m.data 8 = 0) (haK : a < 2^k) (hbK : b < 2^k)
    (hP : ∀ v : ℕ, v ≤ 2^(2*k+2) → P (v : ℚ)) :
    ∃ (steps : ℕ) (z : Memory ℚ), Block.Eval (Memory.AllData P) euclidGCDBlock m steps z ∧
      steps ≤ 2*k * (16*k+17) + 1 ∧ z.data 0 = (a.gcd b : ℕ) ∧ z.data 1 = 0 ∧
      (∀ i, 6 ≤ i → z.data i = m.data i) ∧ (∀ i, i ≠ 1 → z.index i = m.index i) := by
  apply euclidLoopWith_spec _ m a b hm ha hbv hk hz haK hbK
  constructor
  intro s v w hmem hv hw hsk hvK hwp hwK
  obtain ⟨n, z, he, ht, hr, hfix, _hq, hdata, hindex⟩ :=
    quotientRemainderBlock_spec s v w k hmem hv hw hsk hvK hwp hwK hP
  exact ⟨n, z, he, ht, hr, hfix, hdata, hindex⟩

/-- Complete program, taking two scalar naturals and their constructed bit-length
bound in the first address cell. -/
def euclidGCDProgram : Program := euclidGCDBlock.compile 0 ++ [.halt 0]

/-- Standalone terminated trace of the assembled program. Both the instructions
and all intermediate reduced scalar encodings have explicit bit-polynomial bounds. -/
theorem euclidGCDProgram_trace (a b k : ℕ) (ha : a < 2^k) (hb : b < 2^k) :
    ∃ (steps : ℕ) (t : Fin (steps+1) → State ℚ), steps ≤ 2*k*(16*k+17)+2 ∧
      Trace euclidGCDProgram (start [k] [(a : ℚ), (b : ℚ)]) steps t ∧
      (t (Fin.last steps)).output = some 0 ∧ (t (Fin.last steps)).data 0 = (a.gcd b : ℕ) ∧
      ∀ i, scalarBound (2*k+5) (t i) := by
  let m := (start [k] [(a : ℚ), (b : ℚ)]).memory
  let P := fun q : ℚ => ratBits q ≤ 2*k+5
  have hP (v : ℕ) (hv : v ≤ 2^(2*k+2)) : P (v : ℚ) := by
    have hmono : v.log2 ≤ (2^(2*k+2)).log2 := by
      simpa only [Nat.log2_eq_log_two] using Nat.log_mono_right (b := 2) hv
    have hlog : v.log2 ≤ 2*k+2 := hmono.trans_eq Nat.log2_two_pow
    simp only [P, ratBits, Rat.num_natCast, Int.natAbs_natCast, Rat.den_natCast,
      show Nat.log2 1 = 0 from rfl, Nat.add_zero]
    omega
  have hp : 2^k ≤ 2^(2*k+2) := Nat.pow_le_pow_right (by decide) (by omega)
  have hm : m.AllData P := by
    intro i
    match i with
    | 0 => exact hP a (ha.le.trans hp)
    | 1 => exact hP b (hb.le.trans hp)
    | _+2 => exact hP 0 (Nat.zero_le _)
  obtain ⟨steps, z, he, ht, hg, _⟩ :=
    euclidGCDBlock_spec m a b k hm rfl rfl rfl rfl ha hb hP
  obtain ⟨t, htrace, hout, hmem, hsafe⟩ := he.halted_trace (tag := 0)
  refine ⟨steps+1, t, by omega, htrace, hout, ?_, hsafe⟩
  exact (congrArg (fun s : Memory ℚ => s.data 0) hmem).trans hg

end Compression
end LinearProgramming
end Optimization
end OAI
