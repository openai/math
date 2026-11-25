import OAI.Optimization.LinearProgramming.OracleSpec.Arithmetic
import OAI.Optimization.LinearProgramming.PriceGame.Experts
import OAI.Optimization.LinearProgramming.PriceGame.VertexEncoding

/-! # Recover the original coordinate of a mixed-radix vertex on the bit machine

The shift iterates at most the encoded address length, even for arbitrarily large supplied
shift counts. Each iteration consumes the low address bit and decrements the count.
-/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Learning
namespace BitMachine

open ExactQuantumFactoring.BitStackProgram States.Mass

/-- The radix-two factor on each child is its new sign bit. -/
theorem root_address (N : ℕ) (k : ℕ) (i : Vertex N k) :
    ((vertexEquivFin N k i).val >>> k) = (rootVertex N k i).val := by
  induction k with
  | zero => rfl
  | succ k ih =>
    obtain ⟨i,b⟩ := i
    have hb := (finTwoEquiv.symm b).isLt
    have hv : (vertexEquivFin N (k+1) (i,b)).val =
        (finTwoEquiv.symm b).val + 2 * (vertexEquivFin N k i).val := rfl
    rw [hv]
    change _ = (rootVertex N k i).val
    rw [Nat.add_comm k 1, Nat.shiftRight_add]
    have hhalf : ((finTwoEquiv.symm b).val + 2*(vertexEquivFin N k i).val) >>> 1 =
        (vertexEquivFin N k i).val := by
      rw [Nat.shiftRight_eq_div_pow,pow_one]; omega
    rw [hhalf]
    exact ih i

private noncomputable def halfP : Procedure Nat.bits Nat.bits Nat.div2 :=
  (Procedure.tail.precompose Nat.bits).result (fun n => (Nat.div2_bits_eq_tail n).symm)

private def shiftStep (x : ℕ × ℕ) : ℕ × ℕ :=
  if x.2 = 0 then x else (x.1.div2,x.2 - 1)

private theorem iterate_shiftStep (j m k : ℕ) :
    (shiftStep^[j]) (m,k) = (m >>> min j k, k - j) := by
  induction j generalizing m k with
  | zero => simp
  | succ j ih =>
    rw [Function.iterate_succ_apply]
    cases k with
    | zero => simp [shiftStep,ih]
    | succ k =>
      simp only [shiftStep,Nat.succ_ne_zero,ite_false,Nat.add_one_sub_one,ih]
      congr 1
      · rw [Nat.succ_min_succ]
        change m.div2 >>> min j k = m >>> (min j k + 1)
        rw [Nat.add_comm (min j k) 1, Nat.shiftRight_add]
        rfl
      · omega

private noncomputable def shiftStepP : Procedure (prodCode Nat.bits Nat.bits)
    (prodCode Nat.bits Nat.bits) shiftStep := by
  let e := prodCode Nat.bits Nat.bits
  let m := Procedure.first Nat.bits Nat.bits
  let k := Procedure.second Nat.bits Nat.bits
  exact (Procedure.conditional (Procedure.binaryZero.comp k) (Procedure.identity e)
    ((halfP.comp m).pair (Procedure.binarySub.comp (k.pair (Procedure.constant e Nat.bits 1))))).congrFun
    (by intro x; simp [shiftStep])

/-- True binary program for shifting an address to its root. The second input is a binary
integer; the implementation never expands that integer to an unbounded unary counter. -/
noncomputable def rootAddressP : Procedure (prodCode Nat.bits Nat.bits) Nat.bits
    (fun x : ℕ × ℕ => x.1 >>> x.2) := by
  let e := prodCode Nat.bits Nat.bits
  let rep := shiftStepP.iterate Polynomial.X (by
    intro n x j _
    rcases x with ⟨m,k⟩
    rw [iterate_shiftStep]
    have ha := bits_length_mono (show m >>> min j k ≤ m by rw [Nat.shiftRight_eq_div_pow]; exact Nat.div_le_self _ _)
    have hb := bits_length_mono (Nat.sub_le k j)
    simp only [prodCode,pairBits_length,Polynomial.eval_X]
    omega)
  let m := Procedure.first Nat.bits Nat.bits
  let width := (Procedure.length.precompose Nat.bits).comp m
  apply (m.comp (rep.comp (width.pair (Procedure.identity e)))).congrFun
  rintro ⟨m,k⟩
  change ((shiftStep^[m.bits.length]) (m,k)).1 = m >>> k
  rw [iterate_shiftStep]
  by_cases hk : k ≤ m.bits.length
  · simp [Nat.min_eq_right hk]
  · have hm := Nat.lt_size_self m
    rw [← Nat.size_eq_bits_len] at hm
    have hmk : m < 2^k := hm.trans_le (Nat.pow_le_pow_right (by decide) (by omega))
    simp [Nat.min_eq_left (by omega : m.bits.length ≤ k), Nat.shiftRight_eq_div_pow, Nat.div_eq_of_lt hm,
      Nat.div_eq_of_lt hmk]

end BitMachine
end Learning
end PriceGame
end LinearProgramming
end Optimization
end OAI
