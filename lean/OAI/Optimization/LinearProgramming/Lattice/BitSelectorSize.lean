import OAI.Optimization.LinearProgramming.Lattice.BitSelectorConstants
import OAI.Optimization.LinearProgramming.Lattice.ShortSelectorSize

/-! The typed word accepted by the selector is polynomial in the public rounding parameters. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Lattice
namespace Bit
namespace Selector
open ExactQuantumFactoring.BitStackProgram
open ExactQuantumFactoring.BitStackProgram.Procedure

private theorem signedSize (z : ℤ) : (intCode z).length = z.natAbs.size+3 := by
  simp [intCode,intData,prodCode,pairBits_length,boolCode,Nat.size_eq_bits_len]
  omega

theorem rationalSize (q : ℚ) : (ratCode q).length = 2*q.num.natAbs.size+q.den.size+7 := by
  simp [ratCode,prodCode,pairBits_length,signedSize,Nat.size_eq_bits_len]
  omega

theorem input_length {p : ℕ} (M k : ℕ) (u : Fin p → ℚ)
    (hu : ∀ i, (u i).num.natAbs.size ≤ k+1 ∧ (u i).den.size ≤ k+1) :
    (inputCode (M,List.ofFn u)).length ≤ 2*M.size+p*(6*k+22)+2 := by
  have he (i : Fin p) (_ : i∈List.finRange p) : (ratCode (u i)).length ≤ 3*k+10 := by
    rw [rationalSize]
    have h := hu i
    omega
  have hl : (vectorCode (List.ofFn u)).length ≤ p*(6*k+22)+1 := by
    unfold vectorCode
    rw [List.ofFn_eq_map]
    have h := listCode_length_map_bound ratCode u (List.finRange p) (3*k+10) he
    simpa only [List.length_finRange,show 2*(3*k+10)+2=6*k+22 by omega] using h
  simp only [inputCode,prodCode,pairBits_length,Nat.size_eq_bits_len]
  omega

noncomputable def normalizedInputBound : Polynomial ℕ :=
  2*Polynomial.X+Polynomial.X*(30*Polynomial.X^2+22)+2

/-- The bound applies to every possible answer sequence, even one inconsistent with any
real vector. The original rational matrix does not appear in its polynomial parameter. -/
theorem normalized_input_length {p n : ℕ} (M : ℕ) (oracle : (Fin n → ℤ) → Bool)
    (P : Fin p → Fin n → ℚ) :
    (inputCode (M,List.ofFn (normalizedRowApprox oracle P (searchPrecision p M)))).length ≤
      normalizedInputBound.eval (p+M.size+12) := by
  let N := p+M.size+12
  have hp : p ≤ N := by dsimp [N]; omega
  have hp2 : p+2 ≤ N := by dsimp [N]; omega
  have hM : M.size ≤ N := by dsimp [N]; omega
  have hexp : precisionExponent p M ≤ 5*N := by dsimp [precisionExponent,N]; omega
  have hk : searchPrecision p M ≤ 5*N^2 := by
    unfold searchPrecision
    exact (Nat.mul_le_mul hexp hp2).trans_eq (by ring)
  have hq := input_length M (searchPrecision p M) _ (normalizedRowApprox_size oracle P _)
  have hr := Nat.mul_le_mul hp (show 6*searchPrecision p M+22 ≤ 30*N^2+22 by omega)
  change _ ≤ normalizedInputBound.eval N
  simp only [normalizedInputBound,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_X,
    Polynomial.eval_ofNat,Polynomial.eval_pow]
  omega

end Selector
end Bit
end Lattice
end LinearProgramming
end Optimization
end OAI
