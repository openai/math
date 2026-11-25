import OAI.LinearAlgebra.FiniteFourier.ConvolutionCost
import OAI.LinearAlgebra.FiniteFourier.OpenConvolution

/-! # Fixed-operand products over the coefficient rings of integral descent

Specialize the right operand of a formal circuit and differentiate in the
left-input direction. All coefficients of the resulting linear circuit
belong to the same ring as the fixed operand. In particular this construction
preserves the denominator restrictions on the prime lists.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

/-- A formal product circuit of cost `c` provides a shared linear circuit of
cost at most `c` for convolution with a vector over any target ring. -/
theorem ComputesConvolution.circuit_fixed {R K : Type*} [CommRing R] [CommRing K] {n r : ℕ}
    {P : MatrixMultiplication.Arithmetic.Program R (Fin n ⊕ Fin n) r}
    {out : Fin (2*n-1) → Fin r} (hP : ComputesConvolution P out) (φ : R →+* K)
    (y : Fin n → K) :
    ∃ s ≤ P.cost, ∃ q : Circuit K (Fin n) (Fin (2*n-1)) s,
      ∀ x k, q.eval x k = openConv K n x y k := by
  classical
  let lift : Circuit K (Fin n) (Fin n ⊕ Fin n) 0 :=
    ⟨.nil, Sum.elim (fun i => .scaled 1 (.inl i)) (fun _ => .zero)⟩
  have hl (x : Fin n → K) : lift.eval x = Sum.elim x (fun _ => 0) := by
    funext i
    cases i <;> simp [lift, Circuit.eval, Readout.eval]
  obtain ⟨s, hs, q, hq⟩ := exists_circuit_jacobian φ (Sum.elim (fun _ => 0) y) P out
  obtain ⟨s', hs', q', hq'⟩ := circuit_comp lift q
  refine ⟨s', (by simpa using hs' : s' ≤ s).trans hs, q', ?_⟩
  intro x k
  rw [hq', hl, hq, hP, Fintype.sum_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr, mul_zero, Finset.sum_const_zero, add_zero,
    derivativeRow_convolution_left, openConv]
  apply Finset.sum_congr rfl
  intro i _
  rw [mul_comm, Finset.mul_sum]
  simp [mul_ite]

/-- In particular, the length-`n` recursive cost over the integers also
pays for a product with fixed data from any commutative coefficient ring. -/
theorem exists_fixed_convolution_circuit {K : Type*} [CommRing K] (n : ℕ) (y : Fin n → K) :
    ∃ s ≤ integralConvolutionCost n, ∃ q : Circuit K (Fin n) (Fin (2*n-1)) s,
      ∀ x k, q.eval x k = openConv K n x y k := by
  obtain ⟨_, _, _, hp, hc⟩ := integralConvolutionCost_attained n
  rw [← hc]
  exact hp.circuit_fixed (Int.castRingHom K) y

end FiniteFourier
end LinearAlgebra
end OAI
