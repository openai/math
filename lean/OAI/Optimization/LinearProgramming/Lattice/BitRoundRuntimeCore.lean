import OAI.Optimization.LinearProgramming.Lattice.BitRoundSemanticCore
import OAI.Optimization.LinearProgramming.Lattice.BitRoundWidthEnv
import OAI.Optimization.LinearProgramming.Lattice.BitProbeWidthEncoding
import OAI.Optimization.LinearProgramming.Lattice.BitRoundPacketSize
import OAI.Optimization.LinearProgramming.Lattice.QueryTheorem

/-! Polynomials bounding every physical word and the entire clock of the one
finite Appendix A machine. The oracle may depend on history, provided each
well-formed row receives the stated three-valued sign. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Lattice
namespace Bit
namespace Driver

open ExactQuantumFactoring.BitStackProgram OracleSpec
open Polynomial

noncomputable def requestBound : Polynomial ℕ := 100*X^6

noncomputable def probeInputBound : Polynomial ℕ := X+requestBound+RoundWidth.coefficientBound

noncomputable def frameBound : Polynomial ℕ :=
  2*RoundWidth.envBound + Probe.probeWordPolynomial.comp probeInputBound + 7 +
    (2*requestBound+2)*X + 3*X+2

noncomputable def machineTime (step : Polynomial ℕ) : Polynomial ℕ :=
  (requestBound+1) * (step.comp frameBound+18*frameBound+18)+3

private theorem requestBound_eq (N : ℕ) : requestBound.eval N = 100*N^6 := by
  simp [requestBound]

private theorem precision_le (p M : ℕ) : searchPrecision p M ≤ requestBound.eval (RoundWidth.parameter p M) := by
  rw [requestBound_eq]
  apply le_trans _ (rounding_parameter_bounds p M).2.1
  dsimp only [queryCoefficientWidth]
  exact (Nat.le_succ (searchPrecision p M)).trans (Nat.le_add_right _ _)

private theorem frameBound_parts (N : ℕ) :
    frameBound.eval N = 2*RoundWidth.envBound.eval N + Probe.probeWordPolynomial.eval (probeInputBound.eval N)+7 +
      (2*requestBound.eval N+2)*N+3*N+2 := by
  simp [frameBound,Polynomial.eval_comp]

theorem reached_fits_with {f : Kernels} (sem : RoundKernelSemantics f) {p M : ℕ} {q : Request}
    (hq : RequestReachedWith f p M q)
    (reply : Word → Word) (hanswer : ∀ w, (reply w).length ≤ 2) :
    requestFits (frameBound.eval (RoundWidth.parameter p M)) reply q := by
  obtain ⟨fuel,old,row,c,hold,rfl,hreach⟩ := hq
  let N := RoundWidth.parameter p M
  let k := searchPrecision p M
  let B := RoundWidth.coefficientBound.eval N
  let budget := Probe.probeWordPolynomial.eval (p+k+B)
  have hp : p ≤ N := RoundWidth.dim_le p M
  have hparam : p+k+B ≤ probeInputBound.eval N := by
    simp only [probeInputBound,Polynomial.eval_add,Polynomial.eval_X]
    have hk := precision_le p M
    dsimp only [N,k,B] at *
    omega
  have hb : budget ≤ Probe.probeWordPolynomial.eval (probeInputBound.eval N) :=
    Procedure.eval_nat_mono _ hparam
  have hlen : old.length ≤ p := by have := hold.count; omega
  have hf : fuel ≤ p := by have := hold.count; omega
  have hc (i j : Fin p) : (integralRows (residualTableMatrix old) i j).natAbs ≤ 2^B := by
    rw [residualTableMatrix_eq]
    exact (Nat.size_le.mp (RoundWidth.residual_width old hlen hold.digits hold.independent i j)).le
  have hz : Probe.ParamBound p k (2^B) (probeParams f (packedEnv M fuel old)) := by
    rw [sem.params M fuel old hold.independent]
    exact Probe.bounded_square_params _ hc
  have hrow : (intRowCode row).length ≤ budget := Probe.reachable_query_size hz hreach
  have hcarry : (Probe.carryCode c).length ≤ budget := Probe.reachable_carry_size hz hreach
  apply sign_requestFits reply row (packedEnv M fuel old) c (RoundWidth.envBound.eval N) budget
    (frameBound.eval N) (RoundWidth.env_length old hlen hf hold.digits) hrow hcarry (hanswer _)
  rw [frameBound_parts]
  omega

theorem output_frame {p M : ℕ} {z : Fin p → ℤ} (hz : ∀ i, (z i).natAbs.size ≤ radixWidth p M*p) :
    (signRowWord z).length ≤ frameBound.eval (RoundWidth.parameter p M) := by
  let N := RoundWidth.parameter p M
  have hp : p ≤ N := RoundWidth.dim_le p M
  have hb : radixWidth p M*p ≤ requestBound.eval N := by
    rw [requestBound_eq]
    exact (rounding_parameter_bounds p M).2.2
  have out : (signRowWord z).length ≤ (2*requestBound.eval N+2)*N := calc
    _ = ∑ i, (2*(z i).natAbs.size+2) := signRowWord_length z
    _ ≤ ∑ _i : Fin p, (2*requestBound.eval N+2) :=
      Finset.sum_le_sum (fun i _ => by have := (hz i).trans hb; omega)
    _ ≤ _ := by simpa [mul_comm] using Nat.mul_le_mul_right (2*requestBound.eval N+2) hp
  change (signRowWord z).length ≤ frameBound.eval N
  rw [frameBound_parts]
  exact out.trans (by omega)

theorem opening_frame (p M : ℕ) :
    (WordDialogue.stateCode inputCode carryCode (.inl (p,M))).length ≤
      frameBound.eval (RoundWidth.parameter p M) := by
  rw [opening_length,frameBound_parts]
  unfold RoundWidth.parameter
  omega

theorem physical_time_with (step : Polynomial ℕ) {p M : ℕ} {rounds : ℕ}
    (h : rounds ≤ p*(2*p+1+p*searchPrecision p M)) :
    let N := RoundWidth.parameter p M
    let L := frameBound.eval N
    (rounds+1)*(step.eval L+18*L+18)+3 ≤ (machineTime step).eval N := by
  intro N L
  have hb : rounds ≤ requestBound.eval N := by
    rw [requestBound_eq]
    exact h.trans (rounding_parameter_bounds p M).1
  simp only [machineTime,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_one,
    Polynomial.eval_ofNat,Polynomial.eval_comp]
  gcongr

end Driver
end Bit
end Lattice
end LinearProgramming
end Optimization
end OAI
