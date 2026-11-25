import OAI.Optimization.LinearProgramming.Lattice.LLLBitWidth
import OAI.Optimization.LinearProgramming.Lattice.LLLReachNative

/-! A cubic unary clock in the physical input tape suffices for the actual native integer
LLL trajectory. Running that many steps returns the exact native basis. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Lattice
namespace Bit

open Hex.Internal

/-- A terminal native cursor is absorbing. -/
def hold {n m : ℕ} (c : ReductionCursor n m) : ReductionCursor n m := c.next.getD c

theorem hold_iterate_trace {n m : ℕ} (c : ReductionCursor n m) (t : ℕ) :
    hold^[t] c = (c.trace t).1 := by
  induction t generalizing c with
  | zero => rfl
  | succ t ih =>
    rw [Function.iterate_succ_apply, ReductionCursor.trace]
    cases h : c.next with
    | none =>
      have hfixed : hold c = c := by simp [hold,h]
      rw [hfixed]
      exact Function.iterate_fixed hfixed t
    | some d =>
      have hnext : hold c = d := by simp [hold,h]
      rw [hnext]
      exact ih d

theorem initial_reaches_hold {n m : ℕ} (c : ReductionCursor n m) (t : ℕ) :
    c.Reaches (hold^[t] c) := by
  rw [hold_iterate_trace]
  exact c.reaches_trace t

noncomputable def lllTime : Polynomial ℕ := Polynomial.C 30 * (Polynomial.X+1)^3

/-- The integer LLL time clock depends only on the length of the complete original table. -/
theorem lllTime_rank {n m : ℕ} (b : Hex.Matrix ℤ n m) (hn : 1 ≤ n) :
    indexedReductionRank n (LLLState.ofBasis b).potential 1 ≤
      lllTime.eval (intMatrixCode (packMatrix b)).length := by
  let L := (intMatrixCode (packMatrix b)).length
  obtain ⟨hnL,hmL,hentries⟩ := packedMatrix_input_bounds b hn
  have hB (i : Fin n) (j : Fin m) : ((HexMatrixMathlib.matrixEquiv b) i j).natAbs ≤ 2^L :=
    by
      rw [HexMatrixMathlib.matrixEquiv_apply]
      exact (Nat.size_le.mp (hentries i j)).le
  let K := (n+m+2*L)*n*n
  let P := (LLLState.ofBasis b).potential
  have hP : P ≤ 2^K := nativeInitialPotential_le b hB
  have hcube : P^3 ≤ 2^(3*K) := by
    calc
      _ ≤ (2^K)^3 := Nat.pow_le_pow_left hP 3
      _ = _ := by rw [← pow_mul, Nat.mul_comm]
  have hsize := Nat.size_le_size hcube
  rw [Nat.size_pow] at hsize
  change 2*(P^3).size+(n-1) ≤ _
  calc
    _ ≤ 2*(3*((n+m+2*L)*n*n)+1)+n := by dsimp [K] at hsize; omega
    _ ≤ 2*(3*((L+L+2*L)*L*L)+1)+L := by gcongr
    _ ≤ 30*(L+1)^3 := by ring_nf; omega
    _ = _ := by simp [lllTime,L]

/-- A polynomial-length indexed computation agrees bit for bit with the library's
potential-fueled function, even if their nominal clocks differ considerably. -/
theorem lllTime_result {n m : ℕ} (b : Hex.Matrix ℤ n m) (hn : 1 ≤ n) (hi : b.independent) :
    let T := lllTime.eval (intMatrixCode (packMatrix b)).length
    ((hold^[T]) (initialReductionCursor b hn)).state.b = Hex.lllNative b (3/4) (hn := hn) := by
  let c := initialReductionCursor b hn
  let T := lllTime.eval (intMatrixCode (packMatrix b)).length
  let f := lllFuel (LLLState.ofBasis b)
  have hv := HexLLLMathlib.LLLState.ofBasis_valid b
  have hstop : (c.trace T).1.next = none :=
    (reductionTrace_bound c T hv hi).2 (lllTime_rank b hn)
  have hfix : hold ((hold^[T]) c) = (hold^[T]) c := by
    rw [hold_iterate_trace]
    simp [hold,hstop]
  have hlarge : (hold^[f+T]) c = (hold^[T]) c := by
    rw [Function.iterate_add_apply]
    exact Function.iterate_fixed hfix f
  have he := LLLState.lllLoop_fuel_sufficient (LLLState.ofBasis b) (3/4) (by norm_num) (by norm_num) hn hv hi
    (show lllFuel (LLLState.ofBasis b) ≤ f+T from Nat.le_add_right _ _)
  calc
    ((hold^[T]) c).state.b = ((hold^[f+T]) c).state.b := congrArg (fun v => v.state.b) hlarge.symm
    _ = c.nativeAt (f+T) := by rw [hold_iterate_trace,reductionTrace_native]
    _ = Hex.lllNative b (3/4) (hn := hn) := he.symm

end Bit
end Lattice
end LinearProgramming
end Optimization
end OAI
