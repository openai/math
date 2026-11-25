import OAI.Optimization.LinearProgramming.NormalSubspace.Calls
import OAI.Optimization.LinearProgramming.Recovery.InitialOrientationSize
import OAI.Optimization.LinearProgramming.Recovery.InitialOrientationTable
import OAI.Optimization.LinearProgramming.Recovery.GlobalCapacity

/-! Invoke the fixed ordinary marked-subspace program on the two adjacent
initial bases, and identify its returned flag with the rational LP alternative. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Recovery
namespace InitialOrientation

open Matrix RAM RAM.Callable OracleSpec Geometry
open scoped Matrix

private theorem equal_flags {a b : Bool} (same : (a=true) ↔ (b=true)) : a=b := by
  cases a <;> cases b <;> simp_all

theorem first_call {m d k s : ℕ} (solver : NormalSubspace.Spec)
    (A : Matrix (Fin m) (Fin d) ℚ) (b : Fin m→ℚ) (F : Matrix (Fin k) (Fin (m+1)) ℚ)
    (R : Matrix (Fin s) (Fin (m+1)) ℚ) (front back : Memory ℚ)
    (frontSafe : PairBuilder.Within (InitialPair.fragmentWidth m d (max 3 (totalBits (lpInput A b)))) front)
    (backSafe : PairBuilder.Within (InitialPair.fragmentWidth m d (max 3 (totalBits (lpInput A b)))) back)
    (foot : Footprint (PairBuilder.capacity (d+1) (m+1) 0-1) (front.atPC 0))
    (ready : PairBuilder.Prepared false (InitialPair.layout m d) (slackColumns A b)ᵀ F R back) :
    let cap := PairBuilder.capacity (d+1) (m+1) 0
    let W := (width solver).eval (m+d+totalBits (lpInput A b))
    ∃ next, (NormalSubspace.call solver 154).Run (fun z => ratBits z ≤ W) (Odd.memory front back)
      (NormalSubspace.callTime solver cap (m+1))
      (Odd.memory next (back.putIndex 154 (Principal.ref A b).primal.toNat)) ∧
      Footprint (Principal.capacity solver m d-1) (next.atPC 0) := by
  let cap := PairBuilder.capacity (d+1) (m+1) 0
  let W := (width solver).eval (m+d+totalBits (lpInput A b))
  have dims : k+s=m+1 := (Nat.add_comm k s).trans ready.total
  have boundsF := table_width ready.firstTable backSafe
  have boundsR := table_width ready.lastTable backSafe
  obtain ⟨smaller,zero,size⟩ := width_bounds solver A b F R dims boundsF boundsR
  obtain ⟨indR,indF,perp,_,_⟩ := kernelPair_spec (slackColumns A b)ᵀ F R ready.firstSpan ready.kernelSpan
  have orth : F*Rᵀ=0 := by
    simpa only [Matrix.transpose_mul,Matrix.transpose_transpose,Matrix.transpose_zero] using
      congrArg Matrix.transpose perp
  have canReset : 2 ≤ cap := PairBuilder.pair_fits (d+1) (m+1) 0
  have wordsFit : (m+1)*(m+1) ≤ cap := PairBuilder.input_fits (h:=d+1) 0 (Nat.le_add_left ..)
  obtain ⟨next,answer,run,decodes,footprint⟩ := NormalSubspace.call_run solver F R dims
    (Nat.zero_lt_succ m) indF indR orth back front (InitialPair.layout m d).out 208 cap (cap-1) 154 W
    ready.tapes foot (by omega) wordsFit canReset (fun i => (backSafe i).trans smaller)
    (fun i => (frontSafe i).trans smaller) zero size
  have answerSame : answer=(Principal.ref A b).primal := by
    apply equal_flags
    exact decodes.trans (Principal.initial_answer A b F ready.firstSpan).symm
  rw [answerSame] at run
  have window := Principal.capacity_after_initial solver m d k s (MinorLog.entries F++MinorLog.entries R)
    dims (pair_data_length F R dims)
  exact ⟨next,run,footprint.mono (by omega)⟩

end InitialOrientation
end Recovery
end LinearProgramming
end Optimization
end OAI
