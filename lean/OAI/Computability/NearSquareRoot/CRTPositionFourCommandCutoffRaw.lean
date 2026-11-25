import OAI.Computability.NearSquareRoot.CRTPositionFourCommandCutoff
import OAI.Computability.NearSquareRoot.BoundedProgramForget
import OAI.Computability.NearSquareRoot.ScheduleRegisterSelectLink

/-! # Correctness of cutoff dispatch without a reserve assumption -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Controlled.PositionCmd

open IntegerMultiplication IntegerMultiplication.Code Space

/-- If the named programs terminate with the prescribed result on their own
width ranges, the generated cutoff command does so on every input. -/
theorem cutoff_raw {I : Type} (K : ℕ) (k : I → ℕ) (p : ∀ i, Equiv.Perm (Fin (k i)))
    (data output : I → Tree) {big small : Cmd}
    (large : ∃ t, EffectiveTask.Runs big t
      (fun i : {i // K < k i} => cutoffInput p data i.val) (fun i => output i.val))
    (short : ∃ t, EffectiveTask.Runs small t
      (fun i : {i // k i ≤ K} => cutoffInput p data i.val) (fun i => output i.val)) :
    ∃ t, EffectiveTask.Runs (cutoffCmd K big small) t (cutoffInput p data) output := by
  obtain ⟨largeTime,hl⟩ := large
  obtain ⟨shortTime,hs⟩ := short
  let branchTime (i : I) := if h : K < k i then largeTime ⟨i,h⟩ else shortTime ⟨i,Nat.le_of_not_gt h⟩
  let budget i := 2^(k i) + (cutoffInput p data i).count + branchTime i
  have go := cutoff_runs K k budget budget p data output (fun _ => le_rfl)
    (fun i => by dsimp [budget]; omega) 1 (fun i => by
      change (data i).count ≤ 1*(2^(k i)+((send (Reflections.table (p i))).count+(data i).count+1)+_+1)
      have := Nat.zero_le (2 ^ k i)
      omega) (big := big) (small := small)
  have run := go
    ((EffectiveBoundedTask.Runs.of_time hl).mono (fun i => by simp [budget,branchTime,i.property])
      (fun i => by rcases i with ⟨i,h⟩; simp [budget,branchTime,h, Nat.add_assoc]))
    ((EffectiveBoundedTask.Runs.of_time hs).mono (fun i => by simp [budget,branchTime,Nat.not_lt.mpr i.property])
      (fun i => by rcases i with ⟨i,h⟩; simp [budget,branchTime,Nat.not_lt.mpr h,Nat.add_assoc]))
  refine ⟨budget,?_⟩
  exact command_contract (cutoffCmd K big small) from BoundedTask.forget
    (show BoundedTask budget budget (cutoffInput p data) output from ⟨_,run⟩)

end Controlled.PositionCmd

end NearSquareRoot
end Computability
end OAI
