import OAI.Computability.BorderVNP.DiagonalJointSchedule
import OAI.Computability.BorderVNP.RoutingISAScheduleClockWindows
import OAI.Computability.BorderVNP.DiagonalAdmissibleRange

/-! # One signed clock window on the physical team sequence before the stretch is chosen -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal

open Filter Crossing Packing Cover Epoch PackedHistoryCircuit.Normalized TeamScales
open RoutingISA.Evaluator RoutingISA.Evaluator.ScheduleClock

variable {D m : ℕ} [NeZero D] {L : Type*} [Field L] {e : PaidIdentity L D m} {S : SiteSchedule e}
    {a extra : ℕ} (s : EpochScales S a extra)

/-- The five signed phase windows at the actual team count and per-team batch size.
Each window is shared by all substitutions and profile branches at that length. -/
noncomputable def EpochScales.signedWindows (degree K fixed F H n r : ℕ) : PhaseCharges :=
  let R := teams s.α s.τ (epochCopies S) n
  let ξ := (s.τ:ℝ)/5
  uniformWindows r R (exterior ξ r n) ⌈publicWork a s.α r n R⌉₊
    ⌈localWork a degree s.α ξ r n R⌉₊ K fixed F H

/-- Choose the allowed interval of processor exponents before the candidate circuit or
the public geometry branches are supplied. It pays every phase of the signed evaluator
at the same physical length, batch size and team count. -/
theorem EpochScales.signed_clock_range (degree K fixed F H : ℕ) (ha : 1 ≤ a) :
    ∃ ν : ℝ, 0 < ν ∧ AdmissibleRange ν (fun n r =>
      let c := s.signedWindows degree K fixed F H n r
      c.core+c.before+c.argumentsCalls+c.finish+c.reader ≤ ticks ((s.τ:ℝ)/5) r n) := by
  have ht : 0 < (s.τ:ℝ) := by exact_mod_cast s.tau_pos
  have hα : 0 < (s.α:ℝ) := by exact_mod_cast s.alpha_pos
  obtain ⟨ν,pos,windows⟩ := eventually_uniformWindows a degree K fixed F H ha hα.le s.alpha_cube
    (by positivity : 0 < (s.τ:ℝ)/5) (by linarith [s.tau_small,s.alpha_small])
  refine ⟨ν,pos,?_⟩
  filter_upwards [windows,eventually_many_teams hα (s.τ:ℝ) (epochCopies_pos S) 1,eventually_ge_atTop 1]
    with n fit enough hn
  intro r hr cap
  exact fit r _ hr enough cap (teams_le (epochCopies_pos S) hn ht.le s.copy_rate)

end Diagonal

end BorderVNP
end Computability
end OAI
