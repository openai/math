import OAI.Computability.VPVNP.RAMPrivateLog
import OAI.Computability.VPVNP.RAMLocalRun

/-!
# The logged interpreter computes the same metered local calls

The physical processor represents private memory by a finite write log.
These equations transfer the native instruction and probe cutoff, including
rejection on a short guess stream, to that representation.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace BurstRAM

variable {w : ℕ} {C D : Type*}

theorem runLocalCall_map {P : Program w C} {Q : Program w D} (denote : C → D)
    (step : ∀ c, (P.step c).mapState denote = Q.step (denote c))
    (fuel : ℕ) (c : C) (allowance : ℕ) (bits : List Bool) :
    runLocalCall P fuel c allowance bits = runLocalCall Q fuel (denote c) allowance bits := by
  induction fuel generalizing c allowance bits with
  | zero => rfl
  | succ f ih =>
    rw [runLocalCall, runLocalCall, ← step]
    cases P.step c with
    | localStep _ => simp only [CallAction.mapState, ih]
    | branch _ => cases bits <;> simp only [CallAction.mapState, ih]
    | read _ _ =>
      cases allowance with
      | zero => rfl
      | succ _ =>
        cases h : takeWord w bits with
        | none => rfl
        | some pair => obtain ⟨v, tail⟩ := pair; simp only [CallAction.mapState, ih]
    | write _ _ _ => cases allowance <;> simp only [CallAction.mapState, ih]
    | finish _ | reject => rfl

namespace PrivateRAM

variable {p r k : ℕ}

theorem Machine.localCall_logged (M : Machine w p r k) (fuel : ℕ) (l : LogConfig w p r)
    (allowance : ℕ) (bits : List Bool) :
    runLocalCall M.logProgram fuel l allowance bits = runLocalCall M.program fuel l.denote allowance bits :=
  runLocalCall_map LogConfig.denote M.logProgram_step fuel l allowance bits

theorem Machine.chargedCall_logged (M : Machine w p r k) (fuel : ℕ) (persist : Word w)
    (callLeft globalLeft siteLeft : ℕ) (bits : List Bool) :
    runChargedCall M.logProgram fuel (M.logProgram.start persist) callLeft globalLeft siteLeft bits =
      runChargedCall M.program fuel (M.program.start persist) callLeft globalLeft siteLeft bits := by
  unfold runChargedCall
  cases min callLeft (min globalLeft siteLeft) with
  | zero => rfl
  | succ _ => exact M.localCall_logged ..

end PrivateRAM
end BurstRAM

end VPVNP
end Computability
end OAI
