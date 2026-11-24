import OAI.Computability.VPVNP.QueryMachine
import OAI.Computability.VPVNP.QueryClock
import OAI.Computability.VPVNP.ProgramLength

/-!
# Query predicates as coefficients of the explicit family

The literal encoding of a bounded query program supplies a fixed prefix.
Appending any payload computes its Boolean query result with the universal
coefficient machine's prescribed clock.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace QueryMachine

open UniversalMachine

/-- A single program prefix compiles the entire finite query program at a
given query budget. Every payload is interpreted with the fixed clock of §1.1. -/
theorem exists_prefix {k : ℕ} {Q : Type*} [Fintype Q] (p : QueryProgram k Q) (t : ℕ) :
    ∃ (l : ℕ) (bits : Fin l → Bool),
      l ≤ 1000 * ((t + 1) * Fintype.card Q * (k + 1) + 1) ^ 2 ∧
      ∀ x : Fin k → Bool, acceptingCount (Fin.append bits x) = (p.eval x t p.start).toNat := by
  let pre := programPrefix (machine p t)
  have hc : (machine p t).extra = (t + 1) * Fintype.card Q * (k + 1) := by
    simp [machine, TableCompiler.compile, Control, Nat.mul_assoc]
  refine ⟨pre.length, pre.get, (programPrefix_length_le _).trans_eq (by rw [hc]), ?_⟩
  intro x
  have hq : 0 < Fintype.card Q := Fintype.card_pos_iff.mpr ⟨p.start⟩
  have hstates : t + 1 ≤ (machine p t).extra := by
    rw [hc]
    exact (Nat.le_mul_of_pos_right _ hq).trans (Nat.le_mul_of_pos_right _ (by omega))
  simp only [acceptingCount, List.ofFn_fin_append, List.ofFn_get, pre, decode_programPrefix]
  exact correct p t pre x _ (querySteps_le_clock rfl (queryPrefix_lower hstates))

end QueryMachine

end VPVNP
end Computability
end OAI
