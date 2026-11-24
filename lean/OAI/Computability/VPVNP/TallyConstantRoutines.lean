import OAI.Computability.VPVNP.TallyStacks

/-! # Fixed literal and clear instructions for unary parameters -/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMTape.Tally

variable {K : Type*} [DecidableEq K]

/-- The finite control itself specifies the literal number of marks to append. -/
def addConstant (k : K) (a : ℕ) : Routine K (Fin (a+1)) where
  entry := Fin.last a
  code i := if h : i.val = 0 then .goto none else
    .push k true (some ⟨i.val - 1, by have := i.isLt; omega⟩)

theorem addConstant_runs (k : K) (a : ℕ) (s : State K) :
    (addConstant k a).Runs (a+1) (encode s) (encode (Function.update s k (s k+a))) := by
  have aux (j : ℕ) (hj : j ≤ a) (u : State K) :
      StackRuns (addConstant k a).standalone (j+1) (some ⟨j, by omega⟩) (encode u)
        none (encode (Function.update u k (u k+j))) := by
    induction j generalizing u with
    | zero =>
      simp only [Nat.add_zero, Function.update_eq_self]
      exact .cons (.goto rfl) (.nil ..)
    | succ j ih =>
      let v := Function.update u k (u k+1)
      have later := ih (by omega) v
      have hstate : Function.update v k (v k+j) = Function.update u k (u k+(j+1)) := by
        simp only [v, Function.update_self, Function.update_idem]
        congr 1
        omega
      rw [hstate] at later
      have step : StackStep (addConstant k a).standalone (some ⟨j+1, by omega⟩)
          (encode u) (some ⟨j, by omega⟩) (encode v) := by
        rw [show encode v = Function.update (encode u) k (true :: encode u k) from by
          rw [← encode_update, List.replicate_succ]; rfl]
        exact .push (by simp [Routine.standalone, Routine.close, addConstant])
      exact .cons step later
  exact aux a le_rfl s

/-- Pop all marks, returning on the first empty pop. -/
abbrev clear (k : K) := Routine.popLoop k (fun _ => true) (Routine.ret : Routine K Unit) Routine.ret

theorem clear_runs (k : K) (s : State K) :
    (clear k).Runs (2*s k+1) (encode s) (encode (Function.update s k 0)) := by
  have h := drainRuns k Routine.ret (fun j => Function.update s k j) (fun _ => 1) (s k)
    (fun _ _ => by simp) (fun i _ => by
      simp only [Function.update_idem]
      exact Routine.runs_ret _)
  simpa [clear, Function.update_eq_self, Nat.mul_comm, Nat.add_comm] using h

end RAMTape.Tally

end VPVNP
end Computability
end OAI
