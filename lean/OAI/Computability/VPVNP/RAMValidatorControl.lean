import OAI.Computability.VPVNP.RAMSiteWork

/-!
# The local post-call control check of Lemma 10.1

The validator checks that it used every private choice bit. On an internal
successor edge it compares the final cumulative cost and status to the send.
At the last site it requires the computed status to be an accepting halt.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace BurstRAM

variable {w : ℕ}

/-- A nonempty suffix rejects immediately. Otherwise the validator scans each
report and event once. The fixed cost covers the end-of-input test, the
status, cost and state comparisons, branching and return. -/
def finishReports (input : Cut w) (output : Option (Cut w)) (reports : List (Report w))
    (tail : List Bool) : Bool × ℕ :=
  match tail with
  | _ :: _ => (false, 2)
  | [] =>
    let final := meteredAdvance input reports
    let valid := match output with
      | some c => decide (c = final.1)
      | none => final.1.state.isNone
    (valid, 16 + final.2)

theorem finishReports_spec (input : Cut w) (output : Option (Cut w)) (reports : List (Report w))
    (tail : List Bool) :
    (finishReports input output reports tail).1 = true ↔ tail = [] ∧
      match output with
      | some c => c = input.advance reports
      | none => (input.advance reports).state = none := by
  cases tail <;> cases output <;> simp [finishReports, meteredAdvance_result]

theorem finishReports_work (input : Cut w) (output : Option (Cut w)) (reports : List (Report w))
    (tail : List Bool) (H fuel : ℕ)
    (h : reports.length ≤ 2 * H ∧ ∀ r ∈ reports, r.events.length < fuel) :
    (finishReports input output reports tail).2 ≤ 32 + (2*H)*(16*fuel+16) := by
  cases tail with
  | cons bit bits => simp [finishReports]; omega
  | nil =>
    have hscan := meteredAdvance_work_le input reports fuel h.2
    have hsize : reports.length * (7 + 4*fuel) ≤ (2*H)*(16*fuel+16) :=
      Nat.mul_le_mul h.1 (by omega)
    simp only [finishReports]
    omega

end BurstRAM

end VPVNP
end Computability
end OAI
