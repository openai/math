import OAI.Computability.NearSquareRoot.ScheduleRegisterConstructors
import OAI.Computability.IntegerMultiplication.Code.Slice

/-! # Exact division of a tally by a hardcoded arity -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace RegisterDivide
open IntegerMultiplication Code CommonRegisters RegisterWitness

/-- Consume exactly a block of list cells. A short block gives the empty tally. -/
def block : ℕ → Cmd → Cmd
  | 0, k => k
  | j+1, k => splitRoot 0 (fun _ => give 0 false)
      (splitRoot 0 (fun _ => block j k) .pass)

def emit : Cmd := .join (.again 0) (.join (give 0 false) (pack 0))

def command (d : ℕ) : Cmd := .tie (block (d+1) emit)

theorem within {R : ℕ} (hr : 0 < R) (d : ℕ) : Within R (command d) := by
  suffices h : ∀ j, Within R (block j emit) from h (d+1)
  intro j
  induction j with
  | zero => simp [block, emit, Within, give, pack, hr]
  | succ j ih => simp [block, Within, give, hr, ih]

private theorem complete (j n : ℕ) {k : Cmd} {env : Env} {r s : Deck} {t : ℕ}
    (h : Fits env k (pile 0 (send (tally n)) r) s t) :
    Fits env (block j k) (pile 0 (send (tally (j+n))) r) s (t+8*j) := by
  induction j with
  | zero => simpa [block] using h
  | succ j ih =>
    rw [Nat.succ_add,tally_succ,send_cons]
    exact (fits_pair (fits_bit (b := false) (c := fun _ => block j k) ih)).mono (by omega)

/-- The same command works on every exact multiple and every parked deck. -/
theorem divide {R : ℕ} (hR : 0 < R) (d : ℕ) :
    Timed R id (fun n => send (tally ((d+1)*n))) (fun n => send (tally n)) := by
  refine ⟨command d,within hR d,8*(d+1)+16,fun n env r => ?_⟩
  let b := block (d+1) emit
  have run (n : ℕ) : Fits (b::env) b (pile 0 (send (tally ((d+1)*n))) r)
      (pile 0 (send (tally n)) r) ((8*(d+1)+15)*n+5) := by
    induction n with
    | zero =>
      change Fits (b::env) (splitRoot 0 (fun _ => give 0 false) _)
        (pile 0 (.atom false) r) (pile 0 (.atom false) r) _
      exact fits_bit (c := fun _ => give 0 false) (fits_give false r 0 _)
    | succ n ih =>
      have step := ih.again0.join ((fits_give false (pile 0 (send (tally n)) r) 0 (b::env)).join
        (fits_pack (.atom false) (send (tally n)) r 0 (b::env)))
      have h := complete (d+1) ((d+1)*n) (k := emit) step
      rw [Nat.mul_succ,Nat.add_comm ((d+1)*n) (d+1),tally_succ,send_cons]
      exact h.mono (by simp only [Nat.mul_succ]; omega)
  exact (run n).tie.mono (by change _ ≤ (8*(d+1)+16)*(n+1); rw [Nat.mul_add,Nat.mul_one]; nlinarith)

end RegisterDivide

end NearSquareRoot
end Computability
end OAI
