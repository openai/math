import OAI.Optimization.LinearProgramming.PriceGame.ControlTrialArrayTree
import OAI.Optimization.LinearProgramming.PriceGame.ControlTrialGainWire
import OAI.Optimization.LinearProgramming.PriceGame.ControlTrialSourceNode
import OAI.Optimization.LinearProgramming.PriceGame.ControlTrialSchedulePrefix

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Control
namespace Trial

open States.Mass Moment TrialExecution

/-- Branchwise guards apply to every emitted transcript. -/
theorem Emits.of_guarded {N : ℕ} {a : Type*} {P : a → Prop} {Q : Query N → Prop}
    {p : Computation N a} {xs out} (h : Emits p xs out) (hp : p.Guarded Q P) : P out := by
  induction h with
  | pure => exact hp
  | ask b _ ih => exact ih (hp.2 b)

namespace SourceNode

variable {N ne : ℕ}

/-- Exactly the serialized-array and reduced-register information belonging to this real
source node, suitable for the typed reachability relation of the control interpreter. -/
def WeightArrays (c : SourceNode N ne) (env : Wire.Envelope) (r R : ℕ)
    (es : Fin ne → Expert N) (Q L B k : ℕ) : Prop :=
  env.TrialArraysFit r R es k c.level c.path c.history c.weights c.nonneg ∧
  WeightRegistersWithin r R es Q L B k c.level c.path c.history c.weights c.nonneg

theorem WeightArrays.input {c : SourceNode N ne} {env : Wire.Envelope} {r R : ℕ}
    {es : Fin ne → Expert N} {Q L B k : ℕ} (h : c.WeightArrays env r R es Q L B k) :
    env.InputFits c.input := by
  cases k with
  | zero => exact h.1
  | succ _ => exact h.1.1

private theorem emitted_baseline {c : SourceNode N ne} {r R k j : ℕ} {es : Fin ne → Expert N}
    (xs : Fin j → Call N ne r c.level) {tr rc} (h : Emits (c.stepAt r R es k j xs) tr rc) :
    rc.val.data.baseline = c.selectedPrice es xs := by
  by_cases hj : j<r
  · simp only [stepAt, executeStep, dite_eq_left hj] at h
    obtain ⟨_, _, _, _, _, rest⟩ := h.bind_inv
    obtain ⟨_, _, rfl⟩ := rest.map_inv
    simp only [selectedPrice, dite_eq_left hj, probeReturn]
  · simp only [stepAt, executeStep, dite_eq_right hj] at h
    obtain ⟨_, _, rfl⟩ := h.map_inv
    simp only [selectedPrice, dite_eq_right hj, finalReturn]

/-- The physical preparation record and weights for the selected recursive child at a
proper chronological call prefix. Every witness can use inconsistent branch replies. -/
theorem WeightArrays.at_prefix {c : SourceNode N ne} {env : Wire.Envelope} {r R : ℕ}
    {es : Fin ne → Expert N} {Q L B k j : ℕ} (bound : c.WeightArrays env r R es Q L B (k+1))
    (hj : j < 2*r) {tr xs} (pre : Emits (c.schedule r R es k j) tr xs) :
    env.PreparedFits (c.prepared R es xs.val) ∧
    (c.next es xs.val).WeightArrays env r R es Q L B k ∧
    ∀ e, (incomingLocal es c.weights xs.val e).den ∣ L ∧ RAM.ratBits (incomingLocal es c.weights xs.val e) ≤ B := by
  let step := c.stepAt r R es k
  let idx : Fin (2*r) := ⟨j,hj⟩
  obtain ⟨ev,evt⟩ := emits_run (step j xs.val) (fun _ _ => false) []
  obtain ⟨_,ys,full,prior,chosen⟩ := runSchedule_extend_at_emits (fun _ prev call => StepOK es c.weights prev call)
    step idx pre evt
  have first := (full.of_guarded bound.1.2) idx
  have second := full.of_guarded bound.2.2
  have child := second.2 idx
  have base := emitted_baseline xs.val evt
  let branch (rows : Fin j → Call N ne r c.level) (y : Prices N c.level) :=
    c.extend y (incomingDeep es c.weights rows) (incomingDeep_nonneg es c.weights c.nonneg rows)
  have current := (congrArg (fun a : Call N ne r c.level => a.data.baseline) chosen).trans base
  have nextEq : branch («prefix» ys.val idx) (ys.val idx).data.baseline = c.next es xs.val :=
    congrArg₂ branch prior current
  have branchBound : (branch («prefix» ys.val idx) (ys.val idx).data.baseline).WeightArrays
      env r R es Q L B k := ⟨first.2,child⟩
  have prep : env.PreparedFits (c.prepared R es («prefix» ys.val idx)) := first.1
  refine ⟨(congrArg (fun rows : Fin j → Call N ne r c.level => env.PreparedFits (c.prepared R es rows)) prior).mp prep,
    (congrArg (fun next : SourceNode N ne => next.WeightArrays env r R es Q L B k) nextEq).mp branchBound, ?_⟩
  have cut : takePrefix ys.val j hj.le = xs.val := prior
  intro e
  have weight := (second.1 j hj.le e).1
  change (incomingLocal es c.weights (takePrefix ys.val j hj.le) e).den ∣ L ∧
    RAM.ratBits (incomingLocal es c.weights (takePrefix ys.val j hj.le) e) ≤ B at weight
  rwa [cut] at weight

/-- All signed gain registers cached in the actual physical prefix, including after
previous adaptive labels and markets. -/
theorem WeightArrays.gains {c : SourceNode N ne} {env : Wire.Envelope} {r R : ℕ}
    {es : Fin ne → Expert N} {Q L d B k : ℕ} (bound : c.WeightArrays env r R es Q L B (k+1))
    (hL : 0<L) (hd : L≤2^d) (j : ℕ) (hj : j≤2*r) {tr xs}
    (pre : Emits (c.schedule r R es k j) tr xs) : ∀ i : Fin j, ∀ e : Fin ne,
    RAM.ratBits ((xs.val i).data.gain[e]) ≤ 3+2*(B+d) := by
  induction j generalizing tr with
  | zero => intro i; exact Fin.elim0 i
  | succ j ih =>
    unfold schedule at pre
    rw [runSchedule] at pre
    obtain ⟨_,ys,_,_,prefixTrace,next⟩ := pre.bind_inv
    obtain ⟨z,last,rfl⟩ := next.map_inv
    have hp := bound.at_prefix (show j<2*r by omega) prefixTrace
    have hlast := executeStep_emits_gain_bits es c.weights c.nonneg c.history c.path _ hL hd ys.val hp.2.2 last
    intro i e
    cases i using Fin.lastCases with
    | cast i =>
      simpa only [snocSchedule, Fin.snoc_castSucc] using ih (by omega) prefixTrace i e
    | last =>
      simpa only [snocSchedule, Fin.snoc_last] using hlast e

end SourceNode
end Trial
end Control
end PriceGame
end LinearProgramming
end Optimization
end OAI
