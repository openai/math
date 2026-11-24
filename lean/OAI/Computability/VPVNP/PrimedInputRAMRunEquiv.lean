import OAI.Computability.VPVNP.PrimedInputRAMExecution
import OAI.Computability.VPVNP.RAMSuccessor

/-!
# Choice histories of the scheduled primed-input RAM

A native RAM path records one list of branch choices per call. A choose item
contributes a singleton and every other item contributes the empty list, as
does the final accepting call. Reading the singleton at each owner recovers
the chosen assignment even when several branches write equal words.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PrimedInputRAM

open BurstRAM

variable {M w : ℕ}

/-- The exact choice lists supplied to the item calls and the final call. -/
def assignmentCalls (ops : Fin M → Item w) (f : Assignment (fun i ↦ (ops i).owns)) :
    List (List Bool) :=
  (List.finRange M).map (fun i ↦ (ops i).bits (bitAt f i)) ++ [[]]

/-- Read the first choice of the call at each owner. The defaults make the
decoder total on malformed streams, which are excluded from `ActualPaths`. -/
def decodeAssignmentCalls (ops : Fin M → Item w) (bs : List (List Bool)) :
    Assignment (fun i ↦ (ops i).owns) :=
  fun i ↦ ((bs[i.val.val]?).getD []).headD false

theorem decode_assignmentCalls (ops : Fin M → Item w) (f : Assignment (fun i ↦ (ops i).owns)) :
    decodeAssignmentCalls ops (assignmentCalls ops f) = f := by
  funext i
  unfold decodeAssignmentCalls assignmentCalls
  rw [List.getElem?_append_left (by simp),
    List.getElem?_eq_getElem (by simp)]
  simp [Item.bits, bitAt, i.property]

/-- Restricting a total bit vector to the choose items produces the same
choice lists, since deterministic items consume no bits. -/
theorem assignmentCalls_restrict (ops : Fin M → Item w) (g : Fin M → Bool) :
    assignmentCalls ops (fun i ↦ g i.val) =
      (List.finRange M).map (fun i ↦ (ops i).bits (g i)) ++ [[]] := by
  unfold assignmentCalls
  congr 1
  apply List.map_congr_left
  intro i _
  cases h : (ops i).owns <;> simp [Item.bits, bitAt, h]

/-- The external probes of each scheduled item, fixed independently of the bits
and the words fetched from memory. -/
def Item.probeCount : Item w → ℕ
  | .skip => 0
  | .choose _ | .copy (.literal _) _ => 1
  | .copy (.fetch _) _ => 2

@[simp] theorem Item.probes_eq_probeCount (op : Item w) (bitWord : Bool → Word w)
    (next : Word w) (m : Memory w) (b : Bool) :
    (op.report bitWord next m b).probes = op.probeCount := by
  cases op with
  | skip | choose => rfl
  | copy src dst => cases src <;> rfl

/-- Cost of the data calls and the final one-unit halt. -/
def scheduledCost (ops : Fin M → Item w) : ℕ :=
  ((List.finRange M).map (fun i ↦ 1 + (ops i).probeCount)).sum + 1

theorem scheduledReports_cost (ops : Fin M → Item w) (bitWord : Bool → Word w)
    (fit : M < 2^w) (g : Fin M → Bool) (cells : List (Fin M)) (m : Memory w) :
    RAMBuckets.cost Report.probes (scheduledReports ops bitWord fit g cells m) =
      (cells.map (fun i ↦ 1 + (ops i).probeCount)).sum := by
  induction cells generalizing m with
  | nil => rfl
  | cons i cells ih => simp [scheduledReports, RAMBuckets.cost, ih]

theorem generated_cost (ops : Fin M → Item w) (bitWord : Bool → Word w)
    (fit : M < 2^w) (g : Fin M → Bool) (m : Memory w) :
    RAMBuckets.cost Report.probes (scheduledReports ops bitWord fit g (List.finRange M) m ++
      [haltReport w]) = scheduledCost ops := by
  rw [RAMBuckets.cost_append, scheduledReports_cost]
  rfl

private theorem scheduledReports_probes (ops : Fin M → Item w) (bitWord : Bool → Word w)
    (fit : M < 2^w) (g : Fin M → Bool) (cells : List (Fin M)) (m : Memory w) :
    ∀ r ∈ scheduledReports ops bitWord fit g cells m, r.probes ≤ 2 := by
  induction cells generalizing m with
  | nil => simp [scheduledReports]
  | cons i cells ih =>
    intro r hr
    rcases List.mem_cons.mp hr with rfl | ht
    · exact Item.report_probes ..
    · exact ih _ _ ht

/-- Both caps used by the parsimonious transcript construction hold whenever
the public cost fits the global budget and each site permits three units. -/
theorem scheduledReports_withinCaps (ops : Fin M → Item w) (bitWord : Bool → Word w)
    (fit : M < 2^w) (g : Fin M → Bool) (m : Memory w) {S H : ℕ}
    (hH : 3 ≤ H) (hTotal : scheduledCost ops ≤ S * H) :
    withinCaps S H (scheduledReports ops bitWord fit g (List.finRange M) m ++ [haltReport w]) := by
  constructor
  · rwa [generated_cost]
  · intro r hr
    rcases List.mem_append.mp hr with h | h
    · have := scheduledReports_probes ops bitWord fit g _ m r h
      omega
    · obtain rfl := List.mem_singleton.mp h
      change 1 + 0 ≤ H
      omega

/-- The native paths respecting a cap are in bijection with the independent
bits when all generated report sequences fit the cap. -/
def scheduledPathEquivOfCap (ops : Fin M → Item w) (bitWord : Bool → Word w)
    (fit : M < 2^w) (m : Memory w) (cap : List (Report w) → Prop)
    (hcap : ∀ g : Fin M → Bool, cap (scheduledReports ops bitWord fit g (List.finRange M) m ++
      [haltReport w])) :
    ActualPaths (scheduledProgram ops bitWord fit) 3 0 m cap ≃
      Assignment (fun i ↦ (ops i).owns) where
  toFun p := decodeAssignmentCalls ops p.val
  invFun f := ⟨assignmentCalls ops f, by
    have hr := run_generated ops bitWord fit (bitAt f) m
    refine ⟨_, hr, ?_, hcap (bitAt f)⟩
    rw [endState_append]
    rfl⟩
  left_inv p := by
    apply Subtype.ext
    change assignmentCalls ops (decodeAssignmentCalls ops p.val) = p.val
    obtain ⟨rs, hr, he, _⟩ := p.property
    obtain ⟨g, hg⟩ := (run_accepted_iff ops bitWord fit m p.val).mp ⟨rs, hr, he⟩
    rw [hg.trans (assignmentCalls_restrict ops g).symm, decode_assignmentCalls]
  right_inv f := decode_assignmentCalls ops f

/-- With no cost filter the interpreter enumerates every assignment once. -/
def scheduledPathEquiv (ops : Fin M → Item w) (bitWord : Bool → Word w)
    (fit : M < 2^w) (m : Memory w) :
    ActualPaths (scheduledProgram ops bitWord fit) 3 0 m (fun _ ↦ True) ≃
      Assignment (fun i ↦ (ops i).owns) :=
  scheduledPathEquivOfCap ops bitWord fit m _ (fun _ ↦ trivial)

/-- Exact enumeration by paths under the global and per-call RAM caps. -/
def scheduledPathEquivWithinCaps (ops : Fin M → Item w) (bitWord : Bool → Word w)
    (fit : M < 2^w) (m : Memory w) {S H : ℕ}
    (hH : 3 ≤ H) (hTotal : scheduledCost ops ≤ S * H) :
    ActualPaths (scheduledProgram ops bitWord fit) 3 0 m (withinCaps S H) ≃
      Assignment (fun i ↦ (ops i).owns) :=
  scheduledPathEquivOfCap ops bitWord fit m _ fun g ↦
    scheduledReports_withinCaps ops bitWord fit g m hH hTotal

end PrimedInputRAM

end VPVNP
end Computability
end OAI
