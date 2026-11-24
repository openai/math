import OAI.Computability.VPVNP.LiveProgramHandoffs
import OAI.Computability.VPVNP.LiveProgramPairStages

/-!
# The live unit branch after header verification

Once the physical header has checked both modes and every padding bit, the
unit group has one possible sequence of native bursts. The last burst costs
three units, including the outer tag read and the checked mode read.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace LiveProgram.UnitGroup
open BurstRAM BurstRAM.PrivateRAM PairStages

variable (G : Group)

/-- Terminating report of the unit-mode router after header verification, with one outer tag
read and one mode read. -/
def report : Report G.w := Router.mode.outerReport G.evaluator G.g G.lit
  (Router.mode.haltReport G.g G.lit 0 0)

theorem report_result : (report G).result = none := rfl

theorem report_probes : (report G).probes = 2 := rfl

theorem cap_iff (S H : ℕ) (header : List (Report G.w)) :
    withinCaps S H (header++[report G]) ↔
      RAMBuckets.cost Report.probes header + 3 ≤ S*H ∧
      (∀ r ∈ header, 1+r.probes ≤ H) ∧ 3 ≤ H := by
  simp [withinCaps,RAMBuckets.cost,report_probes,or_imp,forall_and]

/-- The conclusion records every native report, as well as the entire
choice stream. It holds at the same clock that executed the header. -/
theorem run {n : ℕ} {m : Memory G.w} {logs : List (Report G.w)}
    (hw : 2 ≤ G.w) (hc : 57 ≤ G.clock) (hr : runSegment G.P G.clock (some 0) m (List.replicate n []) = some logs)
    (hcontinue : endState (some 0) logs = some 0)
    (mode : (after m (eventLog logs)) ((Router.mode.data G.g G.lit) 0).val = 0)
    (tagged : G.tagged Stage.mode (after m (eventLog logs))) :
    runSegment G.P G.clock (some 0) m (List.replicate (n+1) []) = some (logs ++ [report G]) ∧
      endState (some 0) (logs ++ [report G]) = none := by
  have hex := (Router.unit_accept_iff G.constants G.evaluator G.pair G.g G.lit G.tagFit hw
    (fun rs => rs = [report G]) G.clock hc 0 (after m (eventLog logs)) mode tagged [[]]).2 ⟨rfl,rfl⟩
  obtain ⟨_,ht,_,rfl⟩ := hex
  constructor
  · rw [List.replicate_add,PrimedSchedule.runSegment_append,hr]
    simp only [Option.bind_some,hcontinue,show List.replicate 1 ([] : List Bool) = [[]] by rfl,G.program_eq,ht,Option.map_some]
  · rw [endState_append,hcontinue]; exact report_result G

/-- Arbitrary valid choice streams in unit mode agree with the unique forced
trace, even if the cap examines every report rather than just the total cost. -/
theorem accepted_iff {n : ℕ} {m : Memory G.w} {logs : List (Report G.w)}
    (hw : 2 ≤ G.w) (hc : 57 ≤ G.clock) (hr : runSegment G.P G.clock (some 0) m (List.replicate n []) = some logs)
    (hcontinue : endState (some 0) logs = some 0)
    (mode : (after m (eventLog logs)) ((Router.mode.data G.g G.lit) 0).val = 0)
    (tagged : G.tagged Stage.mode (after m (eventLog logs))) (cap : List (Report G.w) → Prop) (bs : List (List Bool)) :
    (∃ rs, runSegment G.P G.clock (some 0) m bs = some rs ∧ endState (some 0) rs = none ∧ cap rs) ↔
      bs = List.replicate (n+1) [] ∧ cap (logs++[report G]) := by
  obtain ⟨full,done⟩ := run G hw hc hr hcontinue mode tagged
  constructor
  · rintro ⟨rs,h,hh,hcap⟩
    obtain ⟨hbs,rfl⟩ := accepted_empty_unique full done h hh
    exact ⟨hbs,hcap⟩
  · rintro ⟨rfl,h⟩; exact ⟨_,full,done,h⟩

/-- A valid unit group contributes the integer one at every permitted clock
and resource cap covering its verified trace. -/
theorem card_one {n : ℕ} {m : Memory G.w} {logs : List (Report G.w)}
    (hw : 2 ≤ G.w) (hc : 57 ≤ G.clock) (hr : runSegment G.P G.clock (some 0) m (List.replicate n []) = some logs)
    (hcontinue : endState (some 0) logs = some 0)
    (mode : (after m (eventLog logs)) ((Router.mode.data G.g G.lit) 0).val = 0)
    (tagged : G.tagged Stage.mode (after m (eventLog logs))) (cap : List (Report G.w) → Prop)
    (hcap : cap (logs++[report G])) : Nat.card (ActualPaths G.P G.clock 0 m cap) = 1 := by
  apply Nat.card_eq_one_iff_exists.mpr
  let eqv := accepted_iff G hw hc hr hcontinue mode tagged cap
  refine ⟨⟨_, (eqv _).2 ⟨rfl,hcap⟩⟩,?_⟩
  intro y; exact Subtype.ext ((eqv y.val).1 y.property).1

end LiveProgram.UnitGroup

end VPVNP
end Computability
end OAI
