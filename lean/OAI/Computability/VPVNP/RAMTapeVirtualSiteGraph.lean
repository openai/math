import OAI.Computability.VPVNP.RAMTapeVirtualSite
import OAI.Computability.VPVNP.RAMProcessorCallRun
import OAI.Computability.VPVNP.RAMProcessorInitRun
import OAI.Computability.VPVNP.RAMProcessorChargedRun

/-!
# The call graph on the parsed site's own incoming and outgoing fields

The controller emits a full-word initialization record for its auxiliary site. From
that bank the call loop tests its incoming cost bucket, simulates the private
instructions, checks the outgoing cut and closes the ordered record buffer.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMTape.VirtualSite

open BurstRAM PrivateRAM RAMSerialization SiteProcessor

variable {d e w p r k : ℕ} (x : Input d e w) (T : Template p r k) (pub : Fin k → Word w) (bits : List Bool)

/-- Initialization record for the actual auxiliary site's address and header word. -/
def Input.initSlot := SiteProcessor.initRecord x.addrWord x.headerWord

/-- Fresh processor snapshot with its initialization fields in place. -/
def Input.staged : Snapshot w p r k := ((x.bare T pub bits).afterFresh T).withInitFields x.addrWord

/-- Snapshot after the native graph emits its first memory record. -/
def Input.entered : Snapshot w p r k := (x.staged T pub bits).afterEmit x.hw x.initSlot

theorem Input.init_run :
    StackRuns (table T) (25*w+12) (atLabel T .initialRecord) (x.staged T pub bits).bank
      (atLabel T .checkEntry) (x.entered T pub bits).bank ∧
    RecordBuffer.Holds x.hw (2^e) [x.initSlot] (x.entered T pub bits).records :=
  initialRecord_run T ((x.bare T pub bits).afterFresh T) x.hw x.addrWord x.headerWord
    rfl rfl rfl rfl rfl (Nat.two_pow_pos _)

theorem Input.entered_ready :
    CallReady x.hw (2^e) x.fuel true (x.entered T pub bits) [x.initSlot] := by
  have hp := Nat.two_pow_pos e
  refine ⟨rfl,rfl,hp,?_,?_,(x.init_run T pub bits).2,Nat.zero_le _,Nat.zero_le _,?_,?_,?_,?_,?_,nofun,?_⟩
  · exact Nat.mul_le_mul_right _ x.v.isLt
  · change 1+(2*2^e-1) ≤ 4*2^e
    omega
  · exact (length_wordBits _).le
  · exact (length_wordBits _).le
  · exact (length_wordBits _).le
  · exact (length_wordBits _).le
  · exact (length_wordBits _).le
  · intro _
    change 0 < 2*2^e-1
    omega

/-- Auxiliary site reports accepted on the nominated private choice string. -/
def Input.validated :=
  validateSite (T.instantiate w pub).program x.fuel (2^d) (2^e) x.v.val
    x.summary.input x.summary.output bits

/-- Work bound for initialization, interpreting all calls and closing the site. -/
def graphBudget (r w e fuel : ℕ) : ℕ :=
  25*w+12+siteWork w (2^e) (perCallEstimate r w (2^e) fuel)+closeWork w (2^e)

/-- Acceptance or rejection of the actual stack graph on the supplied private choices. -/
def Input.GraphOutcome (t : ℕ) : Prop :=
  match x.validated T pub bits with
  | none => RejectRun (table T) t (atLabel T .initialRecord) (x.staged T pub bits).bank
  | some rs => ∃ (u : Snapshot w p r k) (ys : List (WordRecord w)), ys.map WordRecord.record =
      x.initSlot.record :: probeRecords x.summary.input.cost rs ∧
      StackRuns (table T) t (atLabel T .initialRecord) (x.staged T pub bits).bank
        (atLabel T .done) (u.afterClose x.hw (2^e) ys).bank

theorem Input.graphOutcome_of_start
    (start : StartRuns T (CallReady x.hw (2^e) x.fuel) (perCallEstimate r w (2^e) x.fuel)) :
    ∃ t ≤ graphBudget r w e x.fuel, x.GraphOutcome T pub bits t := by
  let s := x.entered T pub bits
  obtain ⟨b,hb,hr⟩ := checkEntry_close start x.hw (fun _ _ _ h => h.toHolds) s [x.initSlot]
    (x.entered_ready T pub bits) (2^d) x.v.val rfl rfl rfl rfl
  have hc : s.tests.cut = x.summary.input := x.bare_cut T pub bits
  have ht : s.tests.target = x.summary.output := x.bare_target T pub bits
  rw [hc, ht] at hr
  change ClosedRun T x.hw s [x.initSlot] .checkEntry b (x.validated T pub bits) at hr
  have init := (x.init_run T pub bits).1
  change b ≤ siteWork w (2^e) (perCallEstimate r w (2^e) x.fuel)+closeWork w (2^e) at hb
  refine ⟨25*w+12+b, by unfold graphBudget; omega, ?_⟩
  unfold Input.GraphOutcome
  cases he : x.validated T pub bits with
  | none => rw [he] at hr; exact init.thenReject hr
  | some rs =>
    rw [he] at hr
    obtain ⟨u, ys, hp, run⟩ := hr
    have hcost : s.cost.val = x.summary.input.cost := congrArg Cut.cost hc
    have records := hp.records
    rw [hcost] at records
    exact ⟨u,ys,records,init.trans run⟩

theorem Input.graphOutcome :
    ∃ t ≤ graphBudget r w e x.fuel, x.GraphOutcome T pub bits t :=
  x.graphOutcome_of_start T pub bits (startRuns_of_segments T (segment_correct T))

end RAMTape.VirtualSite

end VPVNP
end Computability
end OAI
