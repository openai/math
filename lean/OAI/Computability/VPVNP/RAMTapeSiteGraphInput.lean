import OAI.Computability.VPVNP.RAMTapeSiteCutSnapshot
import OAI.Computability.VPVNP.RAMTapeVirtualSiteGraph

/-!
# The call graph on the parsed site's own incoming and outgoing fields

The controller first emits the compulsory local initialization record. From
that bank the call loop tests its incoming cost bucket, simulates the private
instructions, checks the outgoing cut and closes the ordered record buffer.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMTape.SiteCutBank

open BurstRAM PrivateRAM RAMSerialization SiteProcessor

variable {d e w p r k : ℕ} (x : Input d e w) (T : Template p r k) (pub : Fin k → Word w) (bits : List Bool)

/-- Compulsory first record built from the parsed address and header words. -/
def Input.initSlot := SiteProcessor.initRecord x.addrWord x.headerWord

/-- Controller snapshot after fresh-call initialization and staging the address for the
compulsory record. -/
def Input.staged : Snapshot w p r k := ((x.bare T pub bits).afterFresh T).withInitFields x.addrWord

/-- Controller snapshot immediately after emitting the site’s compulsory initialization record. -/
def Input.entered : Snapshot w p r k := (x.staged T pub bits).afterEmit x.word_ge_two x.initSlot

theorem Input.init_run :
    StackRuns (table T) (25*w+12) (atLabel T .initialRecord) (x.staged T pub bits).bank
      (atLabel T .checkEntry) (x.entered T pub bits).bank ∧
    RecordBuffer.Holds x.word_ge_two (2^e) [x.initSlot] (x.entered T pub bits).records :=
  initialRecord_run T ((x.bare T pub bits).afterFresh T) x.word_ge_two x.addrWord x.headerWord
    rfl rfl rfl rfl rfl (Nat.two_pow_pos _)

theorem Input.entered_ready :
    CallReady x.word_ge_two (2^e) (x.n^x.u) true (x.entered T pub bits) [x.initSlot] :=
  x.asWordSite.entered_ready T pub bits

/-- Abstract site validation for the instantiated program, actual incoming and outgoing
summaries, and the given private choice bits. -/
def Input.validated :=
  validateSite (T.instantiate w pub).program (x.n^x.u) (2^d) (2^e) x.v.val
    x.summary.input x.summary.output bits

/-- Budget for initial-record emission, all bounded site calls, and closing the padded record
buffer. -/
def graphBudget (r w e fuel : ℕ) : ℕ :=
  25*w+12+siteWork w (2^e) (perCallEstimate r w (2^e) fuel)+closeWork w (2^e)

/-- Execution outcome matching abstract site validation. Failure reaches rejection, and success
closes the initialization record followed by the probes in order. -/
def Input.GraphOutcome (t : ℕ) : Prop :=
  match x.validated T pub bits with
  | none => RejectRun (table T) t (atLabel T .initialRecord) (x.staged T pub bits).bank
  | some rs => ∃ (u : Snapshot w p r k) (ys : List (WordRecord w)), ys.map WordRecord.record =
      x.initSlot.record :: probeRecords x.summary.input.cost rs ∧
      StackRuns (table T) t (atLabel T .initialRecord) (x.staged T pub bits).bank
        (atLabel T .done) (u.afterClose x.word_ge_two (2^e) ys).bank

end RAMTape.SiteCutBank

end VPVNP
end Computability
end OAI
