import OAI.Computability.VPVNP.RAMProcessorState
import OAI.Computability.VPVNP.RAMProcessorReset
import OAI.Computability.VPVNP.RAMProcessorProbeStages
import OAI.Computability.VPVNP.RAMProcessorSiteTestsFlow

/-!
# The fixed stack table for a complete burst site

On entry the initialization record is staged and the parser has supplied the
local header, cuts and public budgets. Every call starts with fresh registers
and private log. Each probe first pays its unit, then stages its record, emits
it, and increments the ordinal. A returning call either starts another call
in this bucket or finishes the site. The normal exit exposes the padded record
block to the local bitonic and memory checks.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMTape

namespace Fragment

variable {K L M : Type}

/-- Apply a continuation-label map to every normal exit of a fragment. -/
def mapExits (f : Fragment K L) (g : L → M) : Fragment K M :=
  ⟨f.State, f.entry, fun q => (f.code q).rename id (Sum.map id g)⟩

theorem runs_mapExits [DecidableEq K] {f : Fragment K L} (g : L → M)
    {t s exit out} (h : f.Runs t s exit out) :
    (f.mapExits g).Runs t s (g exit) out := by
  have hi (x : Stacks K) : installStacks id s x = x := by
    funext j; exact installStacks_at Function.injective_id s x j
  have hr := h.lift id Function.injective_id (Sum.map id g) s (target := (f.mapExits g).isolated)
    (by intro q hq; cases q with | inl _ => rfl | inr _ => contradiction)
  change StackRuns (f.mapExits g).isolated t (.inl f.entry) s (.inr (g exit)) out
  change StackRuns (f.mapExits g).isolated t (.inl f.entry) (installStacks id s s) (.inr (g exit)) (installStacks id s out) at hr
  simpa only [hi] using hr

end Fragment

namespace SiteProcessor

open BurstRAM PrivateRAM

/-- Locations in the site's call, probe, record and acceptance graph. -/
inductive Label (p r : ℕ) where
  | initialRecord | checkEntry | first | newCall | fresh
  | segment (pc : Fin p)
  | callback (cb : ISA.Callback p r)
  | read (dst addr : Fin r) (next : Fin p)
  | write (addr src : Fin r) (next : Fin p)
  | emit (next : Fin p) | increment (next : Fin p)
  | iteration | finalCheck | close | done | reject
  deriving Fintype

variable {p r k : ℕ}

/-- Select the first call, a subsequent call, the final check or rejection. -/
def route (first : Bool) : SiteTests.Exit → Label p r
  | .reject => .reject
  | .dispatch => if first then .first else .newCall
  | .finish => .finalCheck

/-- Fixed jump graph, instantiated once from a literal-width call template. -/
def blocks (T : Template p r k) : Label p r → Fragment (Port r k) (Label p r)
  | .initialRecord => (Fragment.returning RecordBuffer.appendRecord .checkEntry).onPorts recordPorts
  | .checkEntry => (SiteTests.entry.fragment (route true)).onPorts testPorts
  | .first => (Fragment.returning CallCredit.firstCall .fresh).onPorts Port.credit
  | .newCall => (Fragment.returning CallCredit.startCall .fresh).onPorts Port.credit
  | .fresh => (Fragment.returning (ISA.freshCall (r := r) (k := k)) (.segment T.entry)).onPorts Port.isa
  | .segment pc => (localBlock T pc).mapExits Label.callback
  | .callback (.read dst addr next) => (Fragment.returning CallCredit.prepareProbe (.read dst addr next)).onPorts Port.credit
  | .callback (.write addr src next) => (Fragment.returning CallCredit.prepareProbe (.write addr src next)).onPorts Port.credit
  | .read dst addr next => (ProbeStages.read dst addr (.emit next) .reject).onPorts probePorts
  | .write addr src next => (Fragment.returning (ProbeStages.writePayload addr src) (.emit next)).onPorts probePorts
  | .emit next => (Fragment.returning RecordBuffer.appendRecord (.increment next)).onPorts recordPorts
  | .increment next => (Fragment.returning CallCredit.finishProbe (.segment next)).onPorts Port.credit
  | .callback (.returnState src) => (Fragment.returning (ProbeStages.returnState src) .iteration).onPorts probePorts
  | .callback .accept => (Fragment.returning (ProbeStages.accept (r := r) (k := k)) .iteration).onPorts probePorts
  | .callback _ => Fragment.direct (.goto .reject)
  | .iteration => (SiteTests.iteration.fragment (route false)).onPorts testPorts
  | .finalCheck => (SiteTests.finalCheck.fragment (fun e => if e = .finish then .close else .reject)).onPorts testPorts
  | .close => (Fragment.returning RecordBuffer.close .done).onPorts recordPorts
  | .done => Fragment.direct (.halt true)
  | .reject => Fragment.direct (.halt false)

/-- The finite control type obtained by linking the site's fragments. -/
abbrev Control (T : Template p r k) := ProcessorFlow.State (blocks T)

/-- The executable stack instruction table for a fixed RAM template. -/
def table (T : Template p r k) : StackCode (Port r k) (Control T) :=
  ProcessorFlow.program (blocks T)

/-- Enter the fragment belonging to a site graph location. -/
def atLabel (T : Template p r k) (l : Label p r) : Control T := ProcessorFlow.enter (blocks T) l

@[simp] theorem done_row (T : Template p r k) : table T (atLabel T .done) = .halt true := rfl
@[simp] theorem reject_row (T : Template p r k) : table T (atLabel T .reject) = .halt false := rfl

/-- Physical execution of a segment of the actual graph, including its fuel
and choice cutoffs. -/
theorem segment_run {w : ℕ} (T : Template p r k) (s : Snapshot w p r k) (limit : ℕ)
    (hl : s.cfg.writes.length+s.fuel ≤ limit) :
    let y := LocalProcessor.scan T s.pub s.fuel s.cfg s.choices
    ∃ t ≤ s.fuel*(ISA.prepareBound w limit+4)+1,
      StackRuns (table T) t (atLabel T (.segment s.cfg.pc)) s.bank
        (atLabel T (.callback y.exit)) (s.afterLocal y).bank := by
  obtain ⟨t, ht, h⟩ := s.runLocal T limit hl
  exact ⟨t, ht, ProcessorFlow.run (blocks := blocks T) (l := Label.segment s.cfg.pc) (Fragment.runs_mapExits Label.callback h)⟩

end SiteProcessor
end RAMTape

end VPVNP
end Computability
end OAI
