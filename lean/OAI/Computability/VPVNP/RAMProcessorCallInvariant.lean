import OAI.Computability.VPVNP.RAMProcessorSiteClose
import OAI.Computability.VPVNP.RAMProcessorGraphStart

/-!
# Bounds at the physical call boundary

A charge transfers one unit from the remaining global credit to the cumulative
cost. The private log and unspent fuel together remain bounded by the public
call clock. Every future probe therefore has room in the record buffer before
it is staged.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMTape.SiteProcessor

open BurstRAM PrivateRAM RAMSerialization

variable {w p r k : ℕ}

/-- Site-controller invariant at a call boundary, tracking the buffered records, public limits,
remaining credits, private clock and scratch-word lengths. -/
structure CallReady (hw : 2 ≤ w) (H F : ℕ) (first : Bool) (s : Snapshot w p r k)
    (ys : List (WordRecord w)) : Prop where
  publicH : s.publicH = H
  publicFuel : s.publicFuel = F
  positive : 0 < H
  boundary : s.boundary.val ≤ s.cap.val
  room : ys.length + s.siteLeft ≤ 4*H
  buffer : RecordBuffer.Holds hw H ys s.records
  privateClock : s.cfg.writes.length + s.fuel ≤ F
  callCredit : s.callLeft ≤ H
  saved : s.savedStart.length ≤ w
  ordinal : s.ordinal.length ≤ w
  tag : s.tag.length ≤ w
  address : s.address.length ≤ w
  value : s.value.length ≤ w
  global : first = false → s.globalLeft.val + s.cost.val = s.cap.val
  firstCredit : first = true → 0 < s.siteLeft

/-- Call-boundary invariant strengthened with the saved start and probe ordinal. The current
cost is the start plus one startup charge and the ordinal. -/
structure InCall (hw : 2 ≤ w) (H F : ℕ) (s : Snapshot w p r k) (ys : List (WordRecord w))
    (start ord : Word w) : Prop extends CallReady hw H F false s ys where
  savedEq : s.savedStart = BurstRAM.wordBits start
  ordinalEq : s.ordinal = BurstRAM.wordBits ord
  timestamp : start.val+(1+ord.val) = s.cost.val

theorem CallReady.toHolds {s : Snapshot w p r k} {hw : 2 ≤ w} {H F : ℕ} {first records}
    (h : CallReady hw H F first s records) : RecordBuffer.Holds hw s.publicH records s.records :=
  h.publicH ▸ h.buffer

/-- Stack-step allowance for one segment of private instructions between external actions, as a
function of the word width and call clock. -/
def segmentWork (w F : ℕ) : ℕ := (F+1)*(ISA.prepareBound w F+4)+200*(w+1)
/-- Stack-step allowance for an entire metered call, reserving `F + 1` segments at the
per-segment bound. -/
def callWork (w F : ℕ) : ℕ := (F+1)*segmentWork w F

/-- One returned segment preserves the public bank and records, and reports
the extra probes of the current call with their original startup time and
the ordinals immediately following those already emitted. -/
structure CallReturn (s u : Snapshot w p r k) (old new : List (WordRecord w))
    (start ord : Word w) (rep : Report w) (tail : List Bool) : Prop where
  pub : u.pub = s.pub
  H : u.publicH = s.publicH
  fuel : u.publicFuel = s.publicFuel
  cap : u.cap = s.cap
  boundary : u.boundary = s.boundary
  target : u.tests.target = s.tests.target
  cost : u.cost.val = s.cost.val + rep.probes
  state : u.tests.cut.state = rep.result
  siteLeft : u.siteLeft = s.siteLeft - rep.probes
  bits : u.choices = tail
  records : new.map WordRecord.record = old.map WordRecord.record ++ eventRecords start.val ord.val rep.events

/-- The linked site controller rejects when local call execution fails, or returns to its
iteration test with the corresponding report, residual choices and buffered records. -/
def SegmentRun (T : Template p r k) (hw : 2 ≤ w) (H F : ℕ) (s : Snapshot w p r k)
    (ys : List (WordRecord w)) (start ord : Word w) (t : ℕ) : Prop :=
  match (runLocalCall (T.instantiate w s.pub).logProgram s.fuel s.cfg
      (min s.callLeft (min s.globalLeft.val s.siteLeft)) s.choices).output with
  | none => RejectRun (table T) t (atLabel T (.segment s.cfg.pc)) s.bank
  | some (rep,tail) => ∃ u new, CallReady hw H F false u new ∧ CallReturn s u ys new start ord rep tail ∧
      StackRuns (table T) t (atLabel T (.segment s.cfg.pc)) s.bank (atLabel T .iteration) u.bank

end RAMTape.SiteProcessor

end VPVNP
end Computability
end OAI
