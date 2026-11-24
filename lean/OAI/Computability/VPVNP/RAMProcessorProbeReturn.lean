import OAI.Computability.VPVNP.RAMProcessorPending

/-!
# Splicing a permitted external probe into a completed call

A successful probe contributes one unit of cost and one chronologically
stamped record. A later rejection remains a rejection even when earlier
probes wrote records into the site's private buffer.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMTape.SiteProcessor

open BurstRAM PrivateRAM RAMSerialization

variable {w p r k H F : ℕ} {hw : 2 ≤ w}

/-- Accounting needed to prepend an admitted probe to a call return. It relates the two
snapshots' budgets and identifies the charged event's timestamped record ahead of the
continuation. -/
structure ProbeLink (s u : Snapshot w p r k) (record : WordRecord w) (e : Event w)
    (start ord nextOrd : Word w) : Prop where
  pub : u.pub = s.pub
  H : u.publicH = s.publicH
  fuelCap : u.publicFuel = s.publicFuel
  cap : u.cap = s.cap
  boundary : u.boundary = s.boundary
  target : u.tests.target = s.tests.target
  cost : u.cost.val = s.cost.val+1
  siteLeft : u.siteLeft = s.siteLeft-1
  eventCharge : ∀ xs, countProbes (e::xs) = 1+countProbes xs
  recordHead : ∀ xs, eventRecords start.val ord.val (e::xs) =
    record.record :: eventRecords start.val nextOrd.val xs

theorem CallReturn.afterProbe {s u v : Snapshot w p r k} {rec e start ord nextOrd ys zs rep tail}
    (link : ProbeLink s u rec e start ord nextOrd)
    (ret : CallReturn u v (ys++[rec]) zs start nextOrd rep tail) :
    CallReturn s v ys zs start ord (rep.prepend e) tail := by
  refine ⟨ret.pub.trans link.pub, ret.H.trans link.H, ret.fuel.trans link.fuelCap,
    ret.cap.trans link.cap, ret.boundary.trans link.boundary, ret.target.trans link.target, ?_,
    ret.state, ?_, ret.bits, ?_⟩
  · simpa only [Report.prepend, Report.probes, link.eventCharge, link.cost, Nat.add_assoc] using ret.cost
  · simpa only [Report.prepend, Report.probes, link.eventCharge, link.siteLeft, Nat.sub_sub] using ret.siteLeft
  · simpa only [Report.prepend, link.recordHead, List.map_append, List.map_cons, List.map_nil,
      List.append_assoc, List.cons_append, List.nil_append] using ret.records

theorem probe_then_segment (T : Template p r k) {s u : Snapshot w p r k} {ys rec start ord nextOrd e cb d t}
    (step : StackRuns (table T) d (atLabel T (.callback cb)) s.bank (atLabel T (.segment u.cfg.pc)) u.bank)
    (link : ProbeLink s u rec e start ord nextOrd)
    (eqout : pending T s cb = LocalProcessor.addEvent e
      (runLocalCall (T.instantiate w u.pub).logProgram u.fuel u.cfg (allowance u) u.choices).output)
    (tail : SegmentRun T hw H F u (ys++[rec]) start nextOrd t) :
    Meets T hw H F s ys start ord (.callback cb) (pending T s cb) (d+t) := by
  rw [eqout]
  let out := (runLocalCall (T.instantiate w u.pub).logProgram u.fuel u.cfg (allowance u) u.choices).output
  change Meets T hw H F u (ys++[rec]) start nextOrd (.segment u.cfg.pc) out t at tail
  change Meets T hw H F s ys start ord (.callback cb) (LocalProcessor.addEvent e out) (d+t)
  cases he : out with
  | none => rw [he] at tail; exact step.thenReject tail
  | some z =>
    obtain ⟨rep,bs⟩ := z
    rw [he] at tail
    obtain ⟨v,zs,ready,ret,run⟩ := tail
    exact ⟨v, zs, ready, ret.afterProbe link, step.trans run⟩

end RAMTape.SiteProcessor

end VPVNP
end Computability
end OAI
