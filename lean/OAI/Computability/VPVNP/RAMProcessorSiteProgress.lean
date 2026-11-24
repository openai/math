import OAI.Computability.VPVNP.RAMProcessorLoopTests

/-!
# State and record accounting between bucket calls

The loop invariant retains the public template parameters and target cut,
the exact native continuation, the unconsumed guess suffix, and the full
list of records already emitted by the physical graph.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMTape.SiteProcessor

open BurstRAM PrivateRAM RAMSerialization

variable {w p r k : ℕ}

/-- Relate two call boundaries across a sequence of reports. The reports advance the cut, debit
the site credit and append exactly their timestamped probe records, with the specified
choice suffix. -/
structure Progress (s u : Snapshot w p r k) (old new : List (WordRecord w))
    (reports : List (Report w)) (tail : List Bool) : Prop where
  pub : u.pub = s.pub
  H : u.publicH = s.publicH
  fuel : u.publicFuel = s.publicFuel
  cap : u.cap = s.cap
  boundary : u.boundary = s.boundary
  target : u.tests.target = s.tests.target
  cut : u.tests.cut = s.tests.cut.advance reports
  siteLeft : u.siteLeft = s.siteLeft - RAMBuckets.cost Report.probes reports
  bits : u.choices = tail
  records : new.map WordRecord.record = old.map WordRecord.record ++ probeRecords s.cost.val reports

theorem Progress.nil (s : Snapshot w p r k) (rs : List (WordRecord w)) :
    Progress s s rs rs [] s.choices :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, (Cut.advance_nil _).symm, rfl, rfl, by simp [probeRecords]⟩

theorem Progress.append {s u v : Snapshot w p r k} {a b c : List (WordRecord w)}
    {xs ys : List (Report w)} {mid tail : List Bool}
    (hx : Progress s u a b xs mid) (hy : Progress u v b c ys tail) :
    Progress s v a c (xs++ys) tail := by
  refine ⟨hy.pub.trans hx.pub, hy.H.trans hx.H, hy.fuel.trans hx.fuel, hy.cap.trans hx.cap,
    hy.boundary.trans hx.boundary, hy.target.trans hx.target, ?_, ?_, hy.bits, ?_⟩
  · rw [Cut.advance_append, ← hx.cut, hy.cut]
  · rw [hy.siteLeft, hx.siteLeft, Nat.sub_sub, RAMBuckets.cost_append]
  · have hc : u.cost.val = s.cost.val + RAMBuckets.cost Report.probes xs := congrArg Cut.cost hx.cut
    rw [hy.records, hx.records, probeRecords_append, hc, List.append_assoc]

/-- Run one charged call of the instantiated program from the snapshot's persistent state using
its public fuel and remaining global and site credit. -/
def nativeCall (T : Template p r k) (s : Snapshot w p r k) : Option (Report w × List Bool) :=
  let P := (T.instantiate w s.pub).program
  (runChargedCall P s.publicFuel (P.start s.cfg.persistent) s.publicH
    (s.cap.val-s.cost.val) s.siteLeft s.choices).output

/-- Run the native site loop with the supplied iteration bound, starting at the snapshot's cut
with its site credit and remaining choices. -/
def nativeLoop (T : Template p r k) (n : ℕ) (s : Snapshot w p r k) :=
  runSiteLoop (T.instantiate w s.pub).program s.publicFuel s.publicH s.boundary.val
    s.cap.val n s.tests.cut s.siteLeft s.choices

theorem nativeLoop_next (T : Template p r k) {s u : Snapshot w p r k} {xs ys : List (WordRecord w)}
    {rep : Report w} {tail : List Bool} (h : Progress s u xs ys [rep] tail) (n : ℕ) :
    nativeLoop T n u = runSiteLoop (T.instantiate w s.pub).program s.publicFuel s.publicH s.boundary.val
      s.cap.val n (s.tests.cut.advance [rep]) (s.siteLeft-(1+rep.probes)) tail := by
  unfold nativeLoop
  rw [h.pub, h.fuel, h.H, h.boundary, h.cap, h.cut, h.siteLeft, h.bits]
  simp [RAMBuckets.cost]

/-- Type of a predicate on a site snapshot and the chronological word records accumulated at a
call boundary. -/
abbrev BoundaryInvariant (w p r k : ℕ) := Snapshot w p r k → List (WordRecord w) → Prop

/-- A complete graph run either reaches its next public label with the
indicated records and exact report stream, or reaches an actual rejecting row. -/
def LoopRun (T : Template p r k) (ready : BoundaryInvariant w p r k) (l next : Label p r)
    (s : Snapshot w p r k) (records : List (WordRecord w)) (t : ℕ)
    (native : Option (List (Report w) × List Bool)) : Prop :=
  match native with
  | none => RejectRun (table T) t (atLabel T l) s.bank
  | some (rs, tail) => ∃ u suffix, ready u suffix ∧ Progress s u records suffix rs tail ∧
      StackRuns (table T) t (atLabel T l) s.bank (atLabel T next) u.bank

theorem LoopRun.prepend {T : Template p r k} {ready : BoundaryInvariant w p r k} {l mid next}
    {s : Snapshot w p r k} {records : List (WordRecord w)} {a b : ℕ} {native}
    (h : StackRuns (table T) a (atLabel T l) s.bank (atLabel T mid) s.bank)
    (hr : LoopRun T ready mid next s records b native) :
    LoopRun T ready l next s records (a+b) native := by
  cases native with
  | none => exact h.thenReject hr
  | some z =>
    obtain ⟨rs, tail⟩ := z
    obtain ⟨u, ys, hu, hp, run⟩ := hr
    exact ⟨u, ys, hu, hp, h.trans run⟩

theorem LoopRun.prependReport {T : Template p r k} {ready : BoundaryInvariant w p r k}
    {s u : Snapshot w p r k} {xs ys : List (WordRecord w)} {rep : Report w} {rest}
    {l mid next} {a b : ℕ} {native : Option (List (Report w) × List Bool)}
    (h : StackRuns (table T) a (atLabel T l) s.bank (atLabel T mid) u.bank)
    (hp : Progress s u xs ys [rep] rest) (hr : LoopRun T ready mid next u ys b native) :
    LoopRun T ready l next s xs (a+b) (native.map fun (rs, tail) => (rep :: rs, tail)) := by
  cases native with
  | none => exact h.thenReject hr
  | some z =>
    obtain ⟨rs, tail⟩ := z
    obtain ⟨v, zs, hv, hs, run⟩ := hr
    exact ⟨v, zs, hv, hp.append hs, h.trans run⟩

end RAMTape.SiteProcessor

end VPVNP
end Computability
end OAI
