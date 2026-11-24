import OAI.Computability.VPVNP.PairRefreshHookOrigin
import OAI.Computability.VPVNP.PairRefreshHookRecover
import OAI.Computability.VPVNP.PairRefreshHookEffect
import OAI.Computability.VPVNP.PairRefreshTraversalQuiet
import OAI.Computability.VPVNP.PairTreeEmissions

/-!
# The physical refresh job and its selected term

A prepared parent supplies the same newer argument to the physical and
semantic readers. For the emitted job the natural counter increments are
the exponents of the selected kernel witness. The unique child packet and
the pending siblings satisfy the budgeted frontier after that job.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.RefreshHook.Site

open BurstRAM PrivateRAM Compression Compression.Refresh Compression.DegreeRefresh
open CompressorRecords CompressorRecords.PortRefresh NewSlots NodeArguments NodeArguments.ChildScan
open LocalHistory TreeDecode VertexImage DFS NetworkKernel LeafSourceLoad
open scoped Fin.CommRing

variable {k : Type} [_root_.Field k] {S : BlockSchedule k} {B : S.Templates} {bits n hist t : ℕ}
  (R : Site B n hist bits) (ties : Fin t ≃ Tie (2^S.portExponent)) (stride : ℕ) (order : B.Entry ≃ Fin hist)
  (pub : Fin 11 → BurstRAM.Word bits) (m : Memory bits)
variable {K : Type*} [CommRing K] (f : B.Entry → K) (hf : B.IsSolution f)
local notation "reader" => originReader B f hf (PassOrigin.refresh R.state) R.choice
local notation "site" => R.newerSite
local notation "parent" => R.parent
local notation "base" => R.regions.histBase
local notation "H" => privateHistogram order.symm base
local notation "hook" => R.hook ties stride order pub m

variable (new : R.nextState.network.Half R.newerSite)
  (data : Fin 10 → BurstRAM.Word bits) (offset : BurstRAM.Word bits) (vals : Static 34 → BurstRAM.Word bits)
  (format : Packet → Prop) (desc : ℕ → List ℕ) (nodeCap limit : ℕ)
  (pending : List Packet) (s : Scratch bits n)
local notation "head" => Packet.mk parent (packed R.nextState site new)
local notation "valid" => Budgeted R.arena format (VertexFrameData R.regions data offset vals) desc H nodeCap limit
local notation "assignment" => Placed (TraversalPlan.place R.state) R.state.network.Half site
local notation "oldAt" => (fun before : assignment =>
  before R.olderSite (TraversalPlan.old_place R.state R.port))
local notation "child" => (fun before : assignment => packet R.state R.olderSite R.oldNode (oldAt before))
local notation "bitsOf" => TermParsers.nodeBits (reader) site
local notation "seen" => TermParsers.witness (reader) site

variable (ready : Budgeted R.arena format (VertexFrameData R.regions data offset vals) desc
    (privateHistogram order.symm R.regions.histBase) nodeCap limit
    (Packet.mk R.parent (packed R.nextState R.newerSite new)::pending) s)
  (hw : 0 < bits)
  (shape : ∀ before : Placed (TraversalPlan.place R.state) R.state.network.Half R.newerSite,
    desc R.parent = subtreeAddresses desc (packet R.state R.olderSite R.oldNode
      (before R.olderSite (TraversalPlan.old_place R.state R.port))))
  (typed : ∀ before : Placed (TraversalPlan.place R.state) R.state.network.Half R.newerSite,
    format (packet R.state R.olderSite R.oldNode (before R.olderSite (TraversalPlan.old_place R.state R.port))))
  (nodeBound : ∀ q, format q → q.node < R.rowEnd) (positive : 0 < R.oldNode)
  (cacheFit : R.regions.cacheBase+38 ≤ 2^bits) (limitFit : limit < 2^bits) (capFit : n ≤ nodeCap)

include ready hw shape typed nodeBound positive cacheFit limitFit capFit in
set_option maxHeartbeats 1500000 in
theorem origin_effect (before : Placed (TraversalPlan.place R.state) R.state.network.Half site)
    (w : (seen before new).Choice) (tail : List Bool) (job : VisitPath bits n)
    (read : (hook).read (parent : BurstRAM.Word bits) s (bitsOf before new w ++ tail) = some (job,tail)) :
    RealizesJob H ⟨parent,bitsOf before new w,(seen before new).exponents w⟩ job ∧
      job.enabled s ∧ valid (child before::pending) (job.update s) := by
  have hp := RefreshHalfDecoder.parent_eq R.nextState site R.arena parent s new ready.frontier.head.2.2.2 hw
  have bitsEq := TraversalPlan.origin_nodeBits B f hf R.state R.choice R.port before new w
  rw [bitsEq] at read
  let old := oldAt before
  obtain ⟨es,out,ha,hjob⟩ := R.recover_job ties stride order pub m (parent : BurstRAM.Word bits) s old new hp job tail read
  clear read
  subst job
  obtain ⟨budgeted,counts⟩ := R.action_budgeted ties stride order pub m old new ha format desc nodeCap limit
    head pending ready (shape before) (typed before) nodeBound positive cacheFit limitFit capFit
  refine ⟨⟨rfl,?_,?_⟩,rfl,budgeted⟩
  · change choiceBits (R.front pub m parent old ++ es) = _
    rw [PrimedInputRAM.Flow.choiceBits_append,R.front_choices pub m]
    have quiet := TraversalPlan.canonicalAction_noChoices B ties stride order R.state R.choice R.port R.degree n
      R.rowEnd R.oldNode parent R.room old new m (TraversalControllerInputs.levelHead pub m R.level).val
      (TraversalControllerInputs.levelHead pub m (R.level+1)).val R.geometry ha
    rw [quiet,List.append_nil]
    exact bitsEq.symm
  · intro current enabled label
    change current = s at enabled
    subst current
    exact (counts label).trans (congrArg (H s label + ·)
      (TraversalPlan.origin_emitted_count B order R.state R.choice R.port new before f hf w label))

include ready hw shape typed nodeBound positive cacheFit limitFit capFit in
set_option maxHeartbeats 1500000 in
/-- Both directions of the single selected term row. The returned job has
the exact address, choice word and natural exponents on its enabled scratch,
and prepares the singleton child and every pending sibling. -/
theorem origin_steps :
    (∀ bs job tail, (hook).read (parent : BurstRAM.Word bits) s bs = some (job,tail) →
      ∃ before : assignment, ∃ w : (seen before new).Choice, bs = bitsOf before new w ++ tail ∧
        RealizesJob H ⟨parent,bitsOf before new w,(seen before new).exponents w⟩ job ∧
        job.enabled s ∧ valid (child before::pending) (job.update s)) ∧
    (∀ before : assignment, ∀ w : (seen before new).Choice, ∀ tail, ∃ job,
        (hook).read (parent : BurstRAM.Word bits) s (bitsOf before new w ++ tail) = some (job,tail) ∧
        RealizesJob H ⟨parent,bitsOf before new w,(seen before new).exponents w⟩ job ∧
        job.enabled s ∧ valid (child before::pending) (job.update s)) := by
  have hp := RefreshHalfDecoder.parent_eq R.nextState site R.arena parent s new ready.frontier.head.2.2.2 hw
  have choice bs tail := R.origin_tape_iff ties stride order pub m f hf (parent : BurstRAM.Word bits) s bs tail new hp
  have effect := origin_effect (R := R) (ties := ties) (stride := stride) (order := order) (pub := pub) (m := m)
    (f := f) (hf := hf) (new := new) (data := data) (offset := offset) (vals := vals) (format := format)
    (desc := desc) (nodeCap := nodeCap) (limit := limit) (pending := pending) (s := s) ready hw shape typed
    nodeBound positive cacheFit limitFit capFit
  constructor
  · intro bs job tail hit
    obtain ⟨before,w,tape⟩ := (choice bs tail).mp ⟨job,hit⟩
    rw [tape] at hit
    exact ⟨before,w,tape,effect before w tail job hit⟩
  · intro before w tail
    obtain ⟨job,hit⟩ := (choice (bitsOf before new w ++ tail) tail).mpr ⟨before,w,rfl⟩
    exact ⟨job,hit,effect before w tail job hit⟩

end PairSimulation.RefreshHook.Site

end VPVNP
end Computability
end OAI
