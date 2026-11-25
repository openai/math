import OAI.Hierarchy.DescentDateTaggedOrdinals
import OAI.Hierarchy.DescentDatePortTaggedRead
import OAI.Hierarchy.DescentResetTaggedArchive
import OAI.Hierarchy.DescentCalendarRangeReturn
import OAI.Hierarchy.DescentPostedResetCheckpoints
import OAI.Hierarchy.DescentRegisteredSelectedReady

namespace OAI
/-! The reset publishes all seven operand pages on the registered cut's actual successor memory. -/
namespace Hierarchy.DescentSixParty.Chronology.RegisterTimeline
open DescentDatedAddressBook DescentDatedAddressBook.PhysicalReset DescentCompiler DescentPacking.PackedMatch.Local.Stage
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM
noncomputable section
set_option quotPrecheck false
set_option hygiene false
variable {F P : Type} [Field F] [Fintype P] {G : PoweredGadget F} {S : AtomSchedule}
    {bits : P→ℕ} {d k wire hist final w : ℕ} {q ε : ℝ} {C : Type*}
    (traces : C→RunTrace G q ε S k wire hist final bits d) {n degree : ℕ} (b : Menu n degree)
    (initial : Position) (i : ℕ) (e : RunTrace.Events traces i)
local notation "pos" => calendar (w:=w) traces b initial i
local notation "nextPos" => calendar (w:=w) traces b initial (i+1)
local notation "ports" => (pos).ports
local notation "s₀" => S.firstWidth G.b b.p
local notation "Z₀" => S.grainAt G.b b.p 0
local notation "floor₀" => (ports).priorStart k (pos).floor
local notation "prior₀" => ((ports).afterPad k (pos).floor).archive
local notation "outer" => scheduledAtPorts G S b.board k b.tail i b.p b.f b.gain b.drift b.degreeLimit b.payload b.ordinary b.op s₀ Z₀ (ports) (pos).floor
local notation "model" => (outer).inner
local notation "out" => (model).successor
local notation "ingress" => (model).ingress
local notation "publisher" => priorArchivePhase G S b.board k b.tail i b.p b.f b.gain b.drift b.degreeLimit b.payload b.ordinary b.op s₀ Z₀ (ports) (pos).floor w
local notation "raw" => previousArchiveLayout G S b.board k b.tail i b.p b.f b.gain b.drift b.degreeLimit b.payload b.ordinary b.op s₀ Z₀ (ports) (pos).floor
local notation "phase" => (ingress).phase floor₀ w (ports).io.hubs (fun x=>(ports).io.atoms x.val)
  (fun j=>(ports).io.wire j.1.val j.2.val)
local notation "codes" => instruction (w:=w) traces b initial
local notation "machine" => RunTrace.machine traces (fun t _=>(codes) t)
variable (geo : Geometry G S b k w i (pos))
local notation "cap" => ((capCalendar G.b S.rounds b.gain S.height).take i).prod*256
variable (space : ScheduledCodeRoom G S b.board k b.tail i b.p b.f b.gain b.drift b.degreeLimit
    b.payload b.ordinary b.op s₀ Z₀ (ports).operandLanes (ports).roleLanes (ports).venue (ports).io floor₀ w prior₀)
local notation "u" => DatePorts.resetInputs G S b.board k b.tail i b.p b.f b.gain b.drift b.degreeLimit
    b.payload b.ordinary b.op s₀ Z₀ (ports) (pos).floor w space
local notation "v" => (model).successor
local notation "receiver" => (v).receiver
local notation "atMem" boot:arg => (phase).image ((publisher).image (DateCode.history (machine) boot i))

omit [Fintype P] in
private theorem reset_query_room :
    2*(receiver).candidates<2^(receiver).queryBits :=
  (Nat.lt_succ_self (2*(receiver).candidates)).trans_le (Nat.le_pow_clog (by decide : 1<2) _)

include geo in
omit [Fintype P] in
/-- The selected instruction supplies its own setup and scene room at the cut. -/
theorem reset_tag_support (tags : ∀c,(traces c).path.kinds=kindCalendar S.rounds S.height)
    (kind : e.2.isReset=true) (short : 8*b.receiverWidth G S k i (ports)≤b.payload) (bus : b.payload≤w)
    (degreeRoom : (ports).venue.degree+1<2^w) (roof : (outer).fullEnd<2^w) :
    ScheduledCodeRoom G S b.board k b.tail i b.p b.f b.gain b.drift b.degreeLimit
      b.payload b.ordinary b.op s₀ Z₀ (ports).operandLanes (ports).roleLanes (ports).venue
      (ports).io floor₀ w prior₀ :=by
  obtain ⟨move,issuedAt,_,_⟩:=reset_issued_any traces b initial tags i e kind geo short bus degreeRoom roof
  rcases e with ⟨c,event⟩
  cases event with
  | ordinary before ticket after joined => cases kind
  | reset before closed after joined =>
    obtain ⟨_,res,_⟩:=issuedAt
    exact res

omit [Fintype P] in
/-- The attained actor pass fixes the source of every ordinal. Determinism identifies that
array with the one used inside the registered reset, including on a nonterminal reset date. -/
theorem reset_history_tags (tags : ∀c,(traces c).path.kinds=kindCalendar S.rounds S.height)
    (kind : e.2.isReset=true) (short : 8*b.receiverWidth G S k i (ports)≤b.payload) (bus : b.payload≤w)
    (degreeRoom : (ports).venue.degree+1<2^w) (roof : (outer).fullEnd<2^w) (boot : Memory w)
    (observed : let ok:= (reset_issued_ready traces b initial tags i e kind geo short bus degreeRoom roof space).1
      let small:=reset_query_room (w:=w) traces b initial i
      ∃actorMem,(u).ThroughActors (atMem boot) actorMem ∧ (u).TaggedOrdinals ok small actorMem) :
    DatePorts.ArchiveTags (nextPos).ports (DateCode.history (machine) boot (i+1)) :=by
  obtain ⟨ready,fitted⟩:=reset_issued_ready traces b initial tags i e kind geo short bus degreeRoom roof space
  have small:=reset_query_room (w:=w) traces b initial i
  have kinds (r : RunTrace.Events traces i) : r.2.isReset=e.2.isReset :=
    r.2.compatible e.2 ((tags r.1).trans (tags e.1).symm)
  have chosen:=reset_return (w:=w) traces b initial i e kind geo.capacity space kinds
  have sampled : (machine) i=(codes) i :=
    RunTrace.on_branch traces (fun t _=>(codes) t) (fun _ _ _=>rfl) e.1 i e.2
  have native : (ports).archive.Fits raw (pos).floor := geo.archive.data (v).setup.retained
  have low := (outer).stages.1.trans_lt ((outer).stages.2.trans_lt roof)
  have pages:=(raw).prior_registers (ports).archive.seed (ports).archive.nodeBase (ports).archive.arguments
    (pos).floor w native.1 native.2 low
  have roles (j : Fin (2^k)) := (ports).archive.roles.fits w (pos).floor j.val
    (j.isLt.trans_le geo.archive.blocks) geo.archive.roles low
  have address := (model).occupied ((model).stageStart floor₀)
  have stage := ((address.1.trans address.2.1).trans address.2.2).trans_lt roof
  have wireFits (j : (ingress).signed.Slot) : ((ports).io.wire j.1.val j.2.val).Fits w (pos).floor := by
    exact (geo.room.wires (j.1.cast (congrArg (2^·) geo.format.width.symm))
      (j.2.cast (congrArg (2*·) geo.capacity.symm))).1
  obtain ⟨_,_,mid,first,done,_⟩:=DatePorts.reset_checkpoints G S b.board k b.tail i b.p b.f b.gain b.drift b.degreeLimit
    b.payload b.ordinary b.op s₀ Z₀ (ports) (pos).floor w geo.capacity space (machine) boot
    (sampled.trans chosen.1) ready fitted pages roles geo.room.header.hubs (fun x=>geo.room.paid.stock x.val) wireFits stage
  have layoutAt := (reset_range_fields traces b initial i e kind geo.capacity space kinds geo.format.width).2.1
  rw [chosen.2.1] at layoutAt ⊢
  obtain ⟨actorMem,acted,allRows⟩:=observed
  have rows {z : Memory w} (hit : (u).ThroughActors (atMem boot) z) : (u).TaggedOrdinals ready small z := by
    have eqn := exec_unique _ _ _ _ acted hit
    exact eqn ▸ allRows
  have two : 2≤(v).nodeBits :=
    (DescentOperandWidth.wide G S k b.tail b.drift b.degreeLimit).trans (Nat.le_max_left ..)
  exact DatePorts.reset_archive_tags (u) layoutAt _ ready fitted first done rfl two small
    (fun z hit f j x n=>((rows hit) j x n).1 f)
    (fun z hit j x n=>((rows hit) j x n).2)

/-- Original dated room, real actor execution, and the acquired rows on that execution. -/
structure ResetTagSources (boot : Memory w) : Prop where
  geometry : Geometry G S b k w i (pos)
  installed : ScheduledCodeRoom G S b.board k b.tail i b.p b.f b.gain b.drift b.degreeLimit
    b.payload b.ordinary b.op s₀ Z₀ (ports).operandLanes (ports).roleLanes (ports).venue (ports).io floor₀ w prior₀
  schedule : ∀c,(traces c).path.kinds=kindCalendar S.rounds S.height
  kind : e.2.isReset=true
  short : 8*b.receiverWidth G S k i (ports)≤b.payload
  bus : b.payload≤w
  degreeRoom : (ports).venue.degree+1<2^w
  roof : (outer).fullEnd<2^w
  observed :
    let input:=DatePorts.resetInputs G S b.board k b.tail i b.p b.f b.gain b.drift b.degreeLimit
      b.payload b.ordinary b.op s₀ Z₀ (ports) (pos).floor w installed
    let ready:=(reset_issued_ready traces b initial schedule i e kind geometry short bus degreeRoom roof installed).1
    ∃actorMem,input.ThroughActors (atMem boot) actorMem ∧
      input.TaggedOrdinals ready (reset_query_room (w:=w) traces b initial i) actorMem

variable {traces b initial i e} in
omit [Fintype P] in
theorem ResetTagSources.result {boot : Memory w} (src : ResetTagSources traces b initial i e boot) :
    DatePorts.ArchiveTags (nextPos).ports (DateCode.history (machine) boot (i+1)) :=
  reset_history_tags traces b initial i e src.geometry src.installed src.schedule src.kind src.short src.bus
    src.degreeRoom src.roof boot src.observed

end
end Hierarchy.DescentSixParty.Chronology.RegisterTimeline

end OAI
