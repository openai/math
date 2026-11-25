import OAI.Hierarchy.DescentRegisteredFinalEvent
import OAI.Hierarchy.DescentRecordedPostedPlanes

namespace OAI
/-! # Last-reset registers and the actor bits on the same dated store -/
namespace Hierarchy.DescentSixParty.Chronology
open DescentCompiler DescentSIMDLookup DescentActorRaster DescentColonies ProtocolRAM
open Computability.VPVNP.BurstRAM PrivateRAM
noncomputable section
set_option hygiene false
set_option quotPrecheck false
variable {F P : Type} [Field F] [Fintype P] {G : PoweredGadget F} {S : AtomSchedule}
    {bits : P→ℕ} {d k wire hist w : ℕ} {q ε : ℝ}
    {I U : MarkedWorld F d P bits} {z₀ D₀ len z D : ℕ}
    {first : Reached I G q ε S k 0 z₀ D₀ wire hist} {done_ : Reached U G q ε S k len z D wire hist}
    {path:Path first done_}

def Path.Event.actorPlanes {age:ℕ} (e:path.Event age) (bank : DescentColonies.Block k→Bank) (m:Memory w) : Prop:=by
  cases e with
  | ordinary before ticket after_ placed=>exact False
  | reset before B after_ placed=>
    exact ∀x,DescentPackedColony.Reads (bank x) (Venue.actual B.next.placement (Function.Embedding.refl _)
      (B.next.vertex.trans (Fin.castLEEmb B.next.valid.host)) x) (S.groupCount (age+1)) m

omit [Fintype P] in
theorem Path.FinalReset.actor_planes {p:ℕ} (last:Path.FinalReset p path) (bank : DescentColonies.Block k→Bank) (m:Memory w)
    (physical:last.event.actorPlanes bank m) :
    ∀x,DescentPackedColony.Reads (bank x) (Venue.actual done_.placement (Function.Embedding.refl _)
      (done_.vertex.trans (Fin.castLEEmb done_.valid.host)) x) (S.groupCount len) m:=by
  cases last with
  | posted before B «prefix» paid=>exact physical

namespace RegisterTimeline
variable {C : Type*} {n degree : ℕ} (traces : C→RunTrace G q ε S k wire hist len bits d)
    (b : Menu n degree) (initial : Position) (c : C)
local notation "t" => traces c
local notation "cursor" => calendar (w:=w) traces b initial
local notation "steps" => issued (w:=w) traces b
local notation "code" => instruction (w:=w) traces b initial
local notation "family" => RunTrace.machine traces (fun i _=>code i)
variable (boot:Memory w) (limit:ℕ) (valid:Prop)
local notation "ram" => DateCode.history code boot
local notation "cutRam" => DateCode.history family boot
variable (fixed : ∀i (a z : RunTrace.Events traces i) x y,
      steps i a (cursor i) x → steps i z (cursor i) y → x=y)
  (origin : initial.ports.held (t).first initial.floor boot)
  (runs : ∀i (e : (t).path.Event i), advances traces b initial c boot limit valid i e)

local notation "age" => len-1
local notation "prior_" => cursor age
local notation "innerFloor" => (prior_).ports.priorStart k (prior_).floor
local notation "model_" => DescentDatedAddressBook.PhysicalReset.scheduled G S b.board k b.tail age b.p b.f b.gain b.drift
  b.degreeLimit b.payload b.ordinary b.op (S.firstWidth G.b b.p) (S.grainAt G.b b.p 0)
  (prior_).ports.operandLanes (prior_).ports.roleLanes (prior_).ports.venue (prior_).ports.io.wire
  (prior_).ports.io.roster innerFloor
local notation "sheet" => (model_).successor
local notation "start_" => (model_).rebased ((model_).stageStart innerFloor)
local notation "actor_" => fun x:DescentColonies.Block k=>(sheet).terminalActor start_ x.val

include fixed origin runs in
omit [Fintype P] in
/-- The date rows read on a surviving ballot, at the authentic registered reset.
Earlier held registers are propagated by the original cut induction. The one extra
observed field is the native occupancy bitmap emitted at the selected final event. -/
theorem last_reset_register {p:ℕ} (end_ : Path.FinalReset p (t).path)
    (alive : (t).path.selections.length<limit ∨ valid)
    (present : ∃mv,steps age ⟨c,end_.event⟩ prior_ mv)
    (actors : end_.event.actorPlanes actor_ (ram len)) :
    ∃cap room,
      let mv:=resetMove (G:=G) (S:=S) b k age w prior_ cap room
      family age=mv.code ∧ (cursor len)=mv.next ∧
      mv.next.ports.held (t).last mv.next.floor (cutRam len) ∧
        ∀x,DescentPackedColony.Reads (actor_ x) (Venue.actual (t).last.placement (Function.Embedding.refl _)
          ((t).last.vertex.trans (Fin.castLEEmb (t).last.valid.host)) x) (S.groupCount len) (cutRam len) :=by
  obtain ⟨cap,room,_,date_,next⟩:=final_move traces b initial c end_ fixed present
  have h:=held_prefix traces b initial c boot limit valid fixed origin runs (t).path .here rfl alive
  rw [next] at h
  have final_:=history_from_cuts traces b initial c boot len le_rfl
  exact ⟨cap,room,date_,next,final_.symm ▸ h,final_.symm ▸ end_.actor_planes actor_ (ram len) actors⟩

end RegisterTimeline
end
end Hierarchy.DescentSixParty.Chronology

end OAI
