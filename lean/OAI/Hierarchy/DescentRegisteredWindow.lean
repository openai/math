import OAI.Hierarchy.DescentRegisteredOrdinaryStep
import OAI.Hierarchy.DescentRegisteredResetStep
import OAI.Hierarchy.DescentRegisterTimeline
import OAI.Hierarchy.DescentDatedBranchEvents

namespace OAI
/-! # Each public register change uses the instruction at the original named cut -/
namespace Hierarchy.DescentSixParty.Chronology.RegisterTimeline
open DescentDatedAddressBook DescentDatedAddressBook.PhysicalReset DescentCompiler DescentPacking.PackedMatch.Local.Stage
open Computability.VPVNP.BurstRAM PrivateRAM
noncomputable section
variable {F P : Type} [Field F] [Fintype P] {G : PoweredGadget F} {S : AtomSchedule}
    {bits : P→ℕ} {d k wire hist final w : ℕ} {q ε : ℝ} {C : Type*}
    (traces : C→RunTrace G q ε S k wire hist final bits d)

structure Menu (n degree : ℕ) where
  board : NonlinearExpanders.Graph n degree
  op : RotorSpec
  gain : ℕ
  tail : ℕ
  p : ℕ
  f : ℕ
  drift : ℕ
  degreeLimit : ℕ
  payload : ℕ
  seats : ℕ→ℕ
  ordinary : ℕ→Dated.Ordinary
  profile : ℕ→ℕ
  header : ℕ

variable {n degree : ℕ} (b : Menu n degree)
set_option quotPrecheck false
local notation "model" i:arg a:arg t:arg => DatePorts.ordinaryModel (a:Position).ports t b.op b.gain b.tail b.p b.f b.drift
  b.degreeLimit b.payload (b.seats i) (a:Position).floor b.ordinary
local notation "outer" depth:arg i:arg a:arg => PhysicalReset.scheduledAtPorts G S b.board depth b.tail i b.p b.f b.gain b.drift
  b.degreeLimit b.payload b.ordinary b.op (S.firstWidth G.b b.p) (S.grainAt G.b b.p 0) (a:Position).ports (a:Position).floor
local notation "resetModel" depth:arg i:arg a:arg => (outer depth i a).inner
local notation "innerFloor" depth:arg a:arg => (a:Position).ports.priorStart depth (a:Position).floor
local notation "archives" depth:arg a:arg => ((a:Position).ports.afterPad depth (a:Position).floor).archive

def resetMove (k i w : ℕ) (a : Position) (cap : a.ports.venue.cap=((capCalendar G.b S.rounds b.gain S.height).take i).prod*256)
    (space : PhysicalReset.ScheduledCodeRoom G S b.board k b.tail i b.p b.f b.gain b.drift b.degreeLimit
      b.payload b.ordinary b.op (S.firstWidth G.b b.p) (S.grainAt G.b b.p 0) a.ports.operandLanes a.ports.roleLanes a.ports.venue
      a.ports.io (innerFloor k a) w (archives k a)) : Move w :=
  ⟨DatePorts.resetDate G S b.board k b.tail i b.p b.f b.gain b.drift b.degreeLimit b.payload
          b.ordinary b.op (S.firstWidth G.b b.p) (S.grainAt G.b b.p 0) a.ports a.floor w cap space,
          DatePorts.resetPorts G S b.board k b.tail i b.p b.f b.gain b.drift b.degreeLimit b.payload b.ordinary
            b.op (S.firstWidth G.b b.p) (S.grainAt G.b b.p 0) a.ports a.floor w space,(outer k i a).fullEnd⟩

def issued (i : ℕ) (e : RunTrace.Events traces i) (a : Position) (move : Move w) : Prop :=by
  cases e with
  | mk c e=>
    cases e with
    | ordinary before t after eqn=>
      exact ∃ (pos : 0 < k) (room : DatePorts.OrdinaryCodeRoom a.ports t b.op b.gain b.tail b.p b.f
          b.drift b.degreeLimit b.payload (b.seats i) a.floor b.ordinary w),
        move=⟨DatePorts.ordinaryDate a.ports t b.op b.gain b.tail b.p b.f b.drift b.degreeLimit
          b.payload (b.seats i) a.floor b.ordinary w (b.profile i) b.header pos room,
          DatePorts.ordinaryPorts a.ports t b.op b.gain b.tail b.p b.f b.drift b.degreeLimit
            b.payload (b.seats i) a.floor b.ordinary,(model i a t).fullEnd a.floor⟩
    | reset before closed after eqn=>
      exact ∃ (cap : a.ports.venue.cap=((capCalendar G.b S.rounds b.gain S.height).take i).prod*256)
        (space : PhysicalReset.ScheduledCodeRoom G S b.board k b.tail i b.p b.f b.gain b.drift b.degreeLimit
          b.payload b.ordinary b.op (S.firstWidth G.b b.p) (S.grainAt G.b b.p 0) a.ports.operandLanes a.ports.roleLanes a.ports.venue
          a.ports.io (innerFloor k a) w (archives k a)), move=resetMove (G:=G) (S:=S) b k i w a cap space

abbrev calendar (initial : Position) := @position w _ (issued traces b) initial
abbrev instruction (initial : Position) := @date w _ (issued traces b) initial

omit [Fintype P] in
theorem forward (i : ℕ) (e : RunTrace.Events traces i) (a : Position) (move : Move w)
    (hit : issued traces b i e a move) : a.floor ≤ move.next.floor :=by
  obtain ⟨c,e⟩:=e
  cases e with
  | ordinary before t after eqn=>
    obtain ⟨positive,space,rfl⟩:=hit
    exact ((model i a t).full_spent a.floor).1
  | reset before z after eqn=>
    obtain ⟨cap,space,rfl⟩:=hit
    exact (outer k i a).stages.1.trans (outer k i a).stages.2

omit [Fintype P] in
theorem reset_unique (i : ℕ) (left right : RunTrace.Events traces i) (a : Position) (one two : Move w)
    (ltype : left.2.isReset=true) (rtype : right.2.isReset=true)
    (lrun : issued traces b i left a one) (rrun : issued traces b i right a two) : one=two :=by
  obtain ⟨lc,le⟩:=left
  obtain ⟨rc,re⟩:=right
  cases le with
  | ordinary before t after eqn=>cases ltype
  | reset before z after eqn=>
    cases re with
    | ordinary before t after eqn=>cases rtype
    | reset before' z' after' eqn'=>
      obtain ⟨cap,space,rfl⟩:=lrun
      obtain ⟨cap',space',rfl⟩:=rrun
      rfl

omit [Fintype P] in
theorem same_kind (i : ℕ) (a : Position)
    (kinds : ∀l r : RunTrace.Events traces i,l.2.isReset=r.2.isReset)
    (ordinary : ∀l r : RunTrace.Events traces i,∀x y : Move w,
      l.2.isReset = false → r.2.isReset = false → issued traces b i l a x → issued traces b i r a y → x = y)
    (l r : RunTrace.Events traces i) (x y : Move w)
    (left : issued traces b i l a x) (right : issued traces b i r a y) : x=y :=by
  have em:=kinds l r
  cases hh:l.2.isReset with
  | false=>exact ordinary l r x y hh (em.symm.trans hh) left right
  | true=>exact reset_unique traces b i l r a x y hh (em.symm.trans hh) left right

omit [Fintype P] in
theorem returned (initial : Position) (i : ℕ) (e : RunTrace.Events traces i) (move : Move w)
    (hit : issued traces b i e (calendar (w:=w) traces b initial i) move)
    (fixed : ∀r : RunTrace.Events traces i,∀y : Move w,issued traces b i r (calendar (w:=w) traces b initial i) y→y=move) :
    instruction traces b initial i=move.code ∧ calendar (w:=w) traces b initial (i+1)=move.next :=
  date_at (issued traces b) initial i e move hit (forward traces b i e _ move hit) fixed

omit [Fintype P] in
theorem reset_return (initial : Position) (i : ℕ) (e : RunTrace.Events traces i) (kind : e.2.isReset=true)
    (cap : (calendar (w:=w) traces b initial i).ports.venue.cap=
      ((capCalendar G.b S.rounds b.gain S.height).take i).prod*256)
    (space : PhysicalReset.ScheduledCodeRoom G S b.board k b.tail i b.p b.f b.gain b.drift b.degreeLimit
      b.payload b.ordinary b.op (S.firstWidth G.b b.p) (S.grainAt G.b b.p 0)
      (calendar (w:=w) traces b initial i).ports.operandLanes (calendar (w:=w) traces b initial i).ports.roleLanes
      (calendar (w:=w) traces b initial i).ports.venue (calendar (w:=w) traces b initial i).ports.io
      (innerFloor k (calendar (w:=w) traces b initial i)) w (archives k (calendar (w:=w) traces b initial i)))
    (kinds : ∀r : RunTrace.Events traces i,r.2.isReset=e.2.isReset) :
    let a:=calendar (w:=w) traces b initial i
    let move:=resetMove (G:=G) (S:=S) b k i w a cap space
    let model₀:=resetModel k i a
    instruction traces b initial i=move.code ∧ calendar (w:=w) traces b initial (i+1)=move.next ∧
      (calendar (w:=w) traces b initial (i+1)).ports.archive=PriorResetArchive.reset model₀.successor
        (model₀.rebased (model₀.stageStart (innerFloor k a))) :=by
  let a:=calendar (w:=w) traces b initial i
  let m₁:=resetMove (G:=G) (S:=S) b k i w a cap space
  have hit : issued traces b i e a m₁:=by
    rcases e with ⟨c,x⟩
    cases x with
    | ordinary before t after eqn=>cases kind
    | reset before z after eqn=>exact ⟨cap,space,rfl⟩
  have ⟨op,ret⟩:=returned traces b initial i e m₁ hit
    (fun r y right=>reset_unique traces b i r e a y m₁ ((kinds r).trans kind) kind right hit)
  exact ⟨op,ret,congrArg (fun p : Position=>p.ports.archive) ret⟩


end
end Hierarchy.DescentSixParty.Chronology.RegisterTimeline

end OAI
