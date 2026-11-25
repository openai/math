import OAI.Hierarchy.DescentRegisteredGeometry
import OAI.Hierarchy.DescentArchivePadInputs

namespace OAI
/-! # Every reached previous primitive bank covers its actual physical row count -/
namespace Hierarchy.DescentSixParty.Chronology.RegisterTimeline
open DescentCompiler DescentDatedAddressBook DescentDatedAddressBook.PhysicalReset DescentPacking.PackedMatch.Local.Stage
open Computability.VPVNP.BurstRAM PrivateRAM
set_option quotPrecheck false
noncomputable section
variable {F P : Type} [Field F] [Fintype P] {G : PoweredGadget F} {S : AtomSchedule}
    {bits : P→ℕ} {d k wire hist final w : ℕ} {q ε : ℝ} {C : Type*}
    (traces : C→RunTrace G q ε S k wire hist final bits d)
    {n degree : ℕ} (b : Menu n degree) (initial : Position)

local notation "model" i:arg a:arg t:arg => DatePorts.ordinaryModel (a:Position).ports t b.op b.gain b.tail b.p b.f b.drift
  b.degreeLimit b.payload (b.seats i) (a).floor b.ordinary
local notation "resetModel" i:arg a:arg => PhysicalReset.scheduled G S b.board k b.tail i b.p b.f b.gain b.drift
  b.degreeLimit b.payload b.ordinary b.op (S.firstWidth G.b b.p) (S.grainAt G.b b.p 0) (a:Position).ports.operandLanes (a).ports.roleLanes
  (a).ports.venue (a).ports.io.wire (a).ports.io.roster ((a).ports.priorStart k (a).floor)

omit [Fintype P] in
theorem output_role_rows (i : ℕ) (e : RunTrace.Events traces i) (a : Position) (move : Move w)
    (hit : issued traces b i e a move)  :
    move.next.ports.RoleRows :=by
  obtain ⟨_,e⟩:=e
  cases e with
  | ordinary before t after eqn=>
    obtain ⟨positive,room,rfl⟩:=hit
    let v:=model i a t
    apply DatePorts.ordinary_role_rows v (v.stageStart a.floor) <;> rfl
  | reset before t after eqn=>
    obtain ⟨cap,space,rfl⟩:=hit
    let v:=resetModel i a
    let floor:=a.ports.priorStart k a.floor
    apply DatePorts.reset_role_rows v (v.stageStart floor) _ <;> rfl

local notation "costs" => capCalendar G.b S.rounds b.gain S.height
local notation "cursor" => calendar (w:=w) traces b initial
local notation "steps" => issued (w:=w) traces b
local notation "data" i:arg => Geometry G S b k w i (cursor i)
variable (fixed : ∀i (a z : RunTrace.Events traces i) x y,
  issued (w:=w) traces b i a (calendar (w:=w) traces b initial i) x→
    issued (w:=w) traces b i z (calendar (w:=w) traces b initial i) y→x=y)
variable (caps : ∀c,(traces c).path.capFactors=capCalendar G.b S.rounds b.gain S.height) (tags : ∀c,(traces c).path.kinds=kindCalendar S.rounds S.height)
variable (seed : Geometry G S b k w 0 initial)

variable (placed : ∀i (e : RunTrace.Events traces i),fitsAt traces b initial (w:=w) i e)

include fixed placed in
omit [Fintype P] in
theorem role_rows_next (i : ℕ) (e : RunTrace.Events traces i) (prior : data i) : (cursor (i+1)).ports.RoleRows:=by
  obtain ⟨move,hit,_,_⟩:=placed i e prior
  rw [(returned traces b initial i e move hit (fun j t hj=>fixed i j e t move hj hit)).2]
  exact output_role_rows traces b i e _ move hit

variable (c : C) (initialRows : initial.ports.RoleRows)
local notation "t" => traces c

include fixed caps tags seed placed initialRows in
omit [Fintype P] in
theorem role_rows_prefix {U : MarkedWorld F d P bits} {i z D : ℕ} {r : Reached U G q ε S k i z D wire hist}
    (p : Path (t).first r) (suffix : Path r (t).last) (joined : p.append suffix=(t).path) : (cursor i).ports.RoleRows:=by
  cases p with
  | here=>exact initialRows
  | @ordinary _ age _ _ _ _ src prev _ he T ballot norm dst tick=>
    let e : (t).path.Event age:=.ordinary prev tick suffix joined
    exact role_rows_next traces b initial fixed placed age ⟨c,e⟩
      (geometry_on_event traces b initial fixed caps tags seed placed c age e)
  | @reset _ age _ _ _ _ _ _ _ _ _ src prev ctl closed=>
    let e : (t).path.Event age:=.reset prev closed suffix joined
    exact role_rows_next traces b initial fixed placed age ⟨c,e⟩
      (geometry_on_event traces b initial fixed caps tags seed placed c age e)

end
end Hierarchy.DescentSixParty.Chronology.RegisterTimeline

end OAI
