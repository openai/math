import OAI.Hierarchy.DescentRegisterCutInduction
import OAI.Hierarchy.DescentRegisteredWindowRooms

namespace OAI
/-! # Register dimensions and genuine reads along an allocated physical path -/
namespace Hierarchy.DescentSixParty.Chronology.RegisterTimeline
open Computability.VPVNP.BurstRAM PrivateRAM
noncomputable section
variable {F P : Type} [Field F] [Fintype P] {G : PoweredGadget F} {S : DescentCompiler.AtomSchedule}
    {bits : P→ℕ} {d k wire hist final w : ℕ} {q ε : ℝ} {C : Type*}
    (traces : C→RunTrace G q ε S k wire hist final bits d)
    {n degree : ℕ} (b : Menu n degree) (initial : Position)
local notation "steps" => issued (w:=w) traces b
local notation "cursor" => calendar (w:=w) traces b initial
variable (fixed : ∀i (a z : RunTrace.Events traces i) x y,
  issued (w:=w) traces b i a (calendar (w:=w) traces b initial i) x→issued (w:=w) traces b i z (calendar (w:=w) traces b initial i) y→x=y)
variable (start : Rooms G S b k w 0 initial)
variable (installed : ∀i (e : RunTrace.Events traces i),Rooms G S b k w i (calendar (w:=w) traces b initial i)→
  ∃move : Move w,issued (w:=w) traces b i e (calendar (w:=w) traces b initial i) move ∧ move.next.floor<2^w ∧
    (e.2.isReset=true→8*b.receiverWidth G S k i (calendar (w:=w) traces b initial i).ports ≤ b.payload))

include fixed installed in
omit [Fintype P] in
theorem next_room (i : ℕ) (e : RunTrace.Events traces i) (old : Rooms G S b k w i (cursor i)) :
    Rooms G S b k w (i+1) (cursor (i+1)) :=by
  obtain ⟨move,hit,roof,short⟩:=installed i e old
  have next:=(returned traces b initial i e move hit (fun d t h=>fixed i d e t move h hit)).2
  rw [next]
  exact issued_register_room traces b i e _ move hit old roof short

variable (c : C)
local notation "t" => traces c

include fixed start installed in
omit [Fintype P] in
theorem rooms_prefix {U : MarkedWorld F d P bits} {i z D : ℕ} {r : Reached U G q ε S k i z D wire hist}
    (p : Path (t).first r) (suffix : Path r (t).last) (joined : p.append suffix=(t).path) :
    Rooms G S b k w i (cursor i) :=by
  induction p with
  | here=>exact start
  | @ordinary _ age _ _ _ _ src prev _ he T ballot norm dst tick ih=>
    apply next_room traces b initial fixed installed age ⟨c,.ordinary prev tick suffix joined⟩
    exact ih ((Path.here.ordinary tick).append suffix)
      ((Path.append_cut_assoc prev (Path.here.ordinary tick) suffix).symm.trans joined)
  | @reset _ age _ _ _ _ _ _ _ _ _ src prev ctl closed ih=>
    apply next_room traces b initial fixed installed age ⟨c,.reset prev closed suffix joined⟩
    exact ih ((Path.here.reset closed).append suffix)
      ((Path.append_cut_assoc prev (Path.here.reset closed) suffix).symm.trans joined)

include fixed start installed in
omit [Fintype P] in
theorem rooms_on_event (i : ℕ) (e : (t).path.Event i) : Rooms G S b k w i (cursor i) :=by
  cases e with
  | ordinary before tick after eqn=>
    exact rooms_prefix traces b initial fixed start installed c before ((Path.here.ordinary tick).append after)
      ((Path.append_cut_assoc before (Path.here.ordinary tick) after).symm.trans eqn)
  | reset before closed after eqn=>
    exact rooms_prefix traces b initial fixed start installed c before ((Path.here.reset closed).append after)
      ((Path.append_cut_assoc before (Path.here.reset closed) after).symm.trans eqn)

variable (mem : Memory w) (limit : ℕ) (valid : Prop)
local notation "code" => instruction (w:=w) traces b initial
local notation "ram" => DateCode.history code mem
variable (boot : initial.ports.held (traces c).first initial.floor mem)
variable (native : ∀i (e : (traces c).path.Event i),Rooms G S b k w i (calendar (w:=w) traces b initial i)→
       advances traces b initial c mem limit valid i e)

include fixed start installed boot native in
omit [Fintype P] in
theorem prefix_registers {U : MarkedWorld F d P bits} {i z D : ℕ} {r : Reached U G q ε S k i z D wire hist}
    (p : Path (t).first r) (suffix : Path r (t).last) (joined : p.append suffix=(t).path)
    (live : p.selections.length < limit ∨ valid) :
    Rooms G S b k w i (cursor i) ∧ (cursor i).ports.held r
      (DescentDatedAddressBook.floor initial.floor (span steps initial) i) (ram i) ∧ Fintype.card r.V≤(cursor i).ports.venue.hosts :=
  ⟨rooms_prefix traces b initial fixed start installed c p suffix joined,
   held_floor traces b initial c mem limit valid fixed boot
     (fun j e=>native j e (rooms_on_event traces b initial fixed start installed c j e)) p suffix joined live⟩

end
end Hierarchy.DescentSixParty.Chronology.RegisterTimeline

end OAI
