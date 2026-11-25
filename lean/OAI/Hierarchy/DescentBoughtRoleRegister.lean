import OAI.Hierarchy.DescentRegisterRoleRows
import OAI.Hierarchy.DescentRegisterResetRolePitch
import OAI.Hierarchy.DescentNamedPrimitiveCharge

namespace OAI
/-! # Positivity and address room of the previous role register on every purchased date -/
namespace Hierarchy.DescentSixParty.Chronology.OrdinaryBooks
open DescentCompiler DescentCompiler.TerminalScale DescentPrimitivePalette
noncomputable section
set_option quotPrecheck false
variable {F : Type} [Field F] (G : PoweredGadget F)
variable (op : RotorSpec) (t f g reset τ B drift maxDegree driftR h sites p : ℕ)
local notation "J" => Nat.log 2 h/(2*B)
local notation "S" => stageNumbers G t J f g reset sites (tail τ J)
local notation "c" => primitiveLocalRate G t f g reset
local notation "printed" => printedBits G ((S).firstWidth G.b p) ((S).grainAt G.b p 0) op

theorem PrimitiveCalendar.role_unit (price : PrimitiveCalendar G op t f g reset τ B drift maxDegree driftR h)
    (prior : DatePorts) (nodeBound : prior.nodes≤(S).retainedNodes) (pRoom : p≤h)
    (seed : (S).firstWidth G.b p≤h) : 2*DescentOrdinaryPalette.Configuration.returnUnit printed (S).retainedNodes≤h:=by
  have caps:=price.localRows sites 0 p 0 0 prior pRoom (Nat.zero_le _) nodeBound seed
  obtain ⟨_,_,_,nodes,_,bits,_⟩:=caps
  have product : printed*(S).retainedNodes≤ scale J (c+c):=
    (Nat.mul_le_mul bits nodes).trans_eq (scale_mul J c c)
  have nonzero : 1≤ scale J (c+c):=Nat.two_pow_pos _
  have unit : DescentOrdinaryPalette.Configuration.returnUnit printed (S).retainedNodes≤ scale J (c+c):=
    max_le nonzero product
  have exp : c+c≤primitiveLaneRate G t f g reset driftR:=by
    dsimp only [primitiveLaneRate]
    omega
  have mono : scale J (c+c)≤ scale J (primitiveLaneRate G t f g reset driftR):=
    Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right _ exp)
  have room:=price.available
  have small:=unit.trans mono
  omega

end
end Hierarchy.DescentSixParty.Chronology.OrdinaryBooks

namespace Hierarchy.DescentSixParty.Chronology.RegisterTimeline
open DescentCompiler DescentDatedAddressBook DescentDatedAddressBook.PhysicalReset DescentPrimitivePalette
open Computability.VPVNP.BurstRAM PrivateRAM
set_option quotPrecheck false
noncomputable section
variable {F P : Type} [Field F] [Fintype P] {G : PoweredGadget F} {S : AtomSchedule}
    {bits : P→ℕ} {d k wire hist final w : ℕ} {q ε : ℝ} {C : Type*}
    (traces : C→RunTrace G q ε S k wire hist final bits d)
    {n degree : ℕ} (b : Menu n degree) (initial : Position)
local notation "bits₀" => printedBits G (S.firstWidth G.b b.p) (S.grainAt G.b b.p 0) b.op

local notation "steps" => issued (w:=w) traces b
local notation "cursor" => calendar (w:=w) traces b initial
local notation "data" i:arg => Geometry G S b k w i (cursor i)
variable (fixed : ∀i (a z : RunTrace.Events traces i) x y,
  issued (w:=w) traces b i a (calendar (w:=w) traces b initial i) x→issued (w:=w) traces b i z (calendar (w:=w) traces b initial i) y→x=y)
variable (placed : ∀i (e : RunTrace.Events traces i),fitsAt traces b initial (w:=w) i e)

include fixed placed in
omit [Fintype P] in
private theorem prior_pitch_next (i : ℕ) (e : RunTrace.Events traces i) (prior : data i)
    (ample : 2*DescentOrdinaryPalette.Configuration.returnUnit bits₀ S.retainedNodes≤b.payload) :
    0<(cursor (i+1)).ports.roleLanes:=by
  obtain ⟨move,hit,_,_⟩:=placed i e prior
  rw [(returned traces b initial i e move hit (fun j t hj=>fixed i j e t move hj hit)).2]
  rcases e with ⟨_,event⟩
  cases event with
  | ordinary before ticket after eqn=>
    obtain ⟨_,_,rfl⟩:=hit
    exact (DescentOrdinaryPalette.Configuration.returned_occupancy b.payload bits₀ S.retainedNodes ample).1
  | reset before closed after eqn=>
    obtain ⟨_,_,rfl⟩:=hit
    exact Nat.two_pow_pos _

variable (caps : ∀c,(traces c).path.capFactors=capCalendar G.b S.rounds b.gain S.height)
    (kinds : ∀c,(traces c).path.kinds=kindCalendar S.rounds S.height)
    (start : Geometry G S b k w 0 (calendar (w:=w) traces b initial 0)) (c : C)
local notation "trace" => traces c

include fixed placed caps kinds start in
omit [Fintype P] in
theorem bought_role_registers (seed : initial.ports.RoleRows ∧ 0< initial.ports.roleLanes)
    (ample : 2*DescentOrdinaryPalette.Configuration.returnUnit bits₀ S.retainedNodes≤b.payload)
    {U : MarkedWorld F d P bits} {i z D : ℕ} {r : Reached U G q ε S k i z D wire hist}
    (p : Path (trace).first r) (suffix : Path r (trace).last) (joined : p.append suffix=(trace).path) :
    (cursor i).ports.RoleRows ∧ 0<(cursor i).ports.roleLanes:=by
  refine ⟨role_rows_prefix traces b initial fixed caps kinds start placed c seed.1 p suffix joined,?_⟩
  cases p with
  | here=>exact seed.2
  | @ordinary _ age _ _ _ _ src prev _ he T ballot norm dst tick=>
    let e : (trace).path.Event age:=.ordinary prev tick suffix joined
    exact prior_pitch_next traces b initial fixed placed age ⟨c,e⟩
      (geometry_on_event traces b initial fixed caps kinds start placed c age e) ample
  | @reset _ age _ _ _ _ _ _ _ _ _ src prev ctl closed=>
    let e : (trace).path.Event age:=.reset prev closed suffix joined
    exact prior_pitch_next traces b initial fixed placed age ⟨c,e⟩
      (geometry_on_event traces b initial fixed caps kinds start placed c age e) ample

end
end Hierarchy.DescentSixParty.Chronology.RegisterTimeline

end OAI
