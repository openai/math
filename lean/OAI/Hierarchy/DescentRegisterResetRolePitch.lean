import OAI.Hierarchy.DescentRegisterEmittedRoleRows
import OAI.Hierarchy.DescentDatedPrimitivePitch

namespace OAI
/-! # The preceding primitive register has a positive pitch at every noninitial reset -/
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

/-- The reset's primitive checkpoint footprint includes a complete vector of the
same printed tokens returned by an ordinary predecessor. -/
theorem Menu.primitive_return_room (age : ℕ) (ports : DatePorts)
    (wide : 8*b.receiverWidth G S k age ports≤b.payload) :
    2*DescentOrdinaryPalette.Configuration.returnUnit bits₀ S.retainedNodes≤b.payload :=by
  let earlier:=ResetOutput.Prior.atDate G S age b.p b.drift ports.operandLanes ports.roleLanes bits₀ ports.venue
  let old:=NativePitch.resetCut S k b.tail b.p b.f b.payload age
  let next:=NativePitch.incoming S k b.tail b.p b.f b.payload b.ordinary (age+1)
  let v:=ResetOutput.fromBoard G S b.board k b.tail age b.p b.f b.gain b.drift b.degreeLimit b.payload
    0 old 1 next b.op.C b.op.w earlier 0
  change 8*v.groupWidth≤b.payload at wide
  have measured:=v.groupWidth_fit (t:=v.primitive.chart.bits*v.primitive.chart.nodes+v.primitive.chart.bits)
    (Or.inr (by simp [ResetOutput.receiverUnits]))
  change bits₀*S.retainedNodes+bits₀≤v.groupWidth at measured
  have positive : 1≤v.groupWidth:=Nat.le_add_right 1 _
  have cap : max 1 (bits₀*S.retainedNodes)≤v.groupWidth:=
    max_le positive ((Nat.le_add_right _ _).trans measured)
  change 2*max 1 (bits₀*S.retainedNodes)≤b.payload
  omega

local notation "steps" => issued (w:=w) traces b
local notation "cursor" => calendar (w:=w) traces b initial
local notation "data" i:arg => Geometry G S b k w i (cursor i)
variable (fixed : ∀i (a z : RunTrace.Events traces i) x y,
  issued (w:=w) traces b i a (calendar (w:=w) traces b initial i) x→issued (w:=w) traces b i z (calendar (w:=w) traces b initial i) y→x=y)
variable (placed : ∀i (e : RunTrace.Events traces i),fitsAt traces b initial (w:=w) i e)

include fixed placed in
omit [Fintype P] in
private theorem role_pitch_next (i : ℕ) (e : RunTrace.Events traces i) (prior : data i)
    (wide : 8*b.receiverWidth G S k (i+1) (cursor (i+1)).ports≤b.payload) :
    0<(cursor (i+1)).ports.roleLanes:=by
  have ample:=b.primitive_return_room (G:=G) (S:=S) (k:=k) (i+1) _ wide
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

variable (onCut : ∀i,RunTrace.Events traces i→Geometry G S b k w i (calendar (w:=w) traces b initial i)) (c : C)
local notation "t" => traces c

include fixed placed onCut in
omit [Fintype P] in
theorem archive_role_prefix {U : MarkedWorld F d P bits} {i z D : ℕ} {r : Reached U G q ε S k i z D wire hist}
    (p : Path (t).first r) (suffix : Path r (t).last) (joined : p.append suffix=(t).path) (live : 0< i)
    (wide : 8*b.receiverWidth G S k i (cursor i).ports≤b.payload) : 0<(cursor i).ports.roleLanes:=by
  cases p with
  | here=>omega
  | @ordinary _ age _ _ _ _ src prev _ he T ballot norm dst tick=>
    let e : (t).path.Event age:=.ordinary prev tick suffix joined
    exact role_pitch_next traces b initial fixed placed age ⟨c,e⟩ (onCut age ⟨c,e⟩) wide
  | @reset _ age _ _ _ _ _ _ _ _ _ src prev ctl closed=>
    let e : (t).path.Event age:=.reset prev closed suffix joined
    exact role_pitch_next traces b initial fixed placed age ⟨c,e⟩ (onCut age ⟨c,e⟩) wide

end
end Hierarchy.DescentSixParty.Chronology.RegisterTimeline

end OAI
