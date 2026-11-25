import OAI.Hierarchy.DescentProfiledOrdinaryUniformAxes
import OAI.Hierarchy.DescentProfiledOrdinaryBookRooms
import OAI.Hierarchy.DescentUniformPrimitiveAperture

namespace OAI
/-! # One primitive address exponent for every pair of cofinality parameters -/
namespace Hierarchy.DescentSixParty.SeedNamed.ProfiledOrdinaryOffer
open Chronology Chronology.RegisterTimeline DescentCompiler DescentCompiler.TerminalScale DescentDatedAddressBook
open Filter
noncomputable section
set_option quotPrecheck false
variable {F : Type} [Field F] (G : PoweredGadget F) {n d : ℕ} (board : NonlinearExpanders.Graph n d)
  (op : RotorSpec) (t f g reset drift degreeMax : ℕ)
local notation "offer" τ:arg B:arg h:arg => ProfiledOrdinaryOffer G f g board op t reset τ drift degreeMax B h

theorem uniform_primitive : ∃C : ℕ,∀τ B,0<B→∀ᶠ h : ℕ in atTop,∀x : offer τ B h,
    x.model.primitiveRoof 0≤2^(C*h) :=by
  obtain ⟨C,roof⟩:=PhysicalOrdinary.uniform_primitive_aperture (F:=F) 8
  refine ⟨C,?_⟩
  intro τ B den
  let freq:=OrdinaryBooks.primitiveLocalRate G t f g reset
  filter_upwards [roof,raw_limits G board op t f g reset τ drift degreeMax B,
    OrdinaryBooks.primitive_date_local G op t f g reset τ B drift degreeMax den,
    dyadic_log_room freq 1,eventually_ge_atTop 1] with h final limits localBound small high
  intro x
  let J:=Nat.log 2 h/(2*B)
  let l:=x.model.paletteShape
  let s:=x.primitive_shape
  let r:=limits x
  have localSize : scale J freq≤2^h :=by
    apply Nat.pow_le_pow_right (by decide : 0<2)
    apply (Nat.mul_le_mul_left freq (Nat.add_le_add_right (Nat.div_le_self ..) 1)).trans
    simpa only [pow_one] using small
  have controls:=localBound x.slot.sites x.slot.age x.slot.p x.slot.degree (x.slot.menu.seats x.slot.age)
    x.slot.position.ports x.slot.grainLimit x.slot.degreeLimit
    (previous_nodes G board op t f g reset τ drift degreeMax B h x) x.firstWidth
  have low : l.lows≤2^h :=s.lows.le.trans (controls.2.2.2.2.2.2.trans localSize)
  have old : l.oldNodes≤2^h :=s.old.le.trans (controls.2.2.2.2.1.trans localSize)
  let X:=2^h
  let T:=2^(8*h)
  have grow : X≤T :=Nat.pow_le_pow_right (by decide : 0<2) (by omega)
  have pair : X*X≤T :=by
    change 2^h*2^h≤2^(8*h)
    rw [←pow_add]
    exact Nat.pow_le_pow_right (by decide) (by omega)
  have four : 2^(4*h)≤T :=Nat.pow_le_pow_right (by decide : 0<2) (by omega)
  have hosts : l.hosts≤T :=by
    apply s.hosts.le.trans
    exact (Nat.pow_le_pow_right (by decide) (Nat.clog_le_of_le_pow r.oldHost)).trans four
  have grp : l.groups≤X :=s.groups.le.trans r.newGroup
  have blk : l.blocks≤X :=s.blocks.le.trans r.blocks
  have cap : l.capacity≤T :=s.capacity.le.trans (r.wires.trans grow)
  have ports : l.ports≤T :=by
    apply s.ports.le.trans
    have up : _+1≤2^(h+1) :=(Nat.add_le_add_right r.degree 1).trans
      (by rw [pow_succ];have positive:=Nat.one_le_two_pow (n:=h);omega)
    apply (Nat.pow_le_pow_left up 4).trans
    rw [←pow_mul]
    exact Nat.pow_le_pow_right (by decide) (by omega)
  have word : h≤T := Nat.lt_two_pow_self.le.trans grow
  apply final x.model
  refine ⟨hosts,grp.trans grow,low.trans grow,blk.trans grow,ports,cap,old.trans grow,
    s.pitches.1.trans word,s.pitches.2.1.trans word,s.pitches.2.2.1.trans word,s.pitches.2.2.2.1.trans word,
    s.pitches.2.2.2.2.trans word,s.born.1.le.trans hosts,
    s.born.2.1.le.trans ((Nat.mul_le_mul grp blk).trans pair),s.born.2.2.1.le.trans (blk.trans grow),
    s.born.2.2.2.le.trans cap,?_⟩
  exact s.peak.trans ((Nat.div_le_self ..).trans (by omega))

end
end Hierarchy.DescentSixParty.SeedNamed.ProfiledOrdinaryOffer

end OAI
