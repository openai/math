import OAI.Hierarchy.DescentProfiledOrdinaryUniformAxes
import OAI.Hierarchy.DescentProfiledOrdinaryCeiling

namespace OAI
/-! The public profile decode, orientation tables, donors and count plane share
one address exponent across all tail lengths and logarithmic divisors. -/
namespace Hierarchy.DescentSixParty.SeedNamed.ProfiledOrdinaryOffer
open Chronology Chronology.RegisterTimeline DescentCompiler DescentCompiler.TerminalScale DescentDatedAddressBook
open DescentSIMDLookup DescentPacking.PackedMatch DescentPacking.PackedMatch.Local.Stage Filter
noncomputable section
set_option quotPrecheck false
variable {F : Type} [Field F] (G : PoweredGadget F) {n d : ℕ}
    (board : NonlinearExpanders.Graph n d) (op : RotorSpec) (t f g reset drift bound : ℕ)
local notation "offer" τ:arg B:arg h:arg => ProfiledOrdinaryOffer G f g board op t reset τ drift bound B h
local notation "J_" B:arg h:arg => Nat.log 2 h/(2*B)
local notation "S_" τ:arg B:arg h:arg x:arg =>stageNumbers G t (J_ B h) f g reset (x:offer τ B h).slot.sites (tail τ (J_ B h))
local notation "k_" B:arg h:arg =>groupBits t (J_ B h) (hostRate t reset) (capRate G t g) (cutRate t f g)

private structure Admitted (h : ℕ) where
  τ : ℕ
  B : ℕ
  source : offer τ B h
  limits : RawLimits G board op t f g reset τ drift bound B h source
  digits : (S_ τ B h source).censusBits source.slot.p ≤ 2^(k_ B h)

local notation "adm" h:arg => Admitted G board op t f g reset drift bound h
local notation "v_" h:arg i:arg => (i:adm h).source.model
local notation "schedule" h:arg i:arg => S_ (i:adm h).τ (i:adm h).B h (i:adm h).source

private theorem admitted_preliminary :
    Bounded (fun h (i:adm h)=>preliminary G board op t f g reset i.τ drift bound i.B h i.source) :=by
  let a:=fun h (i:adm h)=>(v_ h i).area
  let seats:=fun h (i:adm h)=>i.source.slot.menu.seats i.source.slot.age
  let dates:=fun h (i:adm h)=>DonorDate.atDate G (schedule h i) g (k_ i.B h) i.source.slot.age i.source.slot.p
  let boards:=fun h (i:adm h)=>(schedule h i).censusBits i.source.slot.p
  let real:=fun h (i:adm h)=>(dates h i).schedule h (seats h i) (boards h i)
  have same:a=real:=by funext h i;exact congrArg PhysicalOrdinary.StaticCore.area i.source.core
  have witnesses (h) (i:adm h):=(dates h i).matcher_widths (boards h i) (DonorDate.dated_cap_pos ..) i.digits
  have H : Bounded (fun h (i:adm h)=>(schedule h i).hostSize i.source.slot.age):=⟨4,Eventually.of_forall fun _ i=>i.limits.oldHost⟩
  have G₀ : Bounded (fun h (i:adm h)=>(schedule h i).groupCount i.source.slot.age):=⟨1,Eventually.of_forall fun _ i=>by simpa only [one_mul] using i.limits.oldGroup⟩
  have X₀ : Bounded (fun h (i:adm h)=>2^(k_ i.B h)):=⟨1,Eventually.of_forall fun _ i=>by simpa only [one_mul] using i.limits.blocks⟩
  have D : Bounded (fun h (i:adm h)=>(dates h i).degree):=⟨1,Eventually.of_forall fun _ i=>by simpa only [one_mul] using i.limits.degree⟩
  have cap : Bounded (fun h (i:adm h)=>(dates h i).cap):=⟨1,Eventually.of_forall fun _ i=>by simpa only [one_mul] using i.limits.wires⟩
  have seatRoom : Bounded seats:=⟨6,Eventually.of_forall fun _ i=>i.source.seats.trans i.limits.batch⟩
  have shape : Dated.Ordinary.ScalarRoom real:=⟨H.padded,G₀,X₀,D,cap,seatRoom,⟨1,Eventually.of_forall (fun _ _=>by simp [real,DonorDate.schedule])⟩,
    fun h i=>(witnesses h i).1,fun h i=>(witnesses h i).2.1,fun h i=>(witnesses h i).2.2.1⟩
  have area : Dated.Ordinary.ScalarRoom a:=same.symm ▸ shape
  have six (h) (i:adm h) : SixBirths.unit (a h i).shapeAt ≤ (a h i).unit:=by
    rw [same]
    exact (witnesses h i).2.2.2.2
  have prof:=PhysicalOrdinary.profile_extent_room G real seats seatRoom (fun _ _=>rfl) (fun _ _=>rfl)
    (fun h i=>(witnesses h i).2.2.2.2)
  have pl:Bounded (fun h (i:adm h)=>(v_ h i).profileRepack.endAddress 0):=ProfileRepack.extent_rate _ prof
  have rotation:=Dated.Ordinary.rotation_rate a (fun h (i:adm h)=>(v_ h i).old) area six
  have donors:=Dated.Ordinary.donor_width_rate a area
  have height (h) (i:adm h) : (a h i).payload=h := by
    rw [same]
    rfl
  have count : Bounded (fun h (i:adm h)=>2^(v_ h i).countBits):=by
    apply Bounded.pow_of_linear (K:=1)
    apply Eventually.of_forall
    intro h i
    have word:(a h i).unit*(a h i).lanesAt ≤ h/2:=by
      have actual:=lanes_fit (a h i).payload (a h i).unit
      calc
        _ ≤ (a h i).payload/2 := by
          simpa only [Dated.Ordinary.lanesAt,Nat.mul_comm (a h i).unit] using actual
        _ = h/2 := by rw [height h i]
    have field:(a h i).shapeAt.outputBits ≤ SixBirths.unit (a h i).shapeAt:=(Nat.le_add_left ..).trans (Nat.le_max_left ..)
    rw [Nat.one_mul]
    change (a h i).shapeAt.outputBits*(a h i).lanesAt ≤ h
    exact ((Nat.mul_le_mul_right _ (field.trans (six h i))).trans word).trans (Nat.div_le_self ..)
  have ambient : Bounded (fun h (_:adm h)=>h):=
    ⟨1,Eventually.of_forall fun h _=>by simpa only [one_mul] using (Nat.lt_two_pow_self (n:=h)).le⟩
  have lanes : Bounded (fun h (i:adm h)=>(a h i).lanesAt):=ambient.of_le fun h i=>
    (Nat.div_le_self (a h i).payload _).trans (height h i).le
  have rows:Bounded (fun h (i:adm h)=>chunks (a h i).G (a h i).lanesAt):=
    (area.groups.add lanes).of_le fun _ _=>(Nat.div_le_self ..).trans (Nat.sub_le ..)
  have batch:Bounded (fun h (i:adm h)=>(a h i).batch):=by
    simpa only [Dated.Ordinary.batch,Nat.pow_succ] using (((area.radix.mul (Bounded.const 2)).mul area.hosts).mul rows)
  exact (((pl.add rotation).add donors).add count).add batch

theorem uniform_preliminary :
    ∃C:ℕ,∀τ B,0 < B → ∀ᶠ h:ℕ in atTop,∀x:offer τ B h,preliminary G board op t f g reset τ drift bound B h x ≤ 2^(C*h):=by
  obtain ⟨C,price⟩:=admitted_preliminary G board op t f g reset drift bound
  refine ⟨C,?_⟩
  intro τ B pos
  filter_upwards [price,raw_limits G board op t f g reset τ drift bound B,census_board_room G t f g reset B pos] with h all caps digits
  intro x
  exact all ⟨τ,B,x,caps x,digits _ _ _ x.slot.grainLimit⟩

end
end Hierarchy.DescentSixParty.SeedNamed.ProfiledOrdinaryOffer

end OAI
