import OAI.Hierarchy.DescentDatedScheduleSpace
import OAI.Hierarchy.DescentAllDateDonorWidth
import OAI.Hierarchy.DescentDonorMatcherSpace
import OAI.Hierarchy.DescentDatedOrdinaryRate

namespace OAI
/-! # Numerical rows and matching alphabets of every ordinary date -/
namespace Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary
open DescentDatedAddressBook DescentSixParty DescentSixParty.Chronology DescentCompiler DescentCompiler.TerminalScale
open DescentPacking.PackedMatch.Local.Stage DescentPackedColony ProtocolRAM Filter
noncomputable section
set_option quotPrecheck false

variable {F : Type} [Field F] (G : PoweredGadget F) {ι : ℕ→Type*} (t f g reset τ B : ℕ)
  (sites age p : ∀h,ι h→ℕ)
local notation "J_" h:arg => Nat.log 2 h/(2*B)
local notation "S_" h:arg i:arg => stageNumbers G t (J_ h) f g reset (sites h i) (τ*(J_ h+1))
local notation "k_" h:arg =>groupBits t (J_ h) (hostRate t reset) (capRate G t g) (cutRate t f g)
local notation "d_" h:arg i:arg =>DonorDate.atDate G (S_ h i) g (k_ h) (age h i) (p h i)
local notation "a_" h:arg i:arg n:arg =>(d_ h i).schedule h n ((S_ h i).censusBits (p h i))

structure OrdinaryGeometry : Prop where
  axis : ScheduleSpace G t f g reset τ B sites age
  blocks : Bounded (fun h (_:ι h)=>2^(k_ h))
  degree : Bounded (fun h i=>(d_ h i).degree)
  cap : Bounded (fun h i=>(d_ h i).cap)
  batch : Bounded (fun h i=>(S_ h i).batch)
  unit : SmallAt (fun h=>J_ h) (fun h i=>(d_ h i).amount)

/-- The original input may itself vary over all sizes admitted at a height.
The stage count and even the complete epoch seat census still fit a linear address width. -/
theorem ordinary_geometry (source : Bounded sites) (live : ∀h i,age h i≤(S_ h i).length) :
    OrdinaryGeometry G t f g reset τ B sites age p :=by
  let κ:=1+(hostRate t reset+capRate G t g)*(t+1)+8+cutRate t f g
  let a:=capRate G t g
  let c:=hostRate t reset
  have axes:=schedule_space G t f g reset τ B sites age source live
  have init:=schedule_space G t f g reset τ B sites (fun _ _=>0) source (fun _ _=>Nat.zero_le _)
  have rooms : ∀ᶠ h:ℕ in atTop,J_ h≤h:=Eventually.of_forall fun h=>(Nat.div_le_self ..).trans (Nat.log_le_self 2 h)
  have blockRate : SmallAt (fun h=>J_ h) (fun h (_:ι h)=>2^(k_ h)) :=
    ⟨κ,Eventually.of_forall fun h i=>Nat.pow_le_pow_right (by decide) (groupBits_linear ..)⟩
  have blocks:=blockRate.bounded rooms
  have degree : Bounded (fun h i=>(d_ h i).degree):=(Bounded.const (DescentDatedSeedStartup.initialDegreeMax t)).of_le
    (fun h i=>DescentDatedSeedStartup.seed_degree ..)
  have caps : SmallAt (fun h=>J_ h) (fun h i=>(d_ h i).cap) :=by
    refine ⟨8+a*(t+1),Eventually.of_forall fun h i=>?_⟩
    apply (NativePitch.all_caps G t g (J_ h) (age h i)).trans
    apply Nat.pow_le_pow_right (by decide)
    change 8+a*((t+1)*(J_ h))≤(8+a*(t+1))*(J_ h+1)
    ring_nf
    omega
  have copies : Bounded (fun h i=>(S_ h i).copies):=by
    apply (init.oldGroup.mul blocks).of_le
    intro h i
    change (S_ h i).baseGroups*((S_ h i).radix^((S_ h i).length+1))≤
      ((S_ h i).baseGroups*(S_ h i).radix^((S_ h i).length-0))*(S_ h i).radix
    rw [Nat.sub_zero,pow_succ,Nat.mul_assoc]
  have power (a b : ℕ) : SmallAt (fun h=>J_ h) (fun h (_:ι h)=>2^(b+a*((t+1)*(J_ h)))) :=by
    refine ⟨b+a*(t+1),Eventually.of_forall fun h i=>?_⟩
    apply Nat.pow_le_pow_right (by decide)
    change b+a*((t+1)*(J_ h))≤(b+a*(t+1))*(J_ h+1)
    ring_nf
    omega
  have growth:=((power c 0).bounded rooms)
  have final:=((power a 11).bounded rooms)
  have seats : Bounded (fun h i=>(S_ h i).batch):=by
    apply (((source.mul copies).mul growth).mul final).of_le
    intro h i
    change ((sites h i*(S_ h i).copies)*(2^c)^((t+1)*(J_ h)))*2^(11+a*((t+1)*(J_ h)))≤_
    rw [←pow_mul,Nat.zero_add]
  obtain ⟨K,measure⟩:=NativePitch.all_donor_rate G t f g reset
  exact ⟨axes,blocks,degree,caps.bounded rooms,seats,⟨K,Eventually.of_forall
    fun h i=>(measure (J_ h) (sites h i) (τ*(J_ h+1)) (p h i) (age h i)).2⟩⟩

theorem OrdinaryGeometry.matcher (geo : OrdinaryGeometry G t f g reset τ B sites age p)
    (seats : ∀h,ι h→ℕ) (capacity : ∀h i,seats h i≤(S_ h i).batch)
    (digits : ∀h i,(S_ h i).censusBits (p h i)≤2^(k_ h)) :
    Dated.Ordinary.ScalarRoom (fun h i=>a_ h i (seats h i)) ∧
    ∀h i,DescentPacking.PackedMatch.SixBirths.unit (a_ h i (seats h i)).shapeAt≤(d_ h i).amount :=by
  have widths (h) (i:ι h) := (d_ h i).matcher_widths ((S_ h i).censusBits (p h i))
    (DonorDate.dated_cap_pos ..) (digits h i)
  exact ⟨⟨geo.axis.oldHost.padded,geo.axis.oldGroup,geo.blocks,geo.degree,geo.cap,geo.batch.of_le capacity,
    ⟨1,Eventually.of_forall fun h _ => by
      change h ≤ 1*h
      rw [Nat.one_mul]⟩,fun h i=>(widths h i).1,fun h i=>(widths h i).2.1,
    fun h i=>(widths h i).2.2.1⟩,fun h i=>(widths h i).2.2.2.2⟩

end
end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary

end OAI
