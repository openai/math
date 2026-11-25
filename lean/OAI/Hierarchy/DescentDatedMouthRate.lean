import OAI.Hierarchy.DescentDatedMouthExtent
import OAI.Hierarchy.DescentDatedWOriginPrice
import OAI.Hierarchy.DescentDatedAddressRate

namespace OAI
/-! The true post-vector aperture for the actor-origin registers and the three returned
newborn fields has a single exponential address bound on all ordinary dates. -/
namespace Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary
open DescentDatedAddressBook DescentOrdinaryOriginMask DescentSIMDLookup DescentOrdinaryOriginPorts Filter
noncomputable section
variable {F P : Type} [Field F] (v : PhysicalOrdinary F P) (extra : ℕ)
set_option quotPrecheck false
local notation "dateₘ" => v.withFundedClip extra
local notation "Lₘ" => (dateₘ).mouthChart rfl
local notation "Rₘ" => (dateₘ).originChart
local notation "Mₘ" => (v.fundedClip extra).postPitch
local notation "rₘ" => (v.fundedClip extra).radix

theorem origin_mouth_extent (same : (dateₘ).bornBook.groups=v.vector.groups*rₘ)
    (mouth : v.mouthPeak extra≤extra) (origin : (Rₘ).peak≤extra) :
    let q:=v.vector.lows
    let e:=2^(v.payload/2)
    let z:=chunks v.vector.groups Mₘ
    let f:=(dateₘ).bornBook.fields
    let n:=(Lₘ).pages
    (dateₘ).originControlWords+(dateₘ).originMouthWords≤
      ((4+3*rₘ)*e+2*(q*(v.vector.hosts*z))+(5*rₘ+2)*((v.vector.hosts*q)*z)+8+
        (1+v.resolver.nodes*6)*(2*e))+
      ((16+4*f)+(2*(1+f)+3*rₘ)*e+(2*f+2*n*q+5*n*q*rₘ+2*q)*((dateₘ).bornBook.hosts*z)) :=by
  intro q e z f n
  have first:=(v.funded_extra_fit extra (dateₘ).bornBook.chipBits ((Nat.le_max_left ..).trans mouth)).1
  have last:=(v.funded_extra_fit extra (Lₘ).bits ((Nat.le_max_right ..).trans mouth)).2.1
  have bits : ((dateₘ).bornBook.chipBits*1+(dateₘ).bornBook.chipBits)*(dateₘ).bornBook.lanes≤v.payload/2:=by
    rw [Nat.mul_one,Nat.add_mul]
    change (dateₘ).bornBook.chipBits*(v.fundedClip extra).working+
      (dateₘ).bornBook.chipBits*(v.fundedClip extra).working≤v.payload/2
    omega
  have backed:=(Lₘ).extent_any 0 v.payload (Nat.two_pow_pos _) rfl same bits (by
    change ((Lₘ).bits*rₘ)*Mₘ ≤ v.payload/2
    omega)
  have actor:=v.funded_origin_area (C:=(dateₘ).reference) (l:=(dateₘ).vector) extra v.resolver.nodes (dateₘ).originBits 0 origin
  have six:=v.funded_origin_ports extra origin
  simp only [Nat.zero_add] at actor backed
  exact Nat.add_le_add (Nat.add_le_add actor six) backed

variable {ι : ℕ→Type*}
theorem origin_mouth_rate {Pins : ∀h,ι h→Type} (dates : ∀h (i : ι h),PhysicalOrdinary F (Pins h i)) (amount : ∀h,ι h→ℕ)
    (caps : ∀ᶠ h : ℕ in atTop, ∀i,let v:=dates h i;let extra:=amount h i;let c:=v.fundedClip extra
      let d:=v.withFundedClip extra
      d.bornBook.groups=v.vector.groups*c.radix ∧ v.mouthPeak extra≤extra ∧ d.originChart.peak≤extra)
    (hosts : Bounded (fun h i=>(dates h i).vector.hosts)) (birth : Bounded (fun h i=>(dates h i).bornBook.hosts))
    (groups : Bounded (fun h i=>(dates h i).vector.groups)) (lows : Bounded (fun h i=>(dates h i).vector.lows))
    (nodes : Bounded (fun h i=>(dates h i).resolver.nodes)) (args : Bounded (fun h i=>(dates h i).vector.operands))
    (capacity : Bounded (fun h i=>(dates h i).reference.capacity))
    (radix : Bounded (fun h i=>2^(dates h i).area.k))
    (lanes : Bounded (fun h i=>((dates h i).fundedClip (amount h i)).postPitch))
    (payload : ∀ᶠ h : ℕ in atTop, ∀i,(dates h i).payload≤h) :
    Bounded (fun h i=>let d:=(dates h i).withFundedClip (amount h i);d.originControlWords+d.originMouthWords) :=by
  let v:=dates
  let cst (n : ℕ):=Bounded.const (ι:=ι) n
  have e : Bounded (fun h i=>2^((v h i).payload/2)):=Bounded.pow_of_linear (K:=1) (by
    filter_upwards [payload] with h fit
    exact fun i=>by simpa only [Nat.one_mul] using (Nat.div_le_self _ 2).trans (fit i))
  have chunk : Bounded (fun h i=>chunks (v h i).vector.groups ((v h i).fundedClip (amount h i)).postPitch):=
    (groups.add lanes).of_le (fun _ _=>(Nat.div_le_self ..).trans (Nat.sub_le ..))
  have f:=((((radix.mul capacity).mul (cst 6)).mul args).mul (cst 7))
  have n:=args.mul (cst 3)
  have oldPart:=((((((cst 4).add ((cst 3).mul radix)).mul e).add
    ((cst 2).mul (lows.mul (hosts.mul chunk)))).add
    ((((cst 5).mul radix).add (cst 2)).mul ((hosts.mul lows).mul chunk))).add (cst 8)).add
    (((cst 1).add (nodes.mul (cst 6))).mul ((cst 2).mul e))
  have band:=((((cst 2).mul f).add (((cst 2).mul n).mul lows)).add
    ((((cst 5).mul n).mul lows).mul radix)).add ((cst 2).mul lows)
  have newPart:=(((cst 16).add ((cst 4).mul f)).add
    ((((cst 2).mul ((cst 1).add f)).add ((cst 3).mul radix)).mul e)).add (band.mul (birth.mul chunk))
  obtain ⟨k,forecast⟩:=oldPart.add newPart
  refine ⟨k,?_⟩
  filter_upwards [caps,forecast] with h ok high
  intro i
  exact ((v h i).origin_mouth_extent (amount h i) (ok i).1 (ok i).2.1 (ok i).2.2).trans (high i)

end
end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary

end OAI
