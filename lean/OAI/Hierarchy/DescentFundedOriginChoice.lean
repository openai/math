import OAI.Hierarchy.DescentDatedWOriginPrice
import OAI.Hierarchy.DescentOrdinaryOriginBounds
import OAI.Hierarchy.DescentOrdinaryWordTariff

namespace OAI
/-! # Add the original actor width to the dated ingress purchase and charge its true selector -/
namespace Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary
open DescentCompiler.TerminalScale DescentOrdinaryVenueIngress DescentOrdinaryOriginBounds
open DescentOrdinaryReferenceInputs DescentPacking.PackedMatch.Local.Stage Filter
noncomputable section
variable {F P : Type} [Field F] (v : PhysicalOrdinary F P)

def originWidthAt :=originWidth v.area.D (2^v.area.k) v.reference.oldNodes v.reference.capacity v.resolver.nodes
def originExtra (earlier : ℕ) :=max earlier v.originWidthAt

theorem peak_at (extra : ℕ) :
    (v.withFundedClip extra).originChart.peak=v.originWidthAt:=rfl

theorem enlarged_peak (earlier : ℕ) :
    (v.withFundedClip (v.originExtra earlier)).originChart.peak≤v.originExtra earlier:=le_max_right ..

theorem unit_at (earlier fresh : ℕ) :
    v.fundedMaxUnit (max earlier fresh)=max (v.fundedMaxUnit earlier) fresh:=by
  change max v.fundedPanelUnit (max v.area.unit (max (v.fundedClip earlier).localUnit (max v.fundedUnit (max earlier fresh))))=
    max (max v.fundedPanelUnit (max v.area.unit (max (v.fundedClip earlier).localUnit (max v.fundedUnit earlier)))) fresh
  simp only [max_assoc]

theorem enlarged_room (earlier : ℕ) (paid : 4*v.fundedMaxUnit earlier*2^v.area.k≤v.payload)
    (origin : 4*v.originWidthAt*2^v.area.k≤v.payload) :
    4*v.fundedMaxUnit (v.originExtra earlier)*2^v.area.k≤v.payload :=by
  rw [originExtra,unit_at]
  rcases le_total (v.fundedMaxUnit earlier) v.originWidthAt with new_|old
  · rwa [max_eq_right new_]
  · rwa [max_eq_left old]

theorem future_enlarged_room (a B : ℕ) (positive : 0<B) (cut : 20*a≤B) :
    ∀ᶠ h : ℕ in atTop, let J:=Nat.log 2 h/(2*B)
    ∀(v : PhysicalOrdinary F P) (earlier : ℕ), let U:=scale J a
    8≤U→v.area.D+1≤U→2^v.area.k≤U→v.reference.oldNodes≤U→v.reference.capacity≤U→v.resolver.nodes≤U→
    v.payload=h→4*v.fundedMaxUnit earlier*2^v.area.k≤h→4*v.fundedMaxUnit (v.originExtra earlier)*2^v.area.k≤h :=by
  filter_upwards [cofinal a B positive cut] with h aperture
  intro J v earlier U large degree radix previous cap next paid old
  have bought:=aperture v.area.D (2^v.area.k) v.reference.oldNodes v.reference.capacity v.resolver.nodes
    large degree radix previous cap next
  rw [←paid] at old bought ⊢
  exact v.enlarged_room earlier old bought

variable (earlier : ℕ) (A : ArgumentEntry v)
local notation "extra" => v.originExtra earlier
local notation "W" => v.withFundedArguments extra A
local notation "r" => 2^v.area.k
local notation "h" => v.payload
local notation "H" => v.vector.hosts
local notation "J" => v.vector.groups
local notation "Q" => v.vector.lows

theorem funded_argument_origin_fee (D : Directory (W).reference (W).vector) (pg : Fin (W).vector.pageCount)
    (floor bits w ratio : ℕ) (paid : 0<v.venue.paidBits) (input : v.venue.paidBits≤v.area.unit)
    (room : 4*v.fundedMaxUnit extra*r≤h) (bus : w≤ratio*h) :
    let code:=(W).originPrefix floor bits w (D.refs pg)
    DateBill.bitTariff code.program code.ticks≤ratio*(2600*(Q+1)*h+
      (160+300*r)*((H*Q)*h+(H*Q)*J*(r*v.fundedWorkingUnit extra))+
      115*((4+r)*2^(h/2))*h+(109+115*((1+v.resolver.nodes*6)*(2*2^(h/2))))*h) :=by
  let p:PhysicalOrdinary F P:={v with ingressWords:=(W).ingressWords}
  exact p.funded_w_origin extra D pg floor bits w ratio (v.enlarged_peak earlier) paid input room bus

end
end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary

end OAI
