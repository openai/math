import OAI.Hierarchy.DescentOrdinaryOriginInvoice
import OAI.Hierarchy.DescentFundedClipChoice
import OAI.Hierarchy.DescentOrdinaryReferenceInputs
import OAI.Hierarchy.DescentOrdinaryRoleControlPrice
import OAI.Hierarchy.DescentOrdinaryOriginScaledInvoice

namespace OAI
/-! # Origin publication at the working and output pitches of the funded ordinary date -/
namespace Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary
open DescentOrdinaryOriginMask DescentOperandVectorArena DescentOrdinaryReferenceInputs
open DescentSIMDLookup DescentStaticWordColumn ProtocolRAM
noncomputable section
set_option quotPrecheck false
variable {F P : Type} [Field F] (v : PhysicalOrdinary F P)

def originReturn (extra : ℕ) (C : DescentOrdinaryRefsROM.Chart) (l : Layout)
    (newNodes ordinalBits : ℕ) : Return :=
  ⟨C.degree,C.k,C.oldNodes,C.capacity,newNodes,ordinalBits,l.hosts,l.lows,l.groups,
    (v.fundedClip extra).radix,(v.fundedClip extra).postPitch⟩

variable {C : DescentOrdinaryRefsROM.Chart} {l : Layout} (directory : Directory C l)

theorem origin_sources (pg : Fin l.pageCount) (i : Fin l.lows) :
    (directory.refs pg i).want.work+(directory.refs pg i).addr.work+(directory.refs pg i).counts.work≤26 :=by
  have real:=directory.population.controls_work directory.rootPorts (Fin.cast directory.sites.symm i)
  change (directory.population.want directory.rootPorts _).work+7+directory.population.counts.work≤26
  omega

variable (extra newNodes ordinalBits : ℕ)
local notation "R" => v.originReturn extra C l newNodes ordinalBits
local notation "h" => v.payload
local notation "r" => (v.fundedClip extra).radix
local notation "M" => (v.fundedClip extra).postPitch

theorem funded_origin_room (selection : (R).peak≤extra) :
    (R).peak*(M*r)≤h/2 :=by
  have bound:=(v.funded_extra_fit extra (R).peak selection).1
  change (R).peak*(M*r)≤h/4 at bound
  omega

theorem funded_origin_area (base : ℕ) (selection : (R).peak≤extra) :
    (R).finish base≤base+(4+3*r)*2^(h/2)+2*(l.lows*(R).grid.rows)+(5*r+2)*(R).grid.nextRows+8 :=
  (R).funded_extent base (v.funded_origin_room (C:=C) (l:=l) extra newNodes ordinalBits selection)

theorem funded_origin_words (base w : ℕ) (pg : Fin l.pageCount) (selection : (R).peak≤extra) :
    (R).ticks (directory.refs pg) base+7*names ((R).program (directory.refs pg) w base)≤
    2600*(l.lows+1)+160*(l.lows*(R).grid.rows)+300*(r*(R).grid.nextRows)+115*((4+r)*2^(h/2)) :=
  (R).origin_table_bill (directory.refs pg) w base (origin_sources directory pg)
    (v.funded_origin_room (C:=C) (l:=l) extra newNodes ordinalBits selection)

/-- Cost in bits using the old donor's true fill, the physical clip and its
successor pitch. The lookup is charged once per date and block. -/
theorem funded_origin_scaled (base w ratio : ℕ) (pg : Fin l.pageCount) (selection : (R).peak≤extra)
    (paid : 0<v.venue.paidBits) (input : v.venue.paidBits≤v.area.unit)
    (wide : 4*v.fundedMaxUnit extra*2^v.area.k≤h) (bus : w≤ratio*h) :
    ((R).ticks (directory.refs pg) base+7*names ((R).program (directory.refs pg) w base))*w≤
    ratio*(2600*(l.lows+1)*h + (160+300*r)*
      ((l.hosts*l.lows)*h+(l.hosts*l.lows)*l.groups*(r*v.fundedWorkingUnit extra))+
      115*((4+r)*2^(h/2))*h) :=by
  exact (R).scaled_bill (directory.refs pg) base w ratio h (r*v.fundedWorkingUnit extra)
    (origin_sources directory pg) (v.funded_origin_room (C:=C) (l:=l) extra newNodes ordinalBits selection)
    (v.funded_bounds extra paid input wide).fill₂ bus

end
end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary

end OAI
