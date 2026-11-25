import OAI.Hierarchy.DescentOrdinaryOriginRasterTariff
import OAI.Hierarchy.DescentOrdinaryResolvingWordTariff
import OAI.Hierarchy.DescentOrdinaryArgumentWidths
import OAI.Hierarchy.DescentNativePhaseInvoice

namespace OAI
/-! # The native grain, eight conditioned ticket fields and seven-column resolver at the funded pitch -/
namespace Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary
open DescentDatedPriorOperand DescentStaticWordColumn ProtocolRAM
noncomputable section
variable {F P : Type} [Field F] (v : PhysicalOrdinary F P)

def resolverFactor (limit : ℕ) :=
  512+128*(v.resolver.jobs*8+1)*(limit+1)+16384*(v.resolver.pageFactor+1)

theorem resolver_charge (floor w h ratio unit limit : ℕ) (src : OriginSources v)
    (shape : v.VectorShape) (fit : v.endAddress floor<2^w)
    (packed : v.resolver.lanes*DescentPackedOperand.unit v.resolver.size≤ w/2)
    (work : ∀j f,(src j f).work≤ limit) (bus : w≤ ratio*h) (fill : h≤ v.resolver.lanes*unit)
    (prior : ((v.resolver.size+2)*v.resolver.nodes)*v.resolver.lanes≤ h/2)
    (splice : ((v.resolver.size+2)+(v.resolver.size+2))*v.resolver.lanes≤ h/2)
    (lookup : (11*(v.resolver.size+2))*v.resolver.lanes≤ h/2) :
    let l:=v.resolver
    (v.grainPhase floor w).wordInvoice+(v.rasterPhase floor src w).wordInvoice+
      (v.resolvePhase floor w shape fit packed).wordInvoice≤
      v.resolverFactor limit*ratio*(h+l.hosts*h+l.hosts*l.groups*unit)+
        16384*(l.pageFactor+1)*ratio*2^(h/2)*h :=by
  intro l
  let vol:=h+l.hosts*h+l.hosts*l.groups*unit
  have gr : (v.grainPhase floor w).wordInvoice≤512*ratio*vol :=
    DescentDatedPublicGrain.word_bill l w _ h unit ratio v.chosenGrain fill bus
  have issued : (v.rasterPhase floor src w).wordInvoice≤128*ratio*(l.jobs*8+1)*(limit+1)*vol :=
    v.origin.word_bill src (v.routedStart floor) w h unit ratio limit work fill bus
  have result : (v.resolvePhase floor w shape fit packed).wordInvoice≤
      16384*ratio*(l.pageFactor+1)*vol+16384*ratio*(l.pageFactor+1)*2^(h/2)*h :=
    (v.nativeArgs floor).word_bill (v.normalizedEnd floor) w h ratio unit bus fill prior splice lookup
  refine (Nat.add_le_add (Nat.add_le_add gr issued) result).trans_eq ?_
  change _=v.resolverFactor limit*ratio*vol+16384*(l.pageFactor+1)*ratio*2^(h/2)*h
  unfold resolverFactor
  change _=(512+128*(l.jobs*8+1)*(limit+1)+16384*(l.pageFactor+1))*ratio*vol+_
  ring

/-- On the selected date the three resolver dictionaries use exactly indices
eight, nine and ten of the incoming argument-width list. -/
theorem funded_resolver_charge (A : ArgumentEntry v) (other floor w ratio limit : ℕ)
    (paid : 0<v.venue.paidBits) (input : v.venue.paidBits≤ v.area.unit)
    (purchase : 4*v.fundedMaxUnit (max (v.fullArgumentUnit A) other)*2^v.area.k≤ v.payload)
    (bus : w≤ ratio*v.payload) :
    let extra:=max (v.fullArgumentUnit A) other
    let W:=v.withFundedArguments extra A
    let unit:=2^v.area.k*v.fundedWorkingUnit extra
    ∀(src : OriginSources W) (shape : W.VectorShape) (fit : W.endAddress floor<2^w)
      (packed : W.resolver.lanes*DescentPackedOperand.unit W.resolver.size≤ w/2),
      (∀j f,(src j f).work≤ limit) →
      (W.grainPhase floor w).wordInvoice+(W.rasterPhase floor src w).wordInvoice+
          (W.resolvePhase floor w shape fit packed).wordInvoice≤
        W.resolverFactor limit*ratio*(v.payload+W.resolver.hosts*v.payload+W.resolver.hosts*W.resolver.groups*unit)+
          16384*(W.resolver.pageFactor+1)*ratio*2^(v.payload/2)*v.payload :=by
  intro extra W unit src shape fit packed work
  have caps:=v.funded_argument_bounds extra A paid input purchase
  have half {x : ℕ} (h : x≤ v.payload/4) : x≤ v.payload/2:=by omega
  exact W.resolver_charge floor w v.payload ratio unit limit src shape fit packed work bus caps.fill₂
    (half (v.funded_argument_widths A other 8).2.2)
    (half (v.funded_argument_widths A other 9).2.2)
    (half (v.funded_argument_widths A other 10).2.2)

end
end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary

end OAI
