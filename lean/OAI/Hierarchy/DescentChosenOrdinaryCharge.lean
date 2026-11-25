import OAI.Hierarchy.DescentProfiledChosenOuterReturn
import OAI.Hierarchy.DescentProfiledMatchedInvoice
import OAI.Hierarchy.DescentProfiledDonorCharge
import OAI.Hierarchy.DescentProfiledArchiveProfileCharge
import OAI.Hierarchy.DescentProfiledRowCharge
import OAI.Hierarchy.DescentProfiledFundedRasterCharge
import OAI.Hierarchy.DescentProfiledPrimitiveCharge
import OAI.Hierarchy.DescentChosenArgumentPhase

namespace OAI
/-! # The attained word price for a registered ordinary descent, at the paid original row counts -/
namespace Hierarchy.DescentSixParty.SeedNamed.ProfiledOrdinaryOffer
open Chronology Chronology.RegisterTimeline DescentCompiler DescentCompiler.TerminalScale DescentDatedAddressBook
open DescentPacking.PackedMatch.Local.Stage DescentPackedColony DescentSIMDLookup Filter
open DescentInitialHost DescentMixedRouter DescentResetInvoice ProtocolRAM
noncomputable section
set_option quotPrecheck false
set_option hygiene false
variable {F : Type} [Field F] (G : PoweredGadget F) {n d : ℕ}
    (board : NonlinearExpanders.Graph n d) (op : RotorSpec) (t f g reset τ drift degreeMax B driftR ratio saving : ℕ)
local notation "idx" h:arg => ProfiledOrdinaryOffer G f g board op t reset τ drift degreeMax B h
local notation "J_" h:arg => Nat.log 2 h/(2*B)
local notation "tb_" h:arg => tail τ (J_ h)
local notation "S_" h:arg x:arg => stageNumbers G t (J_ h) f g reset (x:idx h).slot.sites (tb_ h)
local notation "k_" h:arg => groupBits t (J_ h) (hostRate t reset) (capRate G t g) (cutRate t f g)
local notation "prior_" x:arg => (x).slot.position.ports
local notation "seats_" x:arg => (x).slot.menu.seats (x).slot.age
local notation "args_" x:arg => (x).base.registeredEntry (prior_ x) (x).stageFloor
local notation "ext_" x:arg => (x).base.argumentUnitFrom (prior_ x) (x).stageFloor
local notation "room_" h:arg x:arg => (prior_ x).OrdinaryCodeRoom (x).cut.ticket op g (tb_ h) (x).slot.p f drift (x).slot.degree h (seats_ x) (x).slot.position.floor (x).slot.menu.ordinary


local notation "baseRate" => (NativePitch.FundedBase.public_rate G t f g reset).choose
local notation "argumentCost" => 600*Branch.selectedArgumentRate G t f g reset driftR (Branch.chosenClipRate G t f g reset driftR)
local notation "rasterCost" => fundedRasterExponent G t f g reset driftR
local notation "roleCost" => OrdinaryBooks.primitiveChargeRate G t f g reset driftR
local notation "radixCost" => groupRate G t f g reset
local notation "selectorCost" => matcherChargeRate G t f g reset
local notation "inputCost" a:arg b:arg => inputReadRate G t f g reset driftR baseRate (max a b)

def ordinaryUnitLead :=
  archiveProfileLead G ratio+ratio+privateDonorLead ratio+(ratio+1)+65*ratio+rowLead t reset (ratio+1)

def ordinaryExponent (argRead roleRead : ℕ) :=
  archiveProfileRate G t f g reset+selectorCost+privateDonorRate G t f g reset+returnRate G t f g reset+
    inputCost argRead roleRead+outerTailRate G t f g reset driftR+argumentCost+rasterCost+roleCost+radixCost

def ordinaryCutoff :=
  max 5 (max (2*((2+hostRate t reset*(t+1)+
    ((donorRates G t f g reset).amount+(donorRates G t f g reset).work)+1+1)+5))
    (max (returnCutoff G t f g reset) (OrdinaryBooks.primitiveLaneRate G t f g reset driftR+2)))

theorem chosen_ordinary_charge (argRead roleRead slots : ℕ)
    (bounds : ordinaryCutoff G t f g reset driftR ≤ B) :
    ∀ᶠ h : ℕ in atTop, ∀(x : idx h) (live : 0 < k_ h) (room : x.CodeRoom),
      PitchCalendar.Purchased G board op t f g reset drift driftR degreeMax slots ratio τ B h →
      drift+1 ≤ scale (J_ h) driftR → 2^h ≤ x.slot.sites → h ≤ x.slot.bus → x.slot.bus ≤ ratio*h →
      x.slot.bus+1 ≤ (ratio+1)*h → x.HeaderRoom → 0 < x.slot.p →
      (prior_ x).ArchivePitchRoom ((S_ h x).groupCount x.slot.age) h (scale (J_ h) argRead) (scale (J_ h) roleRead) →
      max x.endAt (x.model.signedGuard x.stageFloor)<2^x.slot.bus →
      (x.date live room).tariff ≤ x.Price (9*ordinaryUnitLead G t reset ratio)
        (ordinaryExponent G t f g reset driftR argRead roleRead) 5 saving :=by
  obtain ⟨five,timer,keep,prim⟩:=show 5 ≤ B ∧ _ ∧ _ ∧ _ from by
    simpa only [ordinaryCutoff,max_le_iff] using bounds
  have den : 0 < B:=by omega
  have old:=eventual_archive_profile_rows G board op t f g reset τ drift degreeMax B den (by simpa using timer)
  have matchPrice:=chosen_match_invoice G board op t f g reset τ drift degreeMax B den timer
  have privatePrice:=eventual_donor_rows G board op t f g reset τ drift degreeMax B den (by simpa using timer)
  have returnPrice:=chosen_return_charge G board op t f g reset τ drift degreeMax B ratio den keep
  have args:=chosen_argument_phase G board op t f g reset τ drift degreeMax B driftR (ratio+1) saving five
  have primitive:=eventual_profiled_primitive_charge G board op t f g reset τ drift degreeMax B driftR ratio prim
  have argRows:=charged_offer_rows G board op t f g reset τ drift degreeMax B (ratio+1) argumentCost saving
  have moneyRows:=charged_offer_rows G board op t f g reset τ drift degreeMax B ratio rasterCost saving
  have primitiveRows:=charged_offer_rows G board op t f g reset τ drift degreeMax B ratio roleCost saving
  filter_upwards [old,matchPrice,privatePrice,returnPrice,args,primitive,argRows,moneyRows,primitiveRows]
    with h loaded matched pair returned argProof role argRow cashRow primRow
  intro x live room buy dr stock hw bus inc header grain pitch guarded
  let S:=S_ h x
  let J:=J_ h
  let w:=x.slot.bus
  let e:=x.base.registeredEntry (prior_ x) x.stageFloor
  let floor:=x.stageFloor
  let E:=ordinaryExponent G t f g reset driftR argRead roleRead
  let L:=ordinaryUnitLead G t reset ratio
  let u:=x.Price L E 0 saving
  let residue:=x.slot.sites/(2^J)^saving
  have relax {a b s : ℕ} (l : a ≤ L) (r : b ≤ E) : x.Price a b s saving ≤ u+s*residue:= by
    apply (x.price_mono l r (le_refl s)).trans
    dsimp only [u,residue,Price,J]
    omega
  have enough : 2^h ≤ 2*x.slot.sites:=by omega
  have liveSites : 0 < x.slot.sites:=(Nat.two_pow_pos h).trans_le stock
  have hosts : 0 < S.hostSize x.slot.age := by
    change 0 < x.slot.sites*(2^S.hostGain*S.radix)^x.slot.age
    exact Nat.mul_pos liveSites (Nat.pow_pos (Nat.mul_pos (Nat.two_pow_pos _) (Nat.two_pow_pos _)))
  have head:=loaded x ratio w stock bus
  have first : x.archiveInvoice ≤ u:=by
    have h₀ : x.archiveInvoice ≤ x.Price (archiveProfileLead G ratio) (archiveProfileRate G t f g reset) 0 saving:=by
      simpa only [archiveInvoice,Price,zero_mul,Nat.add_zero] using head
    exact h₀.trans (x.price_mono (by dsimp only [L,ordinaryUnitLead];omega)
      (by dsimp only [E,ordinaryExponent];omega) le_rfl)
  have second : x.matchInvoice live ≤ u:=(matched x ratio saving enough hw bus guarded live).trans
    (x.price_mono (by dsimp only [L,ordinaryUnitLead];omega) (by dsimp only [E,ordinaryExponent];omega) le_rfl)
  have raw:=pair x ratio w stock hw bus header.1 room.endFit
  have third : x.privateFee ≤ u:=by
    have h₀ : x.privateFee ≤ x.Price (privateDonorLead ratio) (privateDonorRate G t f g reset) 0 saving:=by
      simpa only [privateFee,Price,zero_mul,Nat.add_zero] using raw
    exact h₀.trans (x.price_mono (by dsimp only [L,ordinaryUnitLead];omega)
      (by dsimp only [E,ordinaryExponent];omega) le_rfl)
  have fourth : x.returnInvoice room ≤ u:=by
    have h₀ : x.returnInvoice room ≤ x.Price (ratio+1) (returnRate G t f g reset) 0 saving:=by
      simpa only [Price,zero_mul,Nat.add_zero] using returned x enough hw bus guarded room
    exact h₀.trans (x.price_mono (by dsimp only [L,ordinaryUnitLead];omega)
      (by dsimp only [E,ordinaryExponent];omega) le_rfl)
  have ⟨initial,last⟩:=x.chosen_outer_return buy dr enough bus pitch saving room
  have reader : x.model.inputFee e floor w ≤ u:=initial.trans
    (x.price_mono (by dsimp only [L,ordinaryUnitLead];omega) (by dsimp only [E,ordinaryExponent];omega) le_rfl)
  have seventh : x.lastInvoice room ≤ u:=last.trans
    (x.price_mono (by dsimp only [L,ordinaryUnitLead];omega) (by dsimp only [E,ordinaryExponent];omega) le_rfl)
  let pg:Fin (7*x.model.vector.operands):=⟨0,Nat.mul_pos (by decide) room.slots⟩
  have work:=argProof x w x.slot.sites room pg buy.old buy.returned dr liveSites grain stock inc
  have originalRow:=argRow x ((ratio+1)*TerminalScale.scale J argumentCost*x.model.rowVolume h) stock hosts le_rfl
  have row₁ : (ratio+1)*TerminalScale.scale J argumentCost*x.model.rowVolume h ≤ u+residue:=by
    apply originalRow.trans
    simpa only [one_mul] using (relax (s:=1) (by dsimp only [L,ordinaryUnitLead];omega)
      (by dsimp only [E,ordinaryExponent];omega) :
      x.Price (rowLead t reset (ratio+1)) (argumentCost+radixCost) 1 saving≤_)
  have fifth : (x.dateSteps room).arguments.wordInvoice ≤ 2*u+3*residue:=by
    change (x.dateSteps room).arguments.wordInvoice ≤ x.model.inputFee e floor w+
      ((ratio+1)*TerminalScale.scale J argumentCost*x.model.rowVolume h)+2*residue at work
    omega
  have raster:=profiled_funded_raster_charge G board op t f g reset τ drift degreeMax B driftR ratio x room
    buy.old buy.returned dr hosts grain bus
  have rowLeadSmall : rowLead t reset ratio ≤ L:=by
    have small : rowLead t reset ratio ≤ rowLead t reset (ratio+1):=Nat.mul_le_mul_left _ (Nat.le_succ _)
    dsimp only [L,ordinaryUnitLead];omega
  have sixth : (x.dateSteps room).paid.wordInvoice ≤ u+residue:=by
    apply (cashRow x _ stock hosts raster).trans
    simpa only [one_mul] using (relax (s:=1) rowLeadSmall (by dsimp only [E,ordinaryExponent];omega) :
      x.Price (rowLead t reset ratio) (rasterCost+radixCost) 1 saving≤_)
  have made:=role x room buy.old dr liveSites grain bus
  have eighth : (x.dateSteps room).primitive.wordInvoice ≤ u+residue:=by
    apply (primRow x _ stock hosts made).trans
    simpa only [one_mul] using (relax (s:=1) rowLeadSmall (by dsimp only [E,ordinaryExponent];omega) :
      x.Price (rowLead t reset ratio) (roleCost+radixCost) 1 saving≤_)
  rw [x.charged_date]
  calc
    _ ≤ 9*u+5*residue:=eight_charges first second third fourth fifth sixth seventh eighth
    _ = _:=by dsimp only [u,residue,Price,E,L];ring

end
end Hierarchy.DescentSixParty.SeedNamed.ProfiledOrdinaryOffer

end OAI
