import OAI.Hierarchy.DescentOrdinaryBirthWordTariff
import OAI.Hierarchy.DescentOrdinaryRefPagesCharge
import OAI.Hierarchy.DescentOrdinaryArgumentWidths
import OAI.Hierarchy.DescentNativePhaseInvoice

namespace OAI
/-! # The original four dictionary and row producers between prior retile and vector gather -/
namespace Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary
open DescentStaticWordColumn DescentPacking.PackedMatch.Local.Stage
noncomputable section
variable {F P : Type} [Field F] (v : PhysicalOrdinary F P)

def dictionaryCharge (A : ArgumentEntry v) (h u ratio : ℕ) :=
  let L:=A.population v 0
  let B:=v.bornBook
  let rows₀:=h+L.hosts*h+L.hosts*L.groups*u
  let rows₁:=h+B.hosts*h+B.hosts*B.groups*u
  let c₀:=1024+4096*(L.donors+1)
  let c₁:=2048*(B.fields+1)
  let c₂:=256*(v.reference.oldNodes+v.reference.count+1)
  c₀*ratio*rows₀+c₁*ratio*rows₁+(c₀+c₁+c₂)*ratio*2^(h/2)*h

theorem dictionary_charge (A : ArgumentEntry v) (floor w h u ratio : ℕ)
    (match_ : A.Match v floor) (bus : w≤ ratio*h) (fill : h≤ A.clip.working*u)
    (chip : DescentRawCablePanel.DepotRAM.totalBits (A.chip v).format*A.clip.working≤ h/2)
    (oldRole : A.roleBits*v.reference.oldNodes*A.clip.working≤ h/4)
    (counts : ((A.population v floor).countBits*(A.population v floor).donors+
      (A.population v floor).countBits)*A.clip.working≤ h/4)
    (chunk : (A.population v floor).chunkBits≤ h/4) (pages : (A.population v floor).count≤2^(h/4))
    (refs : v.reference.keyBits*A.clip.working≤ h/2)
    (old : v.reference.bits*v.reference.oldNodes*A.clip.working≤ h/2)
    (born : (v.bornBook.chipBits*1+v.bornBook.chipBits)*A.clip.working≤ h/2)
    (addresses : (v.refChart floor).endAddress<2^w) :
    ((A.chip v).phase (A.chipStart v floor) (A.chipSource v floor) w).wordInvoice+
      ((A.population v floor).phase (A.ports v floor) (A.labels v floor) w).wordInvoice+
      DateBill.bitTariff ((v.refChart floor).program w) (v.refTime floor)+
      DateBill.bitTariff (v.bornBook.program (A.chipBank v floor) (v.birthStart floor) w)
        (v.bornBook.ticks (A.chipBank v floor) (v.birthStart floor))≤ v.dictionaryCharge A h u ratio :=by
  let L:=A.population v floor
  let B:=v.bornBook
  let q:=h+L.hosts*h+L.hosts*L.groups*u
  let r:=h+B.hosts*h+B.hosts*B.groups*u
  have cp:=(A.chip v).word_bill (A.chipStart v floor) w h ratio u (A.chipSource v floor) chip fill bus
  have ct:=L.word_bill (A.ports v floor) (A.labels v floor) w h ratio u fill bus oldRole counts chunk pages
  have cR:=(v.refChart floor).word_bill h w ratio bus
    (show (v.refChart floor).digitBits≤ h/2 by change v.reference.bits*v.reference.oldNodes*v.reference.lanes≤_;rwa [match_.refPitch])
    (show (v.refChart floor).keyBits*(v.refChart floor).lanes≤ h/2 by change v.reference.keyBits*v.reference.lanes≤_;rwa [match_.refPitch])
    addresses
  have cB:=B.word_bill (v.birthStart floor) w h ratio u (A.chipBank v floor)
    (show (B.chipBits*1+B.chipBits)*B.lanes≤ h/2 by change _*v.bornBook.lanes≤_;rwa [match_.bornPitch])
    (show h≤ B.lanes*u by change h≤ v.bornBook.lanes*u;rwa [match_.bornPitch]) bus
  refine (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add cp ct) cR) cB).trans_eq ?_
  change (1024*ratio*(0+1)*q+1024*ratio*(0+1)*2^(h/2)*h)+
    (4096*ratio*(L.donors+1)*q+4096*ratio*(L.donors+1)*2^(h/2)*h)+
    256*ratio*(v.reference.oldNodes+v.reference.count+1)*2^(h/2)*h+
    (2048*ratio*(B.fields+1)*r+2048*ratio*(B.fields+1)*2^(h/2)*h)=
    (1024+4096*(L.donors+1))*ratio*q+(2048*(B.fields+1))*ratio*r+
      ((1024+4096*(L.donors+1))+2048*(B.fields+1)+256*(v.reference.oldNodes+v.reference.count+1))*ratio*2^(h/2)*h
  ring

theorem funded_dictionary_charge (A : ArgumentEntry v) (other floor w ratio : ℕ)
    (paid : 0<v.venue.paidBits) (input : v.venue.paidBits≤ v.area.unit)
    (purchase : 4*v.fundedMaxUnit (max (v.fullArgumentUnit A) other)*2^v.area.k≤ v.payload)
    (bus : w≤ ratio*v.payload) :
    let extra:=max (v.fullArgumentUnit A) other
    let W:=v.withFundedArguments extra A
    let E:=v.fundedEntry extra A
    ∀(_matching : E.Match W floor), (E.population W floor).chunkBits≤ v.payload/4 →
      (E.population W floor).count≤2^(v.payload/4) → (W.refChart floor).endAddress<2^w →
    ((E.chip W).phase (E.chipStart W floor) (E.chipSource W floor) w).wordInvoice+
      ((E.population W floor).phase (E.ports W floor) (E.labels W floor) w).wordInvoice+
      DateBill.bitTariff ((W.refChart floor).program w) (W.refTime floor)+
      DateBill.bitTariff (W.bornBook.program (E.chipBank W floor) (W.birthStart floor) w)
        (W.bornBook.ticks (E.chipBank W floor) (W.birthStart floor))≤ W.dictionaryCharge E v.payload (v.fundedWorkingUnit extra) ratio :=by
  intro extra W E «matching» chunk pages addr
  have caps:=v.funded_argument_bounds extra A paid input purchase
  have half {x : ℕ} (h : x≤ v.payload/4) : x≤ v.payload/2 :=by omega
  exact W.dictionary_charge E floor w v.payload (v.fundedWorkingUnit extra) ratio «matching» bus caps.fill₁
    (half (v.funded_argument_widths A other 3).1) (v.funded_argument_widths A other 1).1
    (v.funded_argument_widths A other 2).1 chunk pages
    (half (v.funded_argument_widths A other 4).1) (half (v.funded_argument_widths A other 5).1)
    (half (v.funded_argument_widths A other 6).1) addr

end
end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary

end OAI
