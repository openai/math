import OAI.Hierarchy.DescentPhysicalOrdinaryReturn
import OAI.Hierarchy.DescentPublishedVenueInvoice
import OAI.Hierarchy.DescentOrdinaryMetadataWordTariff
import OAI.Hierarchy.DescentOrdinaryFinalWordTariff
import OAI.Hierarchy.DescentOrdinaryCountWordTariff
import OAI.Hierarchy.DescentOrdinaryTailFactors

namespace OAI
/-! # Actual ordinary return from funded geometry through the seven operand shelves and final count -/
namespace Hierarchy.DescentSixParty
open DescentSIMDLookup DescentPacking.PackedMatch.Local.Stage DescentPacking.PackedMatch.Local.Stage.DateBill
open DescentStaticWordColumn ProtocolRAM
noncomputable section

namespace StageVenueTail.Date
variable (d : Date) (h u : ℕ)
structure SourceRows : Prop where
  positive : 0<d.signedLanes ∧ 0<d.paidLanes ∧ 0<d.aliveLanes ∧ 0<d.lanes
  rows : ∀m ∈ [d.signedLanes,d.paidLanes,d.aliveLanes,d.lanes],
    d.hosts*chunks d.groups m*h≤d.hosts*h+d.hosts*d.groups*u
  bounds : d.signedLanes≤h ∧ d.paidLanes≤h ∧ d.lanes≤h/2
  signed : DescentSignedCableCodec.width d.degree d.cap*d.signedLanes≤h/2
  paid : d.paidBits*d.paidLanes≤h/2
  alive : d.aliveLanes≤h/2

theorem SourceRows.bill {d : Date} {h u : ℕ} (a : d.SourceRows h u) (B : Sources) (base w ratio : ℕ)
    (bus : w≤ratio*h) :
    bitTariff (d.program B base w) (d.ticks B base)≤
      (d.wordCoefficients ratio).1*(h+2*d.hosts*h+2*d.hosts*d.groups*u)+
      (d.wordCoefficients ratio).2*(2*(h+1)^2*2^(h/2))*h :=by
  obtain ⟨p,q,r,s⟩:=a.positive
  exact d.word_bill_rows B base w h u u u u u ratio p q r s le_rfl le_rfl le_rfl le_rfl bus
    (a.rows _ (by simp)) (a.rows _ (by simp)) (a.rows _ (by simp)) (a.rows _ (by simp))
    a.bounds.1 a.bounds.2.1 a.bounds.2.2 a.signed a.paid a.alive
end StageVenueTail.Date

namespace Chronology.PhysicalOrdinary
variable {F P : Type} [Field F] (v : PhysicalOrdinary F P)
local notation "c" => v.nodeChart
local notation "r" => v.resolver
local notation "a" => v.area
local notation "d" => v.venue
local notation "f" => v.finalChart
local notation "h" => v.payload

structure ShelfRows (u R : ℕ) : Prop where
  positive : 0<u
  wide : 2*u≤h
  metadata : ((c).bits*(c).nodes+(c).bits)*(c).lanes≤h/2
  counts : max v.metadata.paidBits ((r).size+2+(c).bits)*(c).lanes≤h/2
  operands : (((r).size+2)*(c).nodes)*(c).lanes≤h/2
  joined : ((f).scalarWidth*(f).inputs+(f).scalarWidth)*(r).lanes≤h/2
  rows : (r).rows≤R*words (r).hosts (r).groups h u

/-- Separate instruction counts for the actual successor and for the later counter. -/
def tailAmount (floor w : ℕ) (B : StageVenueTail.Sources) (room : v.ResultRoom floor B w) :=
  let first:=v.returnPhase floor B w room
  let last:=v.counter floor w
  bitTariff first.program first.ticks+bitTariff last.program last.ticks

theorem return_words (floor w ratio u R : ℕ) (B : StageVenueTail.Sources) (room : v.ResultRoom floor B w)
    (bus : w≤ratio*h) (venue : (d).SourceRows h u) (shelves : v.ShelfRows u R)
    (unit : 0<v.unit) (wide : 2*v.unit≤h) (count : v.countBits≤h/2) :
    v.tailAmount floor w B room≤
      (((d).wordCoefficients ratio).1*(h+2*(d).hosts*h+2*(d).hosts*(d).groups*u)+
        ((d).wordCoefficients ratio).2*(2*(h+1)^2*2^(h/2))*h)+
      2*ratio*((c).ordinaryFactor R (r).operands 7+((f).tickUnits R+7*(f).textUnits))*volumeBits (r).hosts (r).groups h u+
      2*ratio*(2000*(1+2^((a).k+1)))*volumeBits (a).H (a).G h (a).unit :=by
  let p:=(fun x:Fin (c).blocks=>(d).metadataPaid B x.val)
  let span:=v.spanVectors floor
  have vb:=venue.bill B (v.rasterEnd floor) w ratio bus
  have mb:=(c).ordinaryWordVolume (v.metaStart floor) v.metadata.paidBits ((r).size+2) w h u 7 ratio R p span
    shelves.positive shelves.wide bus shelves.metadata shelves.counts shelves.operands shelves.rows (fun _=>le_rfl)
  have fb:=(f).word_volume (v.finalSources floor) (v.metaEnd floor) w h u ratio R
    shelves.positive shelves.wide bus shelves.joined shelves.rows
  have cb:=v.count_word_bill floor w ratio unit wide bus count
  let venue₀:=(d).phase B (v.rasterEnd floor) w
  let args₀:=(f).program (v.finalSources floor) (v.metaEnd floor) w
  let mid:=(c).ordinaryProgram (v.metaStart floor) v.metadata.paidBits ((r).size+2) w p span
  change bitTariff ((venue₀.program.seq mid).seq args₀) ((venue₀.ticks+_)+_)+_≤_
  rw [bitTariff_seq,bitTariff_seq]
  apply (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add vb mb) fb) cb).trans
  change (_+2*ratio*(c).ordinaryFactor R (r).operands 7*volumeBits (r).hosts (r).groups h u+
    2*ratio*((f).tickUnits R+7*(f).textUnits)*volumeBits (r).hosts (r).groups h u)+_≤_
  have payload_eq : v.area.payload = v.payload := rfl
  exact le_of_eq (by rw [payload_eq]; ring)
end Chronology.PhysicalOrdinary
end
end Hierarchy.DescentSixParty

end OAI
