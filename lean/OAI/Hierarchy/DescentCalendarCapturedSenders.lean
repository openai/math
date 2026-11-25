import OAI.Hierarchy.DescentCalendarCandidateCapture
import OAI.Hierarchy.DescentPhysicalContactInputs
import OAI.Hierarchy.DescentCalendarOriginalContact
import OAI.Hierarchy.DescentReachedContactFrame

namespace OAI
/-! # The original contact emitter on the actual calendar's donor and trunk state -/
namespace Hierarchy.DescentContactOutputShape.Shape
open DescentSIMDLookup DescentPackedZip ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
noncomputable section

def donorPrior (A : Shape) : Type := DescentContactSenderDate.Prior
  A.donor.degree A.donor.lows A.donor.cap A.donor.n A.donor.residual

def senderRegisters (A : Shape) : Type :=
  Fin A.sockets→Fin 4→Fin A.sparseHosts→Fin A.donor.groups→Cell A.metaBits

theorem reads_cast {A B : Shape} (eqn : A=B) {w : ℕ} (base first : ℕ) (u : A.donorPrior)
    (values : B.senderRegisters) (trunk : Memory w)
    (received : ∀q j,Source (B.fieldsAt base first (cast (congrArg donorPrior eqn) u) q j)
      (values q j) B.donor.batch (B.held base first (cast (congrArg donorPrior eqn) u) trunk)) :
    ∀q j,Source (A.fieldsAt base first u q j) (cast (congrArg senderRegisters eqn.symm) values q j)
      A.donor.batch (A.held base first u trunk) :=by
  subst B
  exact received

end
end Hierarchy.DescentContactOutputShape.Shape

namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentDatedAddressBook DescentCompiler DescentColonies DescentDenseHostOrder DescentResetLocalRoster
open DescentPackedPrivateMenu DescentResetPeerUnionRAM DescentPackedColony DescentSIMDLookup
open DescentGroupPeerOrder DescentSortedRoster DescentContactOutputShape DescentPacking.PackedMatch.Local.Stage
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical
noncomputable section
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
  {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k i z D n h C f g cut tail wire hist : ℕ}
  {input : Reached W G q ε S k i z D wire hist} {ctl : ResetRates G S k D n h C f g cut tail}
  (B : ClosedReset input ctl)
set_option quotPrecheck false
set_option hygiene false
local notation "Z" => B.reset
local notation "T" => B.terminals
local notation "A" => input.placement
local notation "H" => S.hostSize i
local notation "J" => 2^(T).commonDepth
local notation "r" => (Z).k-(T).commonDepth
local notation "ht" => GroupStage.depthBound D n f g
local notation "shelf" => (DescentDenseHostOrder.roster (Z).graph r ht).card
local notation "gs" => S.groupCount (i+1)
local notation "cap₀" => max (Fintype.card (DescentCommonPalette.rotor (Z).graph).Edge) (2^(ht+1))
local notation "oldWidth" => DescentPackedPrivateMenu.fieldBits (Z).graph r ht (2^r*(2*(A).cap))
    (DescentRecordedRotorLayers.width f (A).cap) C (Z).width
variable (oldBatch batch : ℕ) (calendar : List ℕ) (paid : (A).cap=(calendar.take i).prod*256)
local notation "cap" => (calendar.take i).prod*256
local notation "field₀" => ResetMiddle.fieldWidth D cap n k ht
local notation "table₀" => CandidateSheets.fromBoard S ctl.board k tail i D f g cap batch
local notation "meta₀" => (table₀).metaBits
local notation "month" => CandidateFront.menu S ctl.board k tail i D f g oldBatch batch C ctl.bitsR calendar
local notation "good" => contactOutputs B H oldBatch field₀ (Nat.clog 2 (D+2)) (Nat.clog 2 (D+3)) gs (2^k)
    batch (month).contact.outputBits meta₀
local notation "deck" => privateProjection («H»:=H) (field:=oldWidth) B oldBatch batch meta₀
variable {date : PhysicalReset} {floor bw : ℕ} (I : date.DateInputs floor bw)
local notation "v₀" => date.successor
local notation "base₀" => date.rebased floor
local notation "phys₀" => (v₀).front
local notation "peer₀" => (phys₀).peer
local notation "pitch₀" => (phys₀).contactLayout ((v₀).actorEnd base₀)
local notation "Q₀" => (v₀).privateShape
local notation "K₀" => (v₀).contactShape
local notation "don₀" => (phys₀).donorStart ((v₀).actorEnd base₀)
local notation "used" => Fintype.card B.next.V
local notation "rawSize" => H*shelf
local notation "L" => 2^(S.groupWidth k tail i+k-(T).commonDepth)
local notation "K" => 2*(A).cap
local notation "F₀" => DescentOldContactSender.count (A).degree L (A).cap (Z).n r
variable (cal : MixedGeometry B oldBatch batch calendar v₀ base₀) (pad : Fintype.card input.V≤H)
local notation "portChart" => input.vertex.trans (Fin.castLEEmb pad)
local notation "adj_" => hostRotor portChart (hostRoster (A) ((portChart).trans Fin.valEmbedding))
variable {keyBits : ℕ} (prior : PriorPeerWords B H oldWidth keyBits)
    (xs : Fin H→Fin J→Fin F₀→Cell field₀) (raw : Fin L→Fin K→Fin H→Fin J→Cell field₀)
    (near : Fin rawSize→Fin 3→Option (Fin rawSize))

local notation "measured" => measured_menu B oldBatch batch calendar I cal pad prior xs raw near
local notation "oldScene" => (v₀).issuedScene base₀ I.earlier
local notation "start₀" => (v₀).actorEnd base₀
local notation "pre₀" m => (phys₀).preScalar start₀ oldScene I.sceneFits m
local notation "look₀" => (v₀).jointRegisters base₀ I.earlier
local notation "trunk₀" m:arg => ((phys₀).trunkScene start₀ oldScene I.sceneFits).image m

local notation "front₁" => (good).donor
local notation "U₁" => cast (congrArg DescentContactOutputShape.Shape.donorPrior cal.contactDeck) (oldScene).donor
local notation "first₁" => (v₀).trunkEnd base₀
local notation "marks₁" => (front₁).markers don₀ (good).shapes (good).markerBits
local notation "job₁" => (front₁).sender don₀
local notation "count₁" => L*(2*(A).cap)

theorem captured_sender_inputs (ok : I.Ready) (early m : Memory bw)
    (front : (front₁).Space don₀ U₁ bw)
    (post : (marks₁).endAddress≤first₁)
    (area : (good).endAddress first₁<2^bw)
    (pack : oldBatch*max (field₀*8) (good).markerBits≤bw/2)
    (before : (job₁).Before U₁ xs adj_ raw early)
    (stable : ∀a,a<(marks₁).endAddress → (trunk₀ m) a=
      (front₁).result don₀ (good).shapes (good).markerBits U₁ (Z).graph front (post.trans_lt ok.trunk) pack early a)
    (jobs : (job₁).Packed bw) (matrix : oldBatch*max (field₀*(marks₁).oldFields) (marks₁).viewBits≤bw/2)
    (tailRoom : (good).marker first₁+H*chunks J oldBatch<2^bw)
    (counter : oldBatch*max (field₀*(count₁+1)) field₀≤bw/2)
    (earned : ContactFieldRoom B oldBatch batch calendar)
    (joints : (good).shapes*2^Nat.clog 2 ((A).degree+2)≤2^meta₀) :
    ∀q j,DescentPackedZip.Source ((K₀).fieldsAt don₀ first₁ (oldScene).donor q j)
      ((measured).contactValues q j) (K₀).donor.batch
      ((K₀).held don₀ first₁ (oldScene).donor (trunk₀ m)) :=by
  apply DescentContactOutputShape.Shape.reads_cast cal.contactDeck don₀ first₁ (oldScene).donor
    (trueContactRegisters B oldBatch batch calendar I pad xs raw) (trunk₀ m)
  exact (good).attained_inputs don₀ first₁ U₁ (Z).graph front post area pack xs adj_ raw early
    (trunk₀ m) before stable jobs matrix tailRoom earned.keys counter earned.opposite joints


end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
