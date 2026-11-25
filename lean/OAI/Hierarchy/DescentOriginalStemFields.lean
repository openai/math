import OAI.Hierarchy.DescentStemPublishedCoordinates
import OAI.Hierarchy.DescentPostedStemInputs
import OAI.Hierarchy.DescentCalendarRealStemAux
import OAI.Hierarchy.DescentStemPostedBasis
import OAI.Hierarchy.DescentNamedPostedStemGeometry

namespace OAI
/-! # Six original stem inputs at the numbered public snapshot -/
namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentDatedAddressBook DescentCompiler DescentColonies DescentDenseHostOrder DescentResetLocalRoster
open DescentPackedPrivateMenu DescentResetPeerUnionRAM DescentPackedColony DescentSIMDLookup
open DescentGroupPeerOrder DescentSortedRoster DescentContactOutputShape DescentPacking.PackedMatch.Local.Stage
open ProtocolRAM
open DescentResetFieldAssembler DescentStemNumberOperands DescentResetStemFlagInputs DescentPackedZip
open scoped Classical Fin.CommRing
noncomputable section
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
  {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k i z D n h C f g cut tail wire hist : ℕ}
  {input : Reached W G q ε S k i z D wire hist} {ctl : ResetRates G S k D n h C f g cut tail}
  (B : ClosedReset input ctl)
set_option hygiene false
set_option quotPrecheck false
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

local notation "R₀" => measured_menu B oldBatch batch calendar I cal pad prior xs raw near
local notation "host₁" => Stage.Host (Fin gs) B.next.V k
local notation "named₀" => (Z).rawHostRank T ((B.frame.host.symm.toEmbedding.trans input.vertex).trans (Fin.castLEEmb pad))
local notation "s₀" => (v₀).sheets


local notation "regs₀" => (v₀).jointRegisters base₀ I.earlier
local notation "real₀" => compactActorName B pad
local notation "rows₀" => DescentResetPeerUnionRAM.selfPeers near
variable (m : Computability.VPVNP.BurstRAM.Memory bw) (seen : PhysicalReset.DateInputs.CaptureRoom (R₀) m)



local notation "fr" => (v₀).front
local notation "cut₀" => (v₀).actorEnd base₀
local notation "trunk" => ((fr).trunkScene cut₀ ((v₀).issuedScene base₀ I.earlier) I.sceneFits).image m
local notation "area" => ((v₀).remap base₀).endAddress
local notation "mid" => I.masked.image (I.privateResult m)
local notation "Pout" => (I.numbered.publicSide area).dst (I.numbered.prefixOutput area mid)

private theorem const_group {N G₁ G₂ b M w : ℕ} (eqn : G₁=G₂) (term : Expr)
    (value : Fin N→Cell b) (m : Computability.VPVNP.BurstRAM.Memory w)
    (read : Source term (fun rowId (_:Fin G₁)=>value rowId) M m) :
    Source term (fun rowId (_:Fin G₂)=>value rowId) M m:=by
  subst G₂
  exact read

include seen in
theorem original_stem_fields (ok : I.Ready) (occupied : used≤I.masked.hosts)
    (sh : PostedStemGeometry B date) (basis : PostedStemBasis B I m)
    (pub : StemPublished B (s₀).hosts (s₀).lanes (s₀).stemSignedBits (s₀).metaBits
      ((fr).mixed cut₀) ((v₀).trunkEnd base₀) I.previousSigned ((fr).stemOperand cut₀) trunk) :
    ∃values : Block k→Fin (stemsCount B)→Fin (s₀).hosts→Fin gs→Fin 6→Cell (s₀).stemBits,
      (∀x j t,Source (I.stemRegisters x.val j.val t) (fun h g=>values x j h g t) (s₀).lanes Pout) ∧
      ∀x j,StemInputs B (originalTrunkRack B) x (stemTag B j).1 (stemTag B j).2 (values x j) :=by
  have nextGroup : I.masked.groups=gs:=congrArg DescentPrivateMaskDeck.Shape.groups cal.privateDeck
  obtain ⟨self,readSelf,realSelf⟩:=real_stem_aux B oldBatch batch calendar I cal pad prior xs raw near m seen ok occupied
  obtain ⟨chip,readChip,realChip⟩:=pub.signed
  have early : (fr).mixed cut₀≤(v₀).trunkEnd base₀:=
    (DescentResetTrunkCompactProgram.grow ..).trans (Nat.le_add_right ..)
  exact posted_stem_inputs B I ok m sh.schedule sh.xRoom sh.jRoom sh.cap basis.chosen basis.saved basis.space
    sh.signedWidth ⟨chip,fun x j=>⟨ProtocolRAMGeneratedWrite.fits_mono _ early (readChip x j).1,(readChip x j).2⟩,realChip⟩
    ⟨self,const_group nextGroup _ self _ readSelf,realSelf⟩ basis.bf pub.head sh.metaPos
    sh.signedFits sh.groupsFit sh.hostsFit sh.fineFit

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
