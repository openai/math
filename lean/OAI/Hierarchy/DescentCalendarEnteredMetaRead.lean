import OAI.Hierarchy.DescentNamedTrunkSector
import OAI.Hierarchy.DescentReachedMixedHeaders
import OAI.Hierarchy.DescentPhysicalSheetEntryFrame

namespace OAI
/-! # Stem, trunk, contact and private rows at the entered rank sheet -/
namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentPackedColony Computability.VPVNP.BurstRAM PrivateRAM DescentDatedAddressBook DescentCompiler DescentColonies DescentDenseHostOrder DescentResetLocalRoster
open DescentPackedPrivateMenu DescentResetPeerUnionRAM DescentPackedColony DescentSIMDLookup
open DescentGroupPeerOrder DescentSortedRoster DescentContactOutputShape DescentPacking.PackedMatch.Local.Stage
open ProtocolRAM
open scoped Classical Fin.CommRing
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
open DescentResetRankedWindows DescentResetCandidatePair DescentPackedZip DescentResetFieldAssembler
local notation "s₀" => (v₀).sheets
variable (bound : used≤(s₀).hosts) (geo : PhysicalReset.DateInputs.SheetGeometry I)
local notation "dense₀" => ((Z).denseHostRank T ((B.frame.host.symm.toEmbedding.trans input.vertex).trans
    (Fin.castLEEmb pad))).trans (Fin.castLEEmb bound)
local notation "rack₀" => rackOf B dense₀
local notation "gx" => congrArg DescentPrivateMaskDeck.Shape.groups cal.privateDeck
local notation "bx" => congrArg DescentPrivateMaskDeck.Shape.blocks cal.privateDeck
local notation "cx" => geo.contacts.trans (congrArg DescentContactOutputShape.Shape.sockets cal.contactDeck)
local notation "px" => geo.privates.trans (congrArg DescentPrivateMaskDeck.Shape.keys cal.privateDeck)
local notation "pos" => CandidateSheet.index (stemsCount B) (contactCount B) (privateCount B)
local notation "meter" => DescentResetFieldAssembler.raw (s₀).metaBits

variable (m : Memory bw)
variable {p zsize : ℕ} (record : B.Recorded p) (pay : 0<(Z).unit)
    (trees : Bool→(Z).Fallback→DescentPackedFallbackTree.Panel ht zsize) (origins : PeerOrigins B pad prior pay trees)

local notation:max "menu_" n:arg => measured_menu B oldBatch batch calendar I cal pad prior xs raw n
local notation "named₀" => (Z).rawHostRank T ((B.frame.host.symm.toEmbedding.trans input.vertex).trans (Fin.castLEEmb pad))
local notation "atTrunk" => ((v₀).front.trunkScene ((v₀).actorEnd base₀) ((v₀).issuedScene base₀ I.earlier) I.sceneFits).image m
variable (hx : (v₀).receiver.blocks=2^k) (hs : I.sectors.stems=stemsCount B)
    (hc : (s₀).contacts=contactCount B) (hp : (s₀).privates=privateCount B)
local notation "heads" => shaped hx hs hc hp I.sectors.header
local notation:max "physical" x:arg j:arg => (fun h g=>meter (actualMeta B rack₀ x (pos j) h g))
include paid geo origins record in
/-- All four physical header families at the same state used by the rank reader. -/
theorem entered_meta_read
    (attained : ∃found : Fin rawSize→Fin 3→Option (Fin rawSize),
      PhysicalReset.DateInputs.CaptureRoom (menu_ found) m ∧
      (∀v : B.next.V,present (selfPeers found) (named₀ v)=(insert v ((Z).emittedNear T v)).map named₀) ∧
      ∀v : B.next.V,(∀j,found (named₀ v) j≠some (named₀ v)) ↔ v∉(Z).emittedNear T v)
    (sender : ContactSenderRead B calendar pad xs raw) (room : ContactFieldRoom B oldBatch batch calendar)
    (ok : I.Ready) (lanes : 0<I.masked.lanes)
    (rankFit : I.masked.lanes*max (I.masked.field*5) I.masked.field≤bw/2)
    (maskFit : I.masked.lanes*max (I.masked.field*9) (I.masked.field*7)≤bw/2)
    (stem : ∀(x : Fin (2^k)) (j : Fin (stemsCount B)),
      ((phys₀).stemOperand ((v₀).actorEnd base₀) x.val j.val).Fits bw ((v₀).trunkEnd base₀) ∧
      Source ((phys₀).stemOperand ((v₀).actorEnd base₀) x.val j.val)
        (fun (h : Fin (s₀).hosts) g=>meter (actualMeta B (originalTrunkRack B) x (stemShelf B j) h g)) (s₀).lanes atTrunk)
    (trunk : ∀(x : Fin (2^k)),((phys₀).trunkOperand ((v₀).actorEnd base₀) x.val).Fits bw ((v₀).trunkEnd base₀) ∧
      Source ((phys₀).trunkOperand ((v₀).actorEnd base₀) x.val)
        (fun (h : Fin (s₀).hosts) g=>meter (actualMeta B (originalTrunkRack B) x (trunkCandidate B) h g)) (s₀).lanes atTrunk) :
    ∀x j,Source (heads x j) (physical x j) (s₀).lanes (I.sheetsEntry ok m):=by
  have mixed:=fun x=>entered_candidate_headers B oldBatch batch calendar paid I cal pad prior xs raw m record pay
    trees origins attained sender room geo ok x lanes rankFit maskFit
  obtain ⟨contacts,privateRows⟩:=rank_private_contact_sources B oldBatch batch calendar I cal pad bound geo hx hs hc hp
    (I.sheetsEntry ok m) (fun x=>(mixed x).1) (fun x=>(mixed x).2)
  have fromStem:=named_stem_sector B I pad bound hx hs hc hp atTrunk stem
  have fromTrunk:=named_trunk_sector B I pad bound hx hs hc hp atTrunk trunk
  intro x j
  rcases j with j|j|j|j
  · exact I.from_trunk_source ok m _ _ (fromStem x j).1 (fromStem x j).2
  · obtain rfl := Subsingleton.elim j 0
    exact I.from_trunk_source ok m _ _ (fromTrunk x).1 (fromTrunk x).2
  · exact contacts x j
  · exact privateRows x j

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
