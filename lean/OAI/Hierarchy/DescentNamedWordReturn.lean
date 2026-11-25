import OAI.Hierarchy.DescentNamedWordGeometry

namespace OAI
/-! # Final rank inputs from the actual named geometry and physical donor columns -/
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
    (near : Fin rawSize→Fin 3→Option (Fin rawSize))

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


open DescentResetOriginalSlots
local notation "sx" => (v₀).sheets
local notation "area" => ((v₀).remap base₀).endAddress
local notation "o" => (sx).original area
local notation "blk" => 2^k
local notation "gt" => S.groupCount (i+1)
local notation "units" => originalBits D k n ht (A).cap (programCount ctl.board ht) g
local notation "T₀" => I.numbered.stemSide area
local notation "P₀" => I.numbered.publicSide area
local notation "D₀" => I.numbered.privateSide area
local notation "packed" x:arg j:arg => (.lookup (bank o (sx).rows (sx).candidates x j) .row:Expr)
local notation "start" m:arg => I.masked.image (I.privateResult m)
local notation "Pout" m:arg => (P₀).dst (I.numbered.prefixOutput area (start m))
local notation "Tout" m:arg => (T₀).image (Pout m)

variable (hx : (v₀).receiver.blocks=blk) (hs : I.sectors.stems=stemsCount B)
    (hc : I.sectors.contacts=contactCount B) (hp : I.sectors.privates=privateCount B)
local notation "groupAt" => congrArg DescentPrivateMaskDeck.Shape.groups cal.privateDeck
local notation "blockAt" => congrArg DescentPrivateMaskDeck.Shape.blocks cal.privateDeck
local notation "values" x:arg j:arg => (fun v g₀=>(actualParentNumber B rack₀ x j v g₀:Cell units))
local notation "word" x:arg j:arg => (fun v (gr:Fin (sx).groups)=>(actualParentNumber B rack₀ x j v (gr.cast groupAt):Cell units))
local notation "reg" x:arg j:arg => shaped hx hs hc hp I.sectors.original x j

open DescentResetPublicParentWord
local notation "pre" m:arg => I.numbered.prefixOutput area (start m)
local notation "orig₀" => I.numbered
local notation "xAt" x:arg => Fin.cast (blockAt).symm x
local notation "jAt" j:arg => Fin.cast hc.symm j
local notation "trunkIdx" => pos (.inr (.inl 0))
local notation "contactIdx" j:arg => pos (.inr (.inr (.inl j)))
local notation "trueZero" x:arg => (fun (_:Fin (sx).hosts) (gr:Fin (sx).groups)=>decide (gr.val=0 ∧ (x).val=0))
local notation "metaIn" x:arg j:arg => (fun (h:Fin (sx).hosts) (gr:Fin (sx).groups)=>actualMeta B rack₀ x j h (gr.cast groupAt))
local notation "vertex" => B.frame.host.symm.toEmbedding.trans input.vertex
open DescentContactDonorSelection DescentParallelBase


local notation "hdr" x:arg j:arg => shaped hx hs hc hp I.sectors.header x j
local notation "priorMeta" x:arg j:arg => (fun v grp=>DescentResetFieldAssembler.raw (sx).metaBits (actualMeta B rack₀ x (pos j) v grp))
local notation "privateIdx" j:arg => pos (.inr (.inr (.inr j)))
local notation "privateReg" x:arg q:arg => I.numbered.privateMeta (xAt x) ((q).cast hp.symm)

local notation "menu" => measured_menu B oldBatch batch calendar I cal pad prior xs raw near

/-- The three physical fields which were printed at the old sender and retained
through the native coordinate, donor, and compaction phases. -/
structure WordDonors (shape : NumberGeometry B I) (m : Computability.VPVNP.BurstRAM.Memory bw) where
  own : Fin blk→Bool→Fin I.numbered.signedSlots→Fin (sx).hosts→Fin (sx).groups→Cell (sx).selectorBits

  cargo : Fin blk→Bool→Fin 2→Fin I.numbered.signedSlots→Fin (sx).hosts→Fin (sx).groups→Cell (sx).shortBits

  labels : ∀x side i,Source ((P₀).old.label (xAt x) side i) (own x side i) (sx).lanes (pre m)

  cargos : ∀x side flag i,Source ((P₀).old.cargo (xAt x) side flag i) (cargo x side flag i) (sx).lanes (pre m)

  origin : ∀x v t,rack₀ v=some t→∀(gr:Fin (sx).groups),
      let u:=((gr.cast groupAt,t),x)
      (∀side (i:Fin (L*(2*(A).cap))),(own x side (i.cast shape.donors.symm) v gr).val=(originalDonor B u side i).elim 0
        (fun e=>(Z).senderJoint T side ((Z).placement.contact e))) ∧
      (∀side (i:Fin (L*(2*(A).cap))) e,originalDonor B u side i=some e→(cargo x side 0 (i.cast shape.donors.symm) v gr).val=
        (Z).senderJoint T false ((Z).placement.contact e)) ∧
      ∀side (i:Fin (L*(2*(A).cap))) e,originalDonor B u side i=some e→(cargo x side 1 (i.cast shape.donors.symm) v gr).val=
        haloNumber B u ((Z).rootVertex T ((Z).placement.owner false ((Z).placement.contact e)))+1

theorem numbered_word_read (ok : I.Ready) (m : Computability.VPVNP.BurstRAM.Memory bw)
    (shape : NumberGeometry B I) (scalar : I.OriginalScalarLayout)
    (captured : PhysicalReset.DateInputs.CaptureRoom (menu) m)
    («meta» : ∀x j,Source (hdr x j) (priorMeta x j) (sx).lanes (I.sheetsEntry ok m))
    (stemFields : ∃vals : Block k→Fin (stemsCount B)→Fin (sx).hosts→Fin gt→Fin 6→Cell (sx).stemBits,
      (∀x j t,Source (I.stemRegisters x.val j.val t) (fun h g=>vals x j h g t) (sx).lanes (Pout m)) ∧
      ∀x j,StemInputs B (originalTrunkRack B) x (stemTag B j).1 (stemTag B j).2 (vals x j))
    (donors : WordDonors B oldBatch batch calendar I cal pad bound shape m) :
    ∀x j,Source (shaped hx hs hc hp I.sectors.original x j) (values x (pos j)) (sx).lanes (I.sheetsEntry ok m):=
  original_word_read B oldBatch batch calendar I cal pad prior xs raw near bound hx hs hc hp ok m scalar captured
    shape.geometry shape.height shape.nodes shape.ports shape.board shape.precision shape.funded shape.zero
    (fun x=>shape.zeroReg (xAt x)) (fun x=>shape.haloReg (xAt x)) «meta» shape.stems shape.stemSlot shape.publicSlot shape.privateSlot
    shape.degree shape.bits shape.side shape.room stemFields shape.donors shape.request
    donors.own donors.cargo donors.labels donors.cargos donors.origin shape.ticket shape.halo shape.jobs

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
