import OAI.Hierarchy.DescentOriginalPrivateEmitter
import OAI.Hierarchy.DescentOriginalBoardGeometry
import OAI.Hierarchy.DescentReachedMixedHeaders
import OAI.Hierarchy.DescentOriginalSectorRetention
import OAI.Hierarchy.DescentResetStemOriginalSlots
import OAI.Hierarchy.DescentResetPublicParentPosted
import OAI.Hierarchy.DescentPhysicalRankSheetIntake

namespace OAI
/-! # The true private chronology words on the named original-number table -/
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
local notation:max "packed" x:arg j:arg => (.lookup (bank o (sx).rows (sx).candidates x j) .row:Expr)
local notation:max "start" m:arg => I.masked.image (I.privateResult m)
local notation:max "Pout" m:arg => (P₀).dst (I.numbered.prefixOutput area (start m))
local notation:max "Tout" m:arg => (T₀).image (Pout m)

variable (hx : (v₀).receiver.blocks=blk) (hs : I.sectors.stems=stemsCount B)
    (hc : I.sectors.contacts=contactCount B) (hp : I.sectors.privates=privateCount B)
local notation "groupAt" => congrArg DescentPrivateMaskDeck.Shape.groups cal.privateDeck
local notation "blockAt" => congrArg DescentPrivateMaskDeck.Shape.blocks cal.privateDeck
local notation:max "values" x:arg j:arg => (fun v g₀=>(actualParentNumber B rack₀ x j v g₀:Cell units))
local notation:max "word" x:arg j:arg => (fun v (gr:Fin (sx).groups)=>(actualParentNumber B rack₀ x j v (gr.cast groupAt):Cell units))
local notation:max "reg" x:arg j:arg => shaped hx hs hc hp I.sectors.original x j

open DescentResetPublicParentWord
local notation:max "pre" m:arg => I.numbered.prefixOutput area (start m)
local notation:max "idx_" j:arg => pos (.inr (.inr (.inr j)))
local notation:max "query" x:arg q:arg => I.numbered.privateMeta (Fin.cast (blockAt).symm x) (Fin.cast hp.symm q)
local notation:max "zero_" x:arg => I.numbered.zero (Fin.cast (blockAt).symm x)
local notation:max "halo_" x:arg => I.numbered.halo (Fin.cast (blockAt).symm x)

local notation "host₁" => DescentSharedCableNames.Stage.Host (Fin gs) B.next.V k

private theorem private_meta_live (u : host₁) (j : Fin (privateCount B)) :
    («meta» B u (localOrigin B u (privateShelfIndex B j))).live=(localOrigin B u (privateShelfIndex B j)).isSome:=by
  cases localOrigin B u (privateShelfIndex B j) <;>rfl

set_option maxHeartbeats 1000000 in
/-- The real private table receives the printed private slot address, measured positive
bit and original self halo. Numeric coding of an absent or unoccupied lane is zero. -/
theorem private_original_output (ok : I.Ready) (m : Computability.VPVNP.BurstRAM.Memory bw)
    (geom : I.numbered.geometry=publicShape B) (rb : I.numbered.resultBits=units)
    (field : 0<(sx).metaBits) (zt : 0<(sx).zeroBits)
    (xf : ∀(x:Fin blk) (q:Fin (privateCount B)),(query x q).Fits bw ((sx).inputDonorsEnd area))
    (zf : ∀x:Fin blk,(zero_ x).Fits bw ((sx).inputDonorsEnd area)) (hf : ∀x:Fin blk,(halo_ x).Fits bw ((sx).inputDonorsEnd area))
    (visible : ∀(x:Fin blk)(q:Fin (privateCount B)),Source (query x q)
        (fun h g=>DescentResetFieldAssembler.raw (sx).metaBits (actualMeta B rack₀ x (idx_ q) h (g.cast groupAt))) (sx).lanes (pre m))
    (zero : ∀x:Fin blk,Source (zero_ x) (fun (_:Fin (sx).hosts) (g:Fin (sx).groups)=>
      ((decide (g.val=0 ∧ x.val=0)).toNat:Cell (sx).zeroBits)) (sx).lanes (pre m))
    (rank : Fin blk→Fin (sx).hosts→Fin (sx).groups→Cell (sx).haloBits)
    (halo : ∀x,Source (halo_ x) (rank x) (sx).lanes (pre m))
    (actual : ∀(x:Fin blk) (h:Fin (sx).hosts) (v:B.next.V),rack₀ h=some v→∀g₀:Fin (sx).groups,(rank x h g₀).val=
      haloNumber B ((g₀.cast groupAt,v),x) (receiverRoot B ((g₀.cast groupAt,v),x)).1) :
    ∀(x:Fin blk) (j:Fin (privateCount B)),Source (packed x.val (I.numbered.privateShelf (j.cast hp.symm)).val)
      (word x (idx_ j)) (sx).lanes (I.numbered.output area (start m)):=by
  intro x j
  let cells:=fun (v:Fin (sx).hosts) (g₀:Fin (sx).groups)=>actualMeta B rack₀ x (idx_ j) v (g₀.cast groupAt)
  let zbit:=fun (_:Fin (sx).hosts) (g₀:Fin (sx).groups)=>decide (g₀.val=0 ∧ x.val=0)
  have row:=I.numbered.private_number_at area ok.numbers (start m) (x.cast (blockAt).symm) (j.cast hp.symm)
    cells zbit (rank x) field zt (xf x j) (zf x) (hf x) (visible x j) (zero x) (halo x)
  have physical : idx_ j=privateShelfIndex B j:=Fin.ext (CandidateSheet.private_val j)
  have numeric (h : Fin (sx).hosts) (g₀ : Fin (sx).groups) :
      privateWord I.numbered.geometry (cells h g₀).live.toNat (zbit h g₀).toNat (rank x h g₀).val j.val=
      actualParentNumber B rack₀ x (idx_ j) h (g₀.cast groupAt):=by
    rw [geom]
    cases present : rack₀ h with
    | none=>simp [cells,actualMeta,actualParentNumber,present,Meta.blank,private_dead]
    | some v=>
      let u:host₁:=((g₀.cast groupAt,v),x)
      have z : zbit h g₀=zeroCoarse B u:=(public_zero B u).symm
      simpa only [cells,actualMeta,actualParentNumber,physical,present,Option.elim_some,z,actual x h v present g₀,
        private_meta_live] using (private_slot_word B u j)
  change Source (packed x.val (I.numbered.privateShelf (j.cast hp.symm)).val)
    (fun h gr => (privateWord I.numbered.geometry (cells h gr).live.toNat (zbit h gr).toNat
      (rank x h gr).val j.val : Cell I.numbered.resultBits)) (sx).lanes (I.numbered.output area (start m)) at row
  simp_rw [numeric] at row
  let readWidth (width : ℕ) : Prop :=
    Source (packed x.val (I.numbered.privateShelf (j.cast hp.symm)).val)
      (fun h (gr : Fin (sx).groups) => (actualParentNumber B rack₀ x (idx_ j) h (gr.cast groupAt) : Cell width))
      (sx).lanes (I.numbered.output area (start m))
  exact (congrArg readWidth rb).mp row

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
