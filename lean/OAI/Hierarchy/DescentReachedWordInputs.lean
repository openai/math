import OAI.Hierarchy.DescentReachedPublicNumbers
import OAI.Hierarchy.DescentReachedPrivateNumbers
import OAI.Hierarchy.DescentReachedOriginalScalarSources
import OAI.Hierarchy.DescentNamedTrunkSector
import OAI.Hierarchy.DescentReachedMixedHeaders
import OAI.Hierarchy.DescentOriginalBoardGeometry
import OAI.Hierarchy.DescentReachedMixedHeaders
import OAI.Hierarchy.DescentOriginalSectorRetention
import OAI.Hierarchy.DescentResetStemOriginalSlots
import OAI.Hierarchy.DescentResetPublicParentPosted
import OAI.Hierarchy.DescentPhysicalRankSheetIntake

namespace OAI
/-! # Original table inputs from the same reached metadata and retained donor prefix -/
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

private theorem pull_groups {w hostCount a G G' M : ℕ} (axis:G=G') {m : Computability.VPVNP.BurstRAM.Memory w} {e : Expr}
    (v : Fin hostCount→Fin G'→Cell a) (s : Source e v M m) : Source e (fun h (g:Fin G)=>v h (g.cast axis)) M m:=by
  subst G';exact s

/-- The source of all positive bits for the chronological number tables is
the very same masked register that is subsequently read by ranking. -/
theorem original_meta_prefix (ok : I.Ready) (m : Computability.VPVNP.BurstRAM.Memory bw)
    («meta» : ∀x j,Source (hdr x j) (priorMeta x j) (sx).lanes (I.sheetsEntry ok m))
    (jobCount : (sx).jobs=(sx).blocks*((sx).contacts+(sx).privates)) :
    (∀x : Fin blk,Source ((P₀).old.meta (xAt x) 0)
      (fun v gr=>meter ((metaIn x trunkIdx) v gr)) (sx).lanes (pre m)) ∧
    (∀(x:Fin blk)(j:Fin (contactCount B)),Source ((P₀).old.meta (xAt x) (jAt j).succ)
      (fun v gr=>meter ((metaIn x (contactIdx j)) v gr)) (sx).lanes (pre m)) ∧
    ∀(x:Fin blk)(j:Fin (privateCount B)),(privateReg x j).Fits bw ((sx).inputDonorsEnd area) ∧
      Source (privateReg x j) (fun v gr=>meter ((metaIn x (privateIdx j)) v gr)) (sx).lanes (pre m):=by
  have entryMem : I.sheetsEntry ok m = I.numbered.output area (start m) := rfl
  have fromEntry (x : Fin blk) (j : CandidateSheet.Sector (stemsCount B) (contactCount B) (privateCount B))
      (op : Expr) (same : hdr x j = op) (fit : op.Fits bw ((sx).inputDonorsEnd area)) :
      Source op (fun v (gr : Fin (sx).groups) => (priorMeta x j) v (gr.cast groupAt)) (sx).lanes (pre m) := by
    have seen := «meta» x j
    rw [same, entryMem] at seen
    have scaled := @pull_groups bw (sx).hosts ((sx).metaBits * 7) (sx).groups gt (sx).lanes groupAt
      (I.numbered.output area (start m)) op (priorMeta x j) seen
    exact I.numbered.prefix_from_return area (start m) ok.numbers op
      (fun v (gr : Fin (sx).groups) => (priorMeta x j) v (gr.cast groupAt)) fit scaled
  refine ⟨?_,?_,?_⟩
  · intro x
    have expr := shaped_trunk hx hs hc hp I.sectors.header x
    exact fromEntry x (.inr (.inl 0)) _ expr (ok.numbers.public_.meta (xAt x) 0)
  · intro x j
    have expr := shaped_contact hx hs hc hp I.sectors.header x j
    exact fromEntry x (.inr (.inr (.inl j))) _ expr (ok.numbers.public_.meta (xAt x) (jAt j).succ)
  · intro x j
    have slotLt:((sx).contacts+(j.cast hp.symm).val)<(sx).contacts+(sx).privates:=
      Nat.add_lt_add_left (j.cast hp.symm).isLt _
    have cut:I.masked.endAddress≤(sx).inputDonorsEnd area:=by
      rw [I.masks_end, CandidateSheets.donors_shift,CandidateSheets.coordinateEnd,(sx).stemSources.extent]
      omega
    have fit:(privateReg x j).Fits bw ((sx).inputDonorsEnd area):=by
      apply ProtocolRAMGeneratedWrite.fits_mono _ cut
      apply I.measured_mark_fits _ _ _ ok.masked
      rw [jobCount]
      change x.val*((sx).contacts+(sx).privates)+_<(sx).blocks*((sx).contacts+(sx).privates)
      exact (Nat.add_lt_add_left slotLt _).trans_le (by rw [←Nat.succ_mul];exact Nat.mul_le_mul_right _ (xAt x).isLt)
    have expr := shaped_private hx hs hc hp I.sectors.header x j
    exact ⟨fit, fromEntry x (.inr (.inr (.inr j))) _ expr fit⟩

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
