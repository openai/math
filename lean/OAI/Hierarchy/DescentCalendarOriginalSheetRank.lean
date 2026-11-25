import OAI.Hierarchy.DescentCalendarOriginalMetaRead
import OAI.Hierarchy.DescentNamedWordReturn
import OAI.Hierarchy.DescentPhysicalRankSheetIntake

namespace OAI
/-! # The signed rank sheet after the concrete reset candidate writers -/
namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentResetNewActorDirectory DescentDatedAddressBook DescentCompiler DescentColonies DescentDenseHostOrder DescentResetLocalRoster
open DescentPackedPrivateMenu DescentResetPeerUnionRAM DescentPackedColony DescentSIMDLookup
open DescentGroupPeerOrder DescentSortedRoster DescentContactOutputShape DescentPacking.PackedMatch.Local.Stage
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
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



local notation "oldScene" => (v₀).issuedScene base₀ I.earlier
local notation "start₀" => (v₀).actorEnd base₀
local notation "pre₀" m:arg => (phys₀).preScalar start₀ oldScene I.sceneFits m
local notation "look₀" => (v₀).jointRegisters base₀ I.earlier
local notation "trunk₀" m:arg => ((phys₀).trunkScene start₀ oldScene I.sceneFits).image m


variable (floor₀ : ℕ) (src : Bank) (before : Memory bw)
local notation "dir₀" => (⟨floor₀,H,shelf,chunks J oldBatch⟩ : DescentResetNewActorDirectory.Layout)
local notation "entered" => (dir₀).result src before
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
local notation "priorMeta" x:arg j:arg => (fun v g=>DescentResetFieldAssembler.raw (sx).metaBits (actualMeta B rack₀ x (pos j) v g))
local notation "privateIdx" j:arg => pos (.inr (.inr (.inr j)))
local notation "privateReg" x:arg q:arg => I.numbered.privateMeta (xAt x) ((q).cast hp.symm)


local notation "trueMenu" near:arg => measured_menu B oldBatch batch calendar I cal pad prior xs raw near
local notation "named₀" => (Z).rawHostRank T ((B.frame.host.symm.toEmbedding.trans input.vertex).trans (Fin.castLEEmb pad))
local notation "ports₀" => (v₀).rankPorts base₀
local notation "ST" => (v₀).sheetsStart base₀
local notation "meter₀" => DescentResetFieldAssembler.raw (s₀).metaBits
local notation "heads" => shaped hx hs hc hp I.sectors.header
local notation "t₀" => I.sectors.pageBits

/-- The forward rank read is the one produced by the actual prefix pass on these occupied actor pages. -/
theorem original_rank_forward (grid : (v₀).actor.directory ((v₀).middle.stop base₀)=dir₀)
    (oldPos : 0<oldBatch) (oldBits : oldBatch≤bw)
    (actor : ∀l (p : Row H J oldBatch),before (src.base+l.val*(H*chunks J oldBatch)+(row H J oldBatch p).val)=
      ((data (Recorded.realActor (reset:=B) (shapes B) (rack B pad) l) p).val:Word bw))
    (srcFits : src.Fits bw floor₀) (srcSize : rawSize*chunks J oldBatch≤ src.size)
    (chunksWide : chunks J oldBatch≤2^bw) (space : (dir₀).endAddress<2^bw) :
    ∀v:B.next.V,entered (((v₀).rankPortRegs base₀).forward.base+(named₀ v).val)=
      (((compactActorOrder B pad v).val):Word bw):=by
  have posted:=paid_actor_result B pad floor₀ src before oldPos oldBits actor srcFits srcSize chunksWide space
  intro v
  change entered (((v₀).actor.directory ((v₀).middle.stop base₀)).ranks.base+(named₀ v).val)=_
  rw [grid]
  exact posted.2.2.2.1 v

/-- Join the observed original metadata with the four native original-number publications.
The actor census determines the forward chart. The measured raw ports determine the peer roster. -/
noncomputable def original_sheet_rank (ok : I.Ready) (oldSort : SourceSorted W input.order) (elapsed : 0< i)
    {cost : ℕ} (record : B.Recorded cost)
    (hosts : (v₀).receiver.hosts=(s₀).hosts) (groups : (v₀).receiver.groups=gs)
    (sameGroups : (s₀).groups=gs) (lanes : (v₀).receiver.lanes=(s₀).lanes)
    (grid : (v₀).actor.directory ((v₀).middle.stop base₀)=dir₀)
    (oldPos : 0<oldBatch) (oldBits : oldBatch≤bw)
    (actor : ∀l (p : Row H J oldBatch),before (src.base+l.val*(H*chunks J oldBatch)+(row H J oldBatch p).val)=
      ((data (Recorded.realActor (reset:=B) (shapes B) (rack B pad) l) p).val:Word bw))
    (srcFits : src.Fits bw floor₀) (srcSize : rawSize*chunks J oldBatch≤ src.size)
    (chunksWide : chunks J oldBatch≤2^bw) (space : (dir₀).endAddress<2^bw)
    (observed : (∃found : Fin rawSize→Fin 3→Option (Fin rawSize),PhysicalReset.DateInputs.CaptureRoom (trueMenu found) entered ∧
      (∀v : B.next.V,present (selfPeers found) (named₀ v)=(insert v ((Z).emittedNear T v)).map named₀) ∧
      ∀v : B.next.V,present found (named₀ v)=((Z).emittedNear T v).map named₀) ∧
      ∀x j,Source (heads x j) (fun h g=>meter₀ (actualMeta B rack₀ x (pos j) h g)) (s₀).lanes (I.sheetsEntry ok entered))
    (shape : NumberGeometry B I) (scalar : I.OriginalScalarLayout)
    (stemFields : ∃vals : Block k→Fin (stemsCount B)→Fin (sx).hosts→Fin gt→Fin 6→Cell (sx).stemBits,
      (∀x j t,Source (I.stemRegisters x.val j.val t) (fun h g=>vals x j h g t) (sx).lanes (Pout entered)) ∧
      ∀x j,StemInputs B (originalTrunkRack B) x (stemTag B j).1 (stemTag B j).2 (vals x j))
    (donors : WordDonors B oldBatch batch calendar I cal pad bound shape entered) :
    RankSources B (b:=(s₀).metaBits) (t:=units) (M:=(s₀).lanes) rack₀ ports₀
      (sheetHeader B ST t₀) (sheetOriginal B ST t₀) (((v₀).rankPortPhase base₀ bw).image (I.before_ports ok entered)):=by
  let near:=Classical.choose observed.1
  have found:=Classical.choose_spec observed.1
  have forward:=original_rank_forward B oldBatch pad floor₀ src before grid oldPos oldBits actor srcFits srcSize chunksWide space
  have wordRead:=numbered_word_read B oldBatch batch calendar I cal pad prior xs raw near bound hx hs hc hp
    ok entered shape scalar found.1 observed.2 stemFields donors
  exact reached_sheet_rank B oldBatch batch calendar paid I cal pad prior xs raw near entered found.1 bound
    oldSort elapsed record hx hs hc hp hosts groups sameGroups lanes ok found.2.1 forward observed.2 wordRead

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
