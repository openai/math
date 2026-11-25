import OAI.Computability.BorderVNP.DiagonalBootLookupInputs
import OAI.Computability.BorderVNP.DiagonalReferenceOwnedSources
import OAI.Computability.BorderVNP.DiagonalSourceOwnedLookup

/-! # The real copied subtotal at the recovered table lookup's own source -/

namespace OAI
namespace Computability
namespace BorderVNP

set_option autoImplicit false

namespace TeamContraction

open PackedHistoryCircuit
open VPVNP BurstRAM Diagonal.Layout Routing RoutingISA RoutingISA.Transmission RoutingISA.Evaluator
open BorderVNP.Cube Physical Scatter Scatter.Assignment SignedPrep TeamRows Tally
open DiagonalTallyPacketEmit CellMacro.Generator JointHeader ProcessorSlots SignedTaskArena FiniteEvaluator
set_option maxHeartbeats 1500000
set_option maxRecDepth 7500

variable {R r t d link inner n w : ℕ} {Edge : Type} {G : Wiring R r t d link inner n Edge}
    {L : WireLayout (R+1) r link} (sa : SignedTaskArena.Layout) {decl : LengthDeclaration sa.cube.n sa.cube.header.d}
    (fixed : Block (R+1)) {header : List Bool} {pin : Fin d → Bool}
    {pub : HeaderExterior L header → Fin (R+1) → Arg → Word w}
    {mac : HeaderExterior L header → Fin (R+1) → TeamOpcode.Macros w 8}
    {reg : HeaderExterior L header → Fin (R+1) → Bank w}
    {mem : HeaderExterior L header → Fin (R+1) → Memory w}
    {owners : (Packet sa.cube.n sa.cube.header.d sa.cube.header.blocks →
      Selector sa.cube.n sa.cube.K sa.cube.h) → Fin sa.cube.header.d → Fin (R+1)}
    (S : SourceReports sa.cube owners) (F : PreparationFrame G L sa.cube decl header pin pub mac reg mem)
    (B : F.Builders fixed sa.id owners) (agree : F.SourceAgreement fixed S B)
    (q : {v : Declared sa.cube owners decl // S.pins v.val}) (reports : S.actual q.val.val)

local notation3 (prettyPrint := false) "full" => (F.sourceEquiv fixed S B agree).symm ⟨q,reports⟩
local notation3 (prettyPrint := false) "raw" => declaredWords sa.cube owners decl q.val
local notation3 (prettyPrint := false) "z" => F.replay fixed raw
local notation3 (prettyPrint := false) "physical" => (B raw).owned.symm ⟨q.val.val,q.val.property,rfl⟩
local notation3 (prettyPrint := false) "family" => ownedHistory sa.cube (pub z.1) (mac z.1)
  (fun u => ((B raw).constants u).val.2.1) (fun u => ((B raw).constants u).val.2.2) physical
local notation3 (prettyPrint := false) "visited" => fun u =>
  (visitsEquiv sa.id (pub full.1 u) (mac full.1 u) (reg full.1 u) (mem full.1 u)).symm (full.2 u)

local notation3 (prettyPrint := false) "data" => bankData q.val.val.2 sa.cube.header.packetBase sa.cube.singleBank
local notation3 (prettyPrint := false) "numbering" => Fin.valEmbedding ∘ owners q.val.val.1

open PackedHistoryCircuit SignedTaskArena

/-- The header seed and reader words belong to the same restored native
visit as the gadget deck. Its single lookup witness supplies the original
boot, the public publisher, the source writer and the ownership scanner. -/
theorem PreparationFrame.BootLookupAt.ownedReadback {u : Fin (R+1)}
    (h : F.BootLookupAt sa fixed S B q u)
    (p : PositiveFields sa.cube.header.profile sa.cube.n sa.cube.header.d sa.cube.header.cap sa.cube.teams sa.dim w)
    (observedHeader : p.bits=observed L z.1.val fixed)
    (broadcast : (h.args u).dst=h.arena.broadcastBase)
    (size : h.arena.header=PositiveFields.width sa.cube.header.profile sa.cube.n sa.cube.header.d sa.cube.header.cap
      sa.cube.teams sa.dim w)
    (teams : sa.cube.teams=R+1) (teamFit : R+1<2^w) (hw : 0<w)
    {queries guesses gates : ℕ} (endFit : sa.endAddress w queries guesses gates<2^w)
    {entries indices : ℕ} (copies : entries*w≤h.arena.copied) (index : indices≤h.arena.count) :
    ReaderKept h.arena entries indices h.boot.memory (h.boot.pins h.sub).val.2.2 (visited u).owned.val.2.2 ∧
      HeaderSeed sa p (pub full.1 u)
        (rawAddress h.arena sa.cube.header.profile sa.cube.n sa.cube.header.d sa.cube.header.cap)
        u.val (visited u).owned.val.2.2 := by
  let P := h.publication
  have seed := h.boot.taskHeader sa h.arena p h.packet h.old P.directory h.dest sa.cube.cables sa.cube.cells
    h.fresh h.reserve h.gates h.outputs h.fieldWidth h.offset h.stride h.literal
    (by simpa only [observedHeader] using h.loaded) broadcast size teams h.secondary endFit teamFit le_rfl hw
  have source := P.projection.sourceBanks G L sa.cube P.directory P.privatePlacement P.livePlacement P.owner decl
    P.group P.frame header pin P.guess P.dst P.ib P.hb P.sb pub mac reg mem P.epoch P.published P.endReg P.out
    P.events P.history F z.1 u h.arena sa rfl p h.hardware h.args h.boot h.sub h.memAt copies index h.row h.col
    h.head size seed h.geometry h.sourceRoom h.outputRoom h.placement h.publishedAt h.emitted h.secondary
  have observed := F.replay_observed_owned sa fixed S B q h.template h.slots h.delivery h.writer h.rows h.handoff h.groupMap
  exact F.sourceEquiv_owned_banks sa fixed S B agree q reports h.template h.slots h.delivery h.writer h.rows
    h.handoff ⟨_,observed⟩ h.arena p u _ _ _ source.1 source.2.1 source.2.2 h.head h.secondary copies index size

/-- The subtotal header for a semantic finish needs no capacity premise on
the independent reader destination. -/
theorem PreparationFrame.BootLookupAt.ownedHeader {u : Fin (R+1)}
    (h : F.BootLookupAt sa fixed S B q u)
    (p : PositiveFields sa.cube.header.profile sa.cube.n sa.cube.header.d sa.cube.header.cap sa.cube.teams sa.dim w)
    (observedHeader : p.bits=observed L z.1.val fixed)
    (broadcast : (h.args u).dst=h.arena.broadcastBase)
    (size : h.arena.header=PositiveFields.width sa.cube.header.profile sa.cube.n sa.cube.header.d sa.cube.header.cap
      sa.cube.teams sa.dim w)
    (teams : sa.cube.teams=R+1) (teamFit : R+1<2^w) (hw : 0<w)
    {queries guesses gates : ℕ} (endFit : sa.endAddress w queries guesses gates<2^w) :
    HeaderSeed sa p (pub full.1 u) (rawAddress h.arena sa.cube.header.profile sa.cube.n sa.cube.header.d sa.cube.header.cap)
      u.val (visited u).owned.val.2.2 :=
  (h.ownedReadback sa fixed S F B agree q reports p observedHeader broadcast size teams teamFit hw endFit
    (entries:=0) (indices:=0) (by simp) (Nat.zero_le _)).2

end TeamContraction

end BorderVNP
end Computability
end OAI
