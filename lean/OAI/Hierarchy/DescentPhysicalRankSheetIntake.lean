import OAI.Hierarchy.DescentRecordedRankPortMounted
import OAI.Hierarchy.DescentRankSheetShapes
import OAI.Hierarchy.DescentResetRankIntake

namespace OAI
/-! # Actual input words of the physical ranked-window compiler -/
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


variable (bound : used≤(s₀).hosts)
local notation "peer_" => Compact.pull (compactRankName B pad) bound rows₀


open DescentResetRankedWindows DescentResetCandidatePair DescentPackedZip DescentResetFieldAssembler
local notation "ST" => (v₀).sheetsStart base₀
local notation "X" => 2^k
local notation "N" => totalLocal B
local notation "b₁" => (s₀).metaBits
local notation "b₂" => originalBits D k n ht (A).cap (programCount ctl.board ht) g
local notation "t" => I.sectors.pageBits
local notation "dense₀" => ((Z).denseHostRank T ((B.frame.host.symm.toEmbedding.trans input.vertex).trans
    (Fin.castLEEmb pad))).trans (Fin.castLEEmb bound)
local notation "rack₀" => rackOf B dense₀
local notation "P₀" => (v₀).rankPorts base₀
local notation "dst" => (v₀).receiver
local notation "pos" => CandidateSheet.index (stemsCount B) (contactCount B) (privateCount B)
variable (oldSort : SourceSorted W input.order) (elapsed : 0< i) {cost : ℕ} (record : B.Recorded cost)
  (hx : (dst).blocks=X) (hs : I.sectors.stems=stemsCount B) (hc : I.sectors.contacts=contactCount B)
  (hp : I.sectors.privates=privateCount B) (hosts : (dst).hosts=(s₀).hosts)
  (groups : (dst).groups=gs) (sameGroups : (s₀).groups=gs) (lanes : (dst).lanes=(s₀).lanes)
local notation "headers" => shaped hx hs hc hp I.sectors.header
local notation "keys" => shaped hx hs hc hp I.sectors.original
variable (ok : I.Ready)

include paid seen oldSort elapsed record hosts groups sameGroups lanes in
/-- The only varying candidate inputs are the previously issued four-family
metadata and comparison words. The sort, bank addresses, native copy and both
order functions are fixed by the physical date. -/
def reached_sheet_rank
    (four : ∀v:B.next.V,present rows₀ (named₀ v)=(insert v (B.reset.emittedNear T v)).map named₀)
    (forward : ∀v:B.next.V,m (((v₀).rankPortRegs base₀).forward.base+(named₀ v).val)=
      (((compactActorOrder B pad v).val):Word bw))
    (metaRead : ∀x j,Source (headers x j) (fun rowId groupId=>DescentResetFieldAssembler.raw b₁ (actualMeta B rack₀ x (pos j) rowId groupId))
      (s₀).lanes (I.sheetsEntry ok m))
    (wordRead : ∀x j,Source (keys x j)
        (fun rowId groupId=>(actualParentNumber B rack₀ x (pos j) rowId groupId:Cell b₂)) (s₀).lanes (I.sheetsEntry ok m)) :
    RankSources B (b:=b₁) («t»:=b₂) (M:=(s₀).lanes) rack₀ P₀
      (sheetHeader B ST t) (sheetOriginal B ST t) (((v₀).rankPortPhase base₀ bw).image (I.before_ports ok m)):=by
  have width : DescentResetLocalRoster.fieldBits (2^g*(A).cap)≤b₁:=by
    rw [cal.fieldWidth,paid]
    exact le_max_left _ _
  have mont:=ranked_port_memory B oldBatch batch calendar I cal pad prior xs raw near m seen bound ok four forward
  rw [sameGroups] at mont
  have limit:=ok.matched
  rw [hx,hs,hc,hp] at limit
  have keep:=(v₀).rankPort_any base₀ bw (I.before_ports ok m) ok.rankPorts
  have vis : I.before_ports ok m=DescentResetCandidatePair.memory ST t (s₀).hosts gs (s₀).lanes
      headers keys (I.sheetsEntry ok m):=shaped_memory hx hs hc hp I.sectors.header I.sectors.original
        ST t hosts groups lanes (I.sheetsEntry ok m)
  have area : (s₀).hosts*chunks gs (s₀).lanes≤2^t:=by
    simpa only [hosts,groups,lanes] using ok.rows
  have space : (v₀).candidateEnd base₀<2^bw:=
    ((v₀).rankPort_after base₀).trans_lt ok.rankPorts.limit
  exact rank_compact_reads B dense₀ width ST t P₀ headers keys (I.sheetsEntry ok m) _ peer_
    (compactRank_order B pad bound) record (compactRank_present B pad near four bound) mont
    (fun a ha=>(keep.2 a (.inl (limit ▸ ha))).trans (congrFun vis a))
    (shaped_fits hx hs hc hp I.sectors.header ST ok.header)
    (shaped_fits hx hs hc hp I.sectors.original ST ok.original)
    metaRead wordRead area (limit.symm ▸ space) oldSort elapsed

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
