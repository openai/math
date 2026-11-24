import OAI.Computability.VPVNP.PairShrinkRoleCanonicalInvariant
import OAI.Computability.VPVNP.PairShrinkSiteInitialPackets

/-!
# Resident packet readback at a canonical shrinking map origin

The initial memory consists of the original caller's scratch, the decoded child
packets and the absorbed fields. At each resident occurrence these stores supply
the independent old halves, the popped parent and the shared hidden inputs.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.ShrinkRole

open BurstRAM BurstRAM.PrivateRAM Compression Compression.PackingData Compression.ShrinkMotif
open NetworkKernel CompressorRecords DescriptorSpace ShrinkBlockInputs ShrinkSlots LocalHistory
open ShrinkVertexImage ShrinkMapImage.Registers MapResidentRows
open NodeArguments NodeArguments.ChildScan
open ShrinkHiddenGuess ResidentMapLoop.Exact
open scoped Fin.CommRing

variable {K : Type} {R : Type*} [_root_.Field K] [CommRing R] {S : BlockSchedule K}
  {B : S.Templates}
  {i : Fin S.steps} {g w n p r : ℕ} {X : State (a i) (packingLaneBits (a i) g)}
  {sel : SelectedScore.Selection B X} {v : MapResidentRows.Site X}
  (site : CanonicalSite B i X sel v w n (Fintype.card B.Entry))
  (ord : B.Entry → Fin (Fintype.card B.Entry)) (f : B.Entry → R) (hf : B.IsSolution f)
  (parent : (X.shrinkNext B.shrink (S.shrink i) sel).network.Half v)
  (dfs : Fin 9 ↪ Fin r) (reg : Fin (shrinkSegment B ord).privateRegs ↪ Fin r)
  (ready : DFS.Scratch w n → Prop)

private noncomputable local instance : DecidableEq X.Base := Classical.decEq _
local notation "regions" => TerminalLayout.privateRegions (slotDegree S) n site.rowEnd
  (Fintype.card B.Entry)
local notation "side" => selectedLayout X B.shrink sel
local notation "widths" => ShrinkPreparedCall.width B.shrink X sel
local notation "Y" => X.shrinkNext B.shrink (S.shrink i) sel
local notation "addr" => site.later + (B.recordLimit + 2) * PortRefresh.ArgumentAddress.siteOrdinal
  (Y) v
local notation "rowsAt" => ShrinkHiddenSlots.rows X side widths v
local notation "common" => shared B ord i reg
set_option quotPrecheck false in
local notation "readerAt" => (shrinkPassReaders B f hf i rfl X).termParsers sel
set_option quotPrecheck false in
local notation "termAt" => (B.shrinkPassAt f hf i rfl X).step.term sel
local notation "heap" => ShrinkCallABI.hiddenBase regions n
local notation "jobs" => ShrinkSiteBank.jobs B i X sel site.workspace site.positions site.blocks
  site.cur site.bounds n site.rowEnd site.older site.later v

variable (xs : List (Child X)) (es : List ShrinkHiddenGuess.Row)

open private rowOrigin from OAI.Computability.VPVNP.PairShrinkRoleCanonicalInvariant
local notation "Origin" => rowOrigin (p := p) site ord dfs reg ready xs es

set_option quotPrecheck false in
local notation "chosenOld" => oldFields (term := termAt) X v ((readerAt).order.children v) xs
local notation "chosenHidden" => hiddenFields X side widths v site.seed es
local notation "J" => jobs chosenOld parent

set_option maxHeartbeats 2200000 in
-- Each resident half is transported along its actual packed site.
theorem origin_packets (o : Origin)
    (space : ∀ old q, ShrinkCanonicalJob.PacketSpace B i X sel q.1.1 q.1.2 (jobs old parent q)
      n site.limit)
    (oldNodes : ∀ u, childNode X site.older B.recordLimit u < site.rowEnd)
    (parentFit : addr < site.rowEnd) (earlier : ∀ u, childNode X site.older B.recordLimit u < addr)
    (wire : X.maxWireWidth ≤ n) (size : ∀ m t, widths m (!side, t) ≤ n ^ 2)
    (room : heap + (ShrinkHistoryRows.hiddenOrder X).length * n ^ 2 ≤ 2 ^ w)
    (baseEq : site.hiddenArgs.scratchBase = heap) (strideEq : site.hiddenArgs.slotStride = n ^ 2)
    (stored : ∀ s, ready s → (Packet.mk addr (packed (Y) v parent)).Stored (regions).arguments s)
    (orderAt : ∀ node : Word w, node.val = addr →
      (site.descriptor node).sites =
        List.ofFn fun j => (((readerAt).order.children v).entries j).val)
    (q : X.packingData.ResidentMap side v) :
    (J q).Packets n o.entry.privateMem ∧ (J q).ChildWords o.entry.privateMem n ∧
      ShrinkCallSupplyCells.Absorbed X side widths q.1.1 q.1.2 (J q).scratch
        (q.2.symm ▸ chosenHidden) o.entry.privateMem ∧
      (∀ u, (J q).arena.base ((J q).nodes u) + (J q).arena.stride ≤ (J q).scratch.hist) ∧
      (J q).arena.base (J q).node + (J q).arena.stride ≤ (J q).scratch.hist := by
  have child := children_oldFields (term := termAt) X v ((readerAt).order.children v) xs
    (o.sites.trans (orderAt o.node o.atRow))
  have abs := rows_hiddenFields X side widths v site.hiddenArgs site.mem site.seed es
    o.node o.parsed
  have inputs := ShrinkSiteBank.initialPackets B f hf i X sel site.workspace site.positions
    site.blocks site.cur site.bounds n site.rowEnd site.older site.later site.limit v chosenOld
    parent
    chosenHidden q o.before xs es child abs (space chosenOld q) oldNodes parentFit
    earlier wire
    (stored _ o.prepared) size room
  rw [o.operands.memory, baseEq, strideEq]
  exact inputs

end PairSimulation.ShrinkRole

end VPVNP
end Computability
end OAI
