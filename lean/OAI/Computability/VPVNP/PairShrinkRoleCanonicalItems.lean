import OAI.Computability.VPVNP.PairShrinkRoleCanonicalInvariant
import OAI.Computability.VPVNP.PairShrinkLiveMapItems
import OAI.Computability.VPVNP.PairShrinkRoleOriginPackets

/-!
# Exact map items for arbitrary parsed lists at a physical shrinking site

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

variable (M : Machine w p r 11) (pc : Fin (shrinkSegment B ord).count → Fin p)
  (saved : VertexImage.Saved ↪ Fin r) (done : Fin p)

set_option maxHeartbeats 3500000 in
-- The native gather, witness, and packet placement use dependent old and output coordinates.
theorem canonicalInv_items
    (installed : ∀ j, M.code (pc j) = ((shrinkSegment B ord).row pc dfs saved reg done j).resize w)
    (ds : ∀ j k, reg j ≠ dfs k) (ss : ∀ j k, reg j ≠ saved k)
    (H : Word w) (terminalRoom : H.val + 31 < 2 ^ w)
    (levelEq : site.level = (levelStart
      (BlockProgram.layout B site.workspace.val site.positions site.blocks) site.cur : Word w))
    (sources : ∀ old q, ShrinkSiteBank.RowSources B i X sel site.workspace site.positions
      site.blocks site.cur site.bounds n site.rowEnd site.older site.later v old parent
      site.mem H q)
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
        List.ofFn fun j => (((readerAt).order.children v).entries j).val) :
    Items (mapLoop B ord i pc reg done) M site.mem dfs (canonicalInv site ord dfs reg ready xs es)
      (firstMap B i site.source v) (canonicalActions site ord f hf parent xs es) := by
  let old := oldFields (term := termAt) X v ((readerAt).order.children v) xs
  let hidden := hiddenFields X side widths v site.seed es
  unfold canonicalActions typedActions canonicalInv
  change Items _ _ _ _
    (OriginInvariant (fun (o : Origin) node => o.node = node)
      (fun o => ShrinkSiteBank.siteInvariant site common o.entry)) _
    (canonicalBank site ord parent old hidden)
  apply Items.existsInvariant (ShrinkSiteBank.actions_quiet site ord parent old hidden)
  intro o
  have word : o.node = ((addr : ℕ) : Word w) :=
    (Fin.cast_val_eq_self o.node).symm.trans (congrArg (fun k : ℕ => (k : Word w)) o.atRow)
  apply ShrinkSiteBank.exact_items (p := p) (r := r) (n := n) (w := w) (g := g)
    (X := X) (B := B) (i := i) (sel := sel) (v := v) site ord parent old hidden M pc dfs
    saved reg done
    installed ds ss H terminalRoom levelEq (sources old) o.entry _ (word ▸ o.operands)
  exact origin_packets (p := p) (r := r) (n := n) (w := w) (g := g)
    site ord f hf parent dfs reg ready xs es o space oldNodes parentFit
    earlier wire size room baseEq strideEq stored orderAt

end PairSimulation.ShrinkRole

end VPVNP
end Computability
end OAI
