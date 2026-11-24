import OAI.Computability.VPVNP.PairShrinkCanonicalSite
import OAI.Computability.VPVNP.PairShrinkHiddenResidentFootprint
import OAI.Computability.VPVNP.PairShrinkNodeStageCost
import OAI.Computability.VPVNP.PairShrinkRoleHiddenTyped
import OAI.Computability.VPVNP.PairShrinkRolePackedHidden
import OAI.Computability.VPVNP.PairShrinkRolePhysicalHidden

/-!
# Hidden-stage reads of a packed shrinking site

The old-level header, the selected owner's resident directory, and the
selected term rows all precede the terminal header. On any successful
hidden read, the decoded fields are a typed assignment at that same owner.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.ShrinkRole.CanonicalSite

open BurstRAM BurstRAM.PrivateRAM Compression Compression.ShrinkMotif NetworkKernel
open CompressorRecords DescriptorSpace SourceTransport ShrinkBlockInputs ShrinkHistoryRows
open ShrinkSlots ShrinkHiddenGuess ShrinkVertexImage
open scoped Fin.CommRing

variable {K : Type} [_root_.Field K] {S : BlockSchedule K} {B : S.Templates}
  {i : Fin S.steps} {g w n t : ℕ} {X : State (a i) (packingLaneBits (a i) g)}
  {sel : SelectedScore.Selection B X} {v : MapResidentRows.Site X}
  (site : CanonicalSite B i X sel v w n t) (H : Word w)

local notation "D" => BlockProgram.layout B site.workspace.val site.positions site.blocks
local notation "head" => levelStart D site.cur
local notation "tab" => (fun j : Fin 6 => tableBase D site.cur j)
local notation "term" => ShrinkInput.termHead (w := w) X (tab 0)
local notation "role" => SelectedArena.roleBase X term (10 : Word w)
local notation "bank" => ShrinkOutput.splitBank (b := b i) X B.shrink sel term 10 role (tab 2)
local notation "R" => TerminalLayout.privateRegions (slotDegree S) n site.rowEnd
  (Fintype.card B.Entry)
local notation "side" => selectedLayout X B.shrink sel
local notation "widths" => ShrinkPreparedCall.width B.shrink X sel
local notation "rows" => ShrinkHiddenSlots.rows X side widths v

/-- The five probes of the physical hidden setup lie in the old-level header. -/
theorem hiddenSetup_reads (terminalFit : H.val + 31 < 2 ^ w)
    (beforeHeader : endAddress D ≤ H.val) (level : site.level = (head : Word w))
    (node : Word w) (saved : DFS.Scratch w n) :
    Reads (TerminalLink.workerCell H) ((physicalHiddenSetup B.shrink.selectorBits (hiddenStride i)
      site.level.val site.mem).trace node saved) := by
  have next := (levelStart_mono D site.bounds.nextLive.le).trans beforeHeader
  have headerEnd : head + 66 ≤ H.val := by
    apply le_trans _ next
    change head + levelHeaderWords D ≤ levelStart D (site.cur + 1)
    simp only [levelStart, Nat.succ_mul, levelWords]
    omega
  have raw : site.level.val = head := by
    rw [level, Fin.val_natCast, Nat.mod_eq_of_lt (by have := H.isLt; omega)]
  rw [raw]
  change Reads _ (List.replicate (VertexLevel.hiddenCount + 1) .tick ++
    Header.canonicalTrace B.shrink.selectorBits (hiddenStride i) (head : Word w) site.mem)
  refine TerminalFootprint.reads_append (TerminalFootprint.reads_ticks _ _) ?_
  let s := B.shrink.selectorBits
  let d := hiddenStride i
  let c : Config w 1 (Table.R s d) := ⟨0, 0, fun _ => (head : Word w), fun _ => 0⟩
  change Reads _ (Header.canonicalTrace s d (head : Word w) site.mem)
  rw [← Header.trace_canonical s d (Table.segmentInputs s d) (Table.vm s d) c site.mem
    (head : Word w) rfl]
  refine Header.trace_reads (TerminalLink.workerCell H) s d (Table.segmentInputs s d)
    (Table.vm s d) c site.mem head rfl (by have := H.isLt; omega) ?_
  intro j hj
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
  exact TerminalFootprint.below H terminalFit (by omega)

set_option maxHeartbeats 1600000 in
-- The field directory and each guessed assignment are indexed by the selected owner.
/-- Every accepted hidden-field tape reads the resident count, dense IDs and
term cells of this packed site below the terminal header. -/
theorem hiddenReader_reads (terminalFit : H.val + 31 < 2 ^ w) (beforeHeader : endAddress D ≤ H.val)
    (payload : CompiledResident.ShrinkPayload B site.workspace site.positions site.blocks n
      site.cur i X sel site.mem)
    (args : site.hiddenArgs = PackedHidden.arguments B i X sel site.workspace site.positions
      site.blocks site.cur n R v)
    {node : Word w} {saved : DFS.Scratch w n} {bs tail : List Bool}
    {out : Outcome w n (List Row)}
    (hit : hiddenReader site.hiddenArgs site.mem (rows site.seed) node saved bs =
      some (out, tail)) :
    Reads (TerminalLink.workerCell H) out.trace := by
  obtain ⟨h, shape, _⟩ := (hiddenReader_typed X side widths v site.hiddenArgs site.mem site.seed
    hit).exists
  rw [(ShrinkNodeCost.hidden_trace _ _ _ _ _ _ _ _ hit).1, shape, args]
  have next := (levelStart_mono D site.bounds.nextLive.le).trans beforeHeader
  have resident := site.bounds.residentEnd.trans next
  have stepWord : (10 : Word w).val = 10 :=
    Nat.mod_eq_of_lt (show 10 < 2 ^ w by omega)
  have room := site.bounds.packedRoom
  have slots := site.bounds.slotAfter
  rw [stepWord] at room slots
  have allocation := ShrinkOutput.fits (b := b i) X B.shrink sel term 10 role (tab 2)
    (S.shrink i) (by decide) room
  have lastTable : tab 3 ≤ H.val :=
    (Nat.le_add_right ..).trans ((tableEnd_le_nextLevel D site.cur (3 : Fin 6)).trans next)
  have termBound : (bank).widthBase ≤ H.val :=
    (ShrinkOutput.width_le_slots (b := b i) X term 10 role (tab 2)).trans
      (slots.trans lastTable)
  apply TerminalFootprint.reads_mono _
    (fun _ before => TerminalFootprint.below H terminalFit before)
  exact ShrinkHiddenRows.reads_below X bank site.mem (tab 5) H.val allocation
    (resident.trans_lt H.isLt) resident termBound (payload.sources.residents false) widths v h
    (ShrinkCallABI.hiddenBase R n) (n * n)

end PairSimulation.ShrinkRole.CanonicalSite

end VPVNP
end Computability
end OAI
