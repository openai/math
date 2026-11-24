import OAI.Computability.VPVNP.PairShrinkRoleCanonicalPacketFits
import OAI.Computability.VPVNP.PairShrinkSiteInitialPackets
import OAI.Computability.VPVNP.PairShrinkRoleCanonicalUpdate

/-!
# The shrinking row update from its published site and popped parent

The child and hidden assignments of the selected term determine one private
store shared by all resident jobs. The row directories fit those stores, and
the retained map rows supply the source headers for the counter increments.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.ShrinkRole

open BurstRAM PrivateRAM DFS Compression Compression.PackingData Compression.ShrinkMotif
open NetworkKernel
open LocalHistory NodeArguments NodeArguments.ChildScan ShrinkHiddenGuess LeafSourceLoad
open CompressorRecords CompressorRecords.ShrinkBlockInputs CompressorRecords.ShrinkSlots
open scoped Fin.CommRing
open private termAt readerAt childOrder from OAI.Computability.VPVNP.PairShrinkRoleScheduledSuffix

variable {K : Type} {C : Type*} [_root_.Field K] [CommRing C] {S : BlockSchedule K}
  {B : S.Templates} {i : Fin S.steps} {g n w p r : ℕ}
  {Z : State (a i) (packingLaneBits (a i) g)} {sel : SelectedScore.Selection B Z}
  {v : MapResidentRows.Site Z} {site : CanonicalSite B i Z sel v w n (Fintype.card B.Entry)}
  {M : Machine w p r 11} {f : B.Entry → C} {hf : B.IsSolution f} {lanes T : ℕ}
  {hT : T * S.laneBits ≤ lanes} {X : State (S.degreeExponent 0) lanes}
  {z : (B.execute f hf T hT X).Choices} {j : Fin (executeLevels B f hf T hT X z).length}
  {id : Fin (executeLevels B f hf T hT X z)[j].outputSites} {base : ℕ}

private noncomputable local instance : DecidableEq Z.Base := Classical.decEq _
local notation "regions" => TerminalLayout.privateRegions (slotDegree S) n site.rowEnd
  (Fintype.card B.Entry)
local notation "side" => selectedLayout Z B.shrink sel
local notation "widths" => ShrinkPreparedCall.width B.shrink Z sel
local notation "Y" => Z.shrinkNext B.shrink (S.shrink i) sel
local notation "nodeAddr" => site.later + (B.recordLimit + 2) *
  PortRefresh.ArgumentAddress.siteOrdinal (Y) v
local notation "rdr" => readerAt B f hf i Z sel
local notation "ordAt" => childOrder B f hf i Z sel v
local notation "term" => termAt B f hf i Z sel
local notation "ptr" => childNode Z site.older B.recordLimit
local notation "heap" => ShrinkCallABI.hiddenBase regions n

variable (info : CanonicalSiteData site M f hf T hT X z j id base)
  (ord : B.Entry ≃ Fin (Fintype.card B.Entry))
  (old : Placed (Z.packingData.shrinkPlace (selectedLayout Z B.shrink sel) ∘
    Z.packingInputIso.site.symm) Z.network.Half v)
  (parent : (Z.shrinkNext B.shrink (S.shrink i) sel).network.Half v) {H : Word w}
  (maps : CanonicalMapData site H parent)

local notation "W" => B.shrinkPassWitnesses f hf i rfl Z sel v old parent
local notation "jobs" => ShrinkSiteBank.jobs B i Z sel site.workspace site.positions site.blocks
  site.cur site.bounds n site.rowEnd site.older site.later v old parent
local notation "packetsAt" => TreeDecode.children rdr
  (fun u b => Packet.mk (ptr u) (packed Z u b)) v old

set_option maxHeartbeats 1200000 in
-- Elaborating the scheduled witness compares its packed site and half assignments.
/-- A choice of hidden fields and resident map witnesses for these two physical half assignments. -/
private noncomputable def rowChoice : Type := (W).Choice

local notation "RowChoice" =>
  rowChoice (B := B) (f := f) (hf := hf) (i := i) (Z := Z) (sel := sel) (v := v) old parent

set_option maxHeartbeats 1200000 in
-- Construct the scheduled reader's choice tape once at its concrete physical site.
/-- The choice tape and parameter increments of the selected native vertex job. -/
private noncomputable def selectedJob (node : Word w) (x : RowChoice) : VertexJob B.Entry :=
  ⟨node.val, (rdr).nodeBits v old parent x, (W).exponents x⟩

local notation "chosenJob" =>
  selectedJob (B := B) (f := f) (hf := hf) (i := i) (Z := Z) (sel := sel) (v := v) old parent

include info maps

set_option maxHeartbeats 4000000 in
-- The native maps reindex the same term choices over their resident placement equalities.
theorem CanonicalSiteData.update (x : RowChoice) (node : Word w) (saved : Scratch w n)
    (atRow : node.val = nodeAddr)
    (stored : (Packet.mk node.val (packed (Y) v parent)).Stored (regions).arguments saved)
    (data : Fin 10 → Word w) (offset : Word w) (vals : Static 34 → Word w)
    (frame : TreeDecode.VertexFrameData regions data offset vals saved)
    (tail : List Bool) (job : VisitPath w n)
    (hit : (canonicalParent site ord f hf).read node saved
      ((chosenJob node x).bits ++ tail) = some (job, tail)) :
    RowUpdate regions ord data offset vals saved job packetsAt (chosenJob node x).increment := by
  let xs := children (t := term) Z v ordAt old
  let es := ShrinkHiddenSlots.rows Z side widths v x.1
  let batch := xs.map (Child.packet Z site.older B.recordLimit)
  let baseline := storeRows heap (n ^ 2) es (storePackets (regions).arguments batch
    (rawScratch saved))
  have rep : scratch n (rawScratch saved) = saved := by
    funext q
    simp only [DFS.scratch, rawScratch, dite_eq_left q.prop]
  have present : (Packet.mk nodeAddr (packed (Y) v parent)).Stored (regions).arguments
      (scratch n (rawScratch saved)) := by rwa [rep, ← atRow]
  have initial (q) : (jobs q).Packets n baseline := (ShrinkSiteBank.initialPackets B f hf i Z
    sel site.workspace site.positions site.blocks site.cur site.bounds n site.rowEnd site.older
    site.later site.limit v old parent x.1 q (rawScratch saved) xs es rfl rfl (maps.space old q)
    info.oldNodes info.parentFit info.earlier info.wire present info.hiddenWidth info.hiddenRoom).1
  have widthsFit := ShrinkHiddenSlots.rows_fit Z heap (n ^ 2) side widths v x.1 info.hiddenWidth
    info.hiddenRoom
  have positive : 0 < w := by
    by_contra! h
    have hw : w = 0 := by omega
    have stride := info.strideFit
    rw [hw, pow_zero] at stride
    omega
  obtain ⟨fits, nodes, above, before⟩ := info.childPacketFits node atRow old
  exact canonicalParent_update site ord f hf old parent x node saved stored positive data offset
    vals frame (info.orderAt node atRow) info.baseEq before
    ((Nat.le_add_right ..).trans info.hiddenRoom)
    (fun e he => info.strideEq ▸ (widthsFit e he).2) fits nodes above baseline initial
    (canonicalOldPublished site old parent H info.levelEq (maps.sources old)) tail job hit

end PairSimulation.ShrinkRole

end VPVNP
end Computability
end OAI
