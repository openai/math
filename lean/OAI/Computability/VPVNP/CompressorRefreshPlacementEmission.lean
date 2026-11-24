import OAI.Computability.VPVNP.CompressorRefreshPlacementResults
import OAI.Computability.VPVNP.CompressorShrinkScheduledTail
import OAI.Computability.VPVNP.CompressorRefreshPlacementPacket
import OAI.Computability.VPVNP.CompressorSelectedDirectoryEmission
import OAI.Computability.VPVNP.CompressorBlockMetadataWindows
import OAI.Computability.VPVNP.CompressorBlockHeadSequence
import OAI.Computability.VPVNP.CompressorRefreshCoreHeader
import OAI.Computability.VPVNP.CompressorRefreshPlacementGeometry

/-!
# The directory and pointers emitted by the refresh

The placement, DFS metadata and two pointer publications run consecutively.
The ordered singleton rows, their five traversal fields and the native term
table are all read from the final packet memory.
-/

namespace OAI
namespace Computability
namespace VPVNP

noncomputable section

namespace CompressorRecords.RefreshPlacement

open BurstRAM BlockPlanner Compression DescriptorSpace Schedule PhaseRecipe SourceOnline
open SelectedDirectoryHistory PairSimulation.TraversalRows SourceTransport
open scoped Fin.CommRing

variable {k R : Type*} [_root_.Field k] [CommRing R] {S : BlockSchedule k} (B : S.Templates)
variable {g w : ℕ} (base : Word w) (positions blocks t cap : ℕ)
variable (f : B.Entry → R) (hf : B.IsSolution f) (X : State S.portExponent (S.portExponent + g))
variable (c : Refresh.DyadicRefreshChoice X S.graph (Nat.two_pow_pos _)
  (S.port_bound.connected_and_pos S.port_order).1 B.refresh) (sel : List Bool)

local notation "scr" => BlockProgram.script B
local notation "L" => BlockProgram.layout B base.val positions blocks
local notation "pt" => Workspace.ports (arity (Script.catalog scr)) base
local notation "pub" => Schedule.Ports.data pt
local notation "first" => Script.levelsPerBlock scr * t
local notation "cur" => (first) + S.steps
local notation "head" => levelStart L (cur)
local notation "nextHead" => levelStart L (cur + 1)
local notation "st" => (levelStart L (first) : Word w)
local notation "start" => tableBase L (cur) (4 : Fin 6)
local notation "level" => selectedLevel B f hf X c sel
local notation "data" => packed w start X.positions
local notation "W₃" => BlockGroups.refresh B 3
local notation "W₄" => BlockGroups.refresh B 4
local notation "W₅" => BlockGroups.refresh B 5
local notation "W₆" => BlockGroups.refresh B 6
local notation "off" => List.length (Script.initial scr) + t * List.length (Script.block scr)

open private metaTapes from OAI.Computability.VPVNP.CompressorShrinkScheduledTail
open private space from OAI.Computability.VPVNP.CompressorRefreshPlacementPacket
open private offset_length from OAI.Computability.VPVNP.CompressorBlockHeadSequence

private theorem offsets :
    (W₄).before.length = (W₃).before.length + 1 ∧
      (W₅).before.length = (W₄).before.length + 3 := by
  have len := BlockGroups.refreshParts_length B
  have h := offset_length (BlockGroups.refreshParts B) 3 (by rw [len]; decide)
  have k := offset_length (BlockGroups.refreshParts B) 4 (by rw [len]; decide)
  have one : ((BlockGroups.refreshParts B)[3]'(by rw [len]; decide)).length = 1 := rfl
  have three : ((BlockGroups.refreshParts B)[4]'(by rw [len]; decide)).length = 3 := rfl
  rw [one] at h
  rw [three] at k
  constructor
  · rw [BlockGroups.refresh_offset, BlockGroups.refresh_offset, Nat.add_assoc]
    exact congrArg (Nat.add _) h
  · rw [BlockGroups.refresh_offset, BlockGroups.refresh_offset, Nat.add_assoc]
    exact congrArg (Nat.add _) k

private theorem head_span : head + 66 ≤ start ∧ head + 66 ≤ nextHead := by
  have len : levelHeaderWords L = 66 := rfl
  have lo : head + 66 ≤ start := by unfold tableBase arrayBase incidenceStart; omega
  exact ⟨lo, lo.trans ((Nat.le_add_right ..).trans (tableEnd_le_nextLevel L (cur) (4 : Fin 6)))⟩

private theorem placement_tapes (p : Fin 6 → Word w) (k n : ℕ) :
    branchPaths (log p k n) = List.replicate n [] := by
  induction n generalizing k with
  | zero => rfl
  | succ n ih =>
    change [] :: branchPaths (log p (k + 1) n) = _
    rw [ih, List.replicate_succ]

set_option maxHeartbeats 850000 in
-- Matching the actual calendar windows compares the full compiled packet types.
/-- Run the selected singleton-directory scan immediately followed by the
three metadata publications, and identify the directory at their common output. -/
theorem install_metadata (m : Memory w) (live : t < blocks) (size : X.positions ≤ positions)
    (fit : endAddress L < 2 ^ w) (rows : m (pt).rows.val = (directoryRows L : Word w))
    (pitch : m (pub 1 - 1).val = (levelWords L : Word w)) (clock : scanCap scr 42 ≤ cap)
    (dH : ℕ) (header : LevelFields.Published L (cur) level dH m)
    (pointers : PortRefresh.TraversalHeaders.HeadBank L (cur) (level).oldSlots m) :
    ∃ ps, MetadataResult B base positions blocks t cap f hf X c sel m ps := by
  have cap13 : scanCap scr 13 ≤ cap := by unfold scanCap at clock ⊢; omega
  obtain ⟨ps, group₃, phase₃, log₃, ⟨dir, bank⟩, old, cols, frame₃⟩ :=
    install B base positions blocks t f hf X c sel cap m live size fit rows pitch cap13
      dH header pointers
  let mid := post m ps
  have span := head_span B base positions blocks t
  have low := (levelStart_mono L (Nat.zero_le (cur)))
  have ctl := Window.lowCells (A := scr) L base rfl rfl
    ((levelStart_mono L (Nat.zero_le (L).levels)).trans_lt fit)
  have nr := (frame₃ _ (.inl (ctl.1.trans_le (by omega)))).trans rows
  have stride := (frame₃ _ (.inl (ctl.2.trans_le (by omega)))).trans pitch
  have entry : LevelFields.Entry L (first) pub st mid := ⟨rfl, stride⟩
  obtain ⟨qs, group₄, phase₄, published⟩ :=
    BlockMetadata.refresh_group B base positions blocks t cap mid live fit nr stride clock
      X.positions (LevelFields.eval_dimensions entry old).1
  have room := PublishedHeads.level_room B base positions blocks t S.steps live le_rfl fit
  obtain ⟨h₀, h₂, _, h₃, h₅, h₄⟩ :=
    metadata_values B base positions blocks t f hf X c sel mid dH entry old cols room
  have vals := SelectedDirectoryHistory.placement_words published
    (bank ▸ ⟨h₀, h₂, h₃, h₅, h₄⟩ :
      PlacementWords (fun j => (BlockMetadata.fieldExprs (L).shape S.steps B.recordLimit
        (slotDegree S) (BlockMetadata.refreshFields B) j).eval pub st mid) dir.pub)
  have lower := (packed_geometry B base positions blocks t X.positions size live fit
    (by omega)).1
  let e := Emission.ofPublished (v := level) published dir (bank ▸ lower) vals
  let e₀ := e.prepend (frame₃ _ (.inl (by omega))) (frame₃ _ (.inl (by omega)))
  have pubEq : e₀.dir.pub = data :=
    (Emission.prepend_pub e (frame₃ _ (.inl (by omega))) (frame₃ _ (.inl (by omega)))).trans
      ((Emission.ofPublished_pub (v := level) published dir (bank ▸ lower) vals).trans bank)
  have emits : ∃ e : Emission L (cur) level m
      (after mid (eventLog (qs.flatMap SourceWalk.Packet.reports))),
      e.dir.pub = data := ⟨e₀, pubEq⟩
  have len : ps.length = 1 := by
    have h := congrArg List.length phase₃
    simp only [List.length_map, Window.indices, List.length_ofFn] at h
    exact h.trans (by rfl)
  have index : off + (W₃).before.length + ps.length = off + (W₄).before.length := by
    rw [(offsets B).1, len, Nat.add_assoc]
  have afterEq : post m (ps ++ qs) = after mid (eventLog (qs.flatMap SourceWalk.Packet.reports)) :=
    post_append m ps qs
  refine ⟨ps ++ qs, ?_⟩
  constructor
  · apply group₃.append
    change SourceOnline.Group scr L base cap (off + (W₃).before.length + ps.length)
      (directoryRows L) mid qs
    rw [index]; exact group₄
  · rw [List.map_append, phase₃, phase₄]; rfl
  · rw [List.flatMap_append, RAMBuckets.cost_append, log₃, published.charge,
      (cost data 0 X.positions).2.1]
  · rw [afterEq]; exact emits
  · rw [afterEq]; exact published.payload 0
  · intro n newRows hlen bankNext
    rw [afterEq]
    exact metadata_geometry B base positions blocks t f hf X c sel published live size fit
      nr stride old cols frame₃ hlen bankNext
  · intro n hlen
    rw [afterEq]
    exact SelectedChildDirectory.Stored.of_refresh f hf X c sel published entry old cols room nr
      ((frame₃ _ (.inl (by omega))).trans hlen)
  · have mb := metaTapes published.source
    rw [published.length] at mb
    rw [List.flatMap_append, PublishedHeads.chronological_tapes _ _ group₃.chronological,
      PublishedHeads.chronological_tapes _ _ group₄.chronological, log₃, placement_tapes, mb,
      List.replicate_add]
  · rintro x ⟨hs, hh, hn, hr⟩
    rw [afterEq]
    have hx := published.outside x hh (by rwa [← Nat.add_assoc]) (by rwa [← Nat.add_assoc])
    exact hx.trans (frame₃ x hs)

local notation "shape" => RefreshBlockPlan.shape B
local notation "arena" => arrayBase L (cur)
local notation "tmp" => PortRefresh.Allocation.plan X (S.degreeExponent 0)
  (PortRefresh.LevelRecipe.Shape.dH shape) (PortRefresh.LevelRecipe.Shape.ties shape)
  (PortRefresh.LevelRecipe.Shape.stride shape) arena
local notation "termVals" => BlockHeadStability.refreshTerms B
local notation "nextVals" => (fun _ : Fin 1 => LevelFields.atLevel (S.steps + 1))

set_option maxHeartbeats 1600000 in
-- The selected term and traversal share the dependent block memory and packet types.
/-- The final five pointer publications retain the selected directory and
record the native refresh term bank and physical successor header. -/
theorem install_tail (m : Memory w) (live : t < blocks) (size : X.positions ≤ positions)
    (fit : endAddress L < 2 ^ w) (rows : m (pt).rows.val = (directoryRows L : Word w))
    (pitch : m (pub 1 - 1).val = (levelWords L : Word w)) (clock : scanCap scr 42 ≤ cap)
    (dH : ℕ) (header : LevelFields.Published L (cur) level dH m)
    (pointers : PortRefresh.TraversalHeaders.HeadBank L (cur) (level).oldSlots m) :
    ∃ ps, TailResult B base positions blocks t cap f hf X c sel m ps := by
  obtain ⟨ps, old⟩ := install_metadata B base positions blocks t cap f hf X c sel
    m live size fit rows pitch clock dH header pointers
  let mid := post m ps
  have span := head_span B base positions blocks t
  have before (x : ℕ) (hx : x < head) : mid x = m x := old.frame _ ⟨.inl (by omega),
    .inl (by omega), by omega, by omega⟩
  have lower := levelStart_mono L (Nat.zero_le (cur))
  have ctl := Window.lowCells (A := scr) L base rfl rfl
    ((levelStart_mono L (Nat.zero_le (L).levels)).trans_lt fit)
  have pitch₄ := (before _ (ctl.2.trans_le lower)).trans pitch
  have ready : PublishedHeads.Ready B base positions blocks t cap mid :=
    ⟨live, fit, (before _ (ctl.1.trans_le lower)).trans rows, pitch₄,
      by unfold scanCap at clock ⊢; omega⟩
  have pair := PublishedHeads.refresh_pair B ready
  obtain ⟨qs, group, labels, logs, tapes⟩ := pair.online
  have count : ps.length = 4 := by
    have h := congrArg List.length old.phases
    simp only [List.length_map, List.length_append, Window.indices, List.length_ofFn] at h
    exact h.trans (by rfl)
  have ord : off + (W₃).before.length + ps.length = off + (W₅).before.length := by
    obtain ⟨a, b⟩ := offsets B; omega
  let termMem := PublishedHeads.image pub st mid (head + 36) termVals
  let finalMem := PublishedHeads.image pub st termMem (head + 40) nextVals
  have eqn : post m (ps ++ qs) = finalMem := by
    rw [post_append, post, logs, SourceWalk.after_append]
    rfl
  have keep (x : ℕ) (hx : x < head + 36 ∨ head + 41 ≤ x) : post m (ps ++ qs) x = mid x :=
    (congrFun eqn x).trans (pair.frame _ hx)
  have hfit := (space B base positions blocks t size live fit)
  have pfit := hfit.1.trans_lt hfit.2
  obtain ⟨em, emBank⟩ := old.emits
  have owner : (em.dir.pub 1).val = start := by
    rw [emBank]; exact (packed_values pfit (by have := header.room; omega)).2.1
  have arrays : Agree (Directory.cells em.dir.pub) mid (post m (ps ++ qs)) := by
    intro x hx
    have lo := (Directory.cells_interval em.dir hx).1
    rw [owner] at lo
    exact (keep _ (.inr (by omega))).symm
  let e := em.transfer arrays
    (fun o ho => keep _ (.inl (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ho; omega)))
    (fun o _ => keep _ (.inr (by omega)))
  have cap₄ := PublishedHeads.level_room B base positions blocks t S.steps live le_rfl fit
  have still (n : ℕ) (hn : n < 66) (hf : n < 15 ∨ 27 ≤ n) : mid (head + n) = m (head + n) :=
    old.frame _ ⟨.inl (by omega), by omega, by omega, by omega⟩
  have hdr : LevelFields.Published L (cur) level dH mid :=
    ⟨header.room, (still 0 (by decide) (.inl (by decide))).trans header.vertices,
      (still 1 (by decide) (.inl (by decide))).trans header.degree,
      (still 2 (by decide) (.inl (by decide))).trans header.lanes,
      (still 3 (by decide) (.inl (by decide))).trans header.residual,
      (still 4 (by decide) (.inl (by decide))).trans header.nextDegree,
      (still 5 (by decide) (.inl (by decide))).trans header.expander⟩
  have bank₄ : PortRefresh.TraversalHeaders.HeadBank L (cur) (level).oldSlots mid := by
    constructor
    · intro j
      have hj := j.isLt
      have hj' := still (54 + j.val) (by omega) (.inr (by omega))
      simpa only [incidenceHead, show (L).shape.scalarFields = 54 from rfl, Nat.add_assoc]
        using hj'.trans (by simpa only [incidenceHead,
          show (L).shape.scalarFields = 54 from rfl, Nat.add_assoc] using pointers.incidence j)
    · intro j
      have hj : j.val < 6 := j.isLt
      have h := still (54 + 6 + j.val) (by omega) (.inr (by omega))
      simpa only [tableHead, show (L).shape.scalarFields = 54 from rfl, Nat.add_assoc]
        using h.trans (by simpa only [tableHead,
          show (L).shape.scalarFields = 54 from rfl, Nat.add_assoc] using pointers.tables j)
  let ctx : PortRefresh.LevelRecipe.Context w := ⟨pub, st, mid⟩
  have entry : LevelFields.Entry L (first) pub st mid := ⟨rfl, pitch₄⟩
  have rd := RefreshCore.Header.ofPublished hdr bank₄ rfl (show 0 < 6 by decide) (by omega)
  have src := RefreshCore.Header.describes (s := shape) (X := X) (C := ctx)
    (F := BlockProgram.geometry B) rfl (0 : Fin 6) rfl entry rd
  have termAt := (PortRefresh.LevelRecipe.addresses (s := shape)
    (RefreshBlockPlan.input (BlockProgram.geometry B) S.steps (0 : Fin 6)) ctx X arena
    (packedIncidence L w (cur) (level).oldSlots) src).term_eq
  have termRead (j : Fin 4) : post m (ps ++ qs) (head + 36 + j.val) =
      (termVals j).eval pub st mid := by
    rw [eqn]
    have kept := pair.dataGroup.source.outside (head + 36 + j.val)
      (Or.inl (by have := j.isLt; omega))
    exact kept.trans (pair.termGroup.source.stored j)
  have midPitch := (pair.termGroup.source.outside (pub 1 - 1).val
    (Or.inl (ctl.2.trans_le (by omega)))).trans pitch₄
  have termEntry : LevelFields.Entry L (first) pub st termMem := ⟨rfl, midPitch⟩
  have nextStored := pair.dataGroup.source.stored (0 : Fin 1)
  have nextWord : post m (ps ++ qs) (head + 40) = (nextHead : Word w) := by
    rw [eqn]
    exact nextStored.trans ((LevelFields.eval_atLevel termEntry (S.steps + 1)).trans
      (congrArg (fun n : ℕ => (levelStart L n : Word w)) (Nat.add_assoc ..).symm))
  refine ⟨ps ++ qs, ?_⟩
  constructor
  · apply old.group.append
    rw [ord]; exact group
  · rw [List.map_append, old.phases, labels]; rfl
  · rw [List.flatMap_append, RAMBuckets.cost_append, old.charge, logs,
      PublishedHeads.pair_charge pub st mid head termVals nextVals]
  · exact ⟨e, emBank⟩
  · exact (termRead 0).trans termAt
  · exact termRead 1
  · exact termRead 2
  · exact termRead 3
  · exact nextWord
  · exact (keep _ (.inl (by omega))).trans old.recordWords
  · intro n newRows hlen bankNext
    exact keep_geometry_heads (old.geometry n newRows hlen bankNext) span.2 keep
  · intro n hlen
    exact (old.child n hlen).keep (fun x _ hx => keep x (.inl (by omega)))
  · rw [List.flatMap_append, old.tapes, tapes, ← List.replicate_add]
  · exact fun x hx hx' => (keep x hx').trans (old.frame x hx)

end CompressorRecords.RefreshPlacement

end

end VPVNP
end Computability
end OAI
