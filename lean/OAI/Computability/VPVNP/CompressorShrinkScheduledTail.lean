import OAI.Computability.VPVNP.CompressorBlockHeadSequence
import OAI.Computability.VPVNP.CompressorBlockMetadataWindows

/-! # The three terminal DFS publication windows of a shrink

Starting at the actual memory after the slot construction, the metadata
writer emits its twelve old-header operands and two successor words. The
term and data writers then fill eighteen old-header words. Each report is
from the installed phase at its chronological ordinal.
-/

namespace OAI
namespace Computability
namespace VPVNP

noncomputable section

namespace CompressorRecords.ShrinkScheduledTail

open BurstRAM DescriptorSpace BlockPlanner PhaseRecipe Schedule Compression SourceOnline SourceTransport
open scoped Fin.CommRing

variable {w : ℕ} {k : Type*} [_root_.Field k] {S : BlockSchedule k} (B : S.Templates)
variable (base : Word w) (positions blocks t cap : ℕ) (i : Fin S.steps)
local notation "prog" => BlockProgram.script B
local notation "L" => BlockProgram.layout B base.val positions blocks
local notation "pt" => Workspace.ports (arity (Script.catalog prog)) base
local notation "pub" => Ports.data pt
local notation "first" => Script.levelsPerBlock prog * t
local notation "st" => (levelStart L (first) : Word w)
local notation "oldHead" => levelStart L (first+i.val)
local notation "newHead" => levelStart L (first+(i.val+1))
local notation "origin" => tableBase L (first+i.val) (0 : Fin 6)
local notation "termVec" => BlockHeadStability.shrinkTerms B i
local notation "headVec" => PublishedHeads.dataValues B i
local notation "startOrdinal" => ShrinkForward.first B i t + ShrinkForward.visitsBefore B i 9
local notation "Packet₀" => SourceOnline.Packet prog w
local notation "metaW" => BlockGroups.shrink B i 9
local notation "termW" => BlockGroups.shrink B i 10
local notation "dataW" => BlockGroups.shrink B i 11

variable {g : ℕ} (X : State (ShrinkBlockInputs.a i) (packingLaneBits (ShrinkBlockInputs.a i) g)) (m : Memory w)
local notation "meta" => BlockMetadata.Published B base positions blocks t i.val BlockMetadata.Role.shrink (BlockMetadata.shrinkFields B i) m (ShrinkPreimages.oldCount X)

/-- Memory after writing the term base, term stride, selected layout bit, and absolute motif
table base to offsets 36 through 39 of the old level header. -/
def termImage (mem : Memory w) := PublishedHeads.image pub st mem (oldHead+36) termVec

/-- Memory after writing the fourteen data pointers used by the shrinking node reader to
offsets 40 through 53 of the old level header. -/
def dataImage (mem : Memory w) := PublishedHeads.image pub st mem (oldHead+40) headVec

/-- Exact post-images of the three groups, together with their fixed online
control positions. -/
structure Result (metadata ps : List Packet₀) : Prop where
  group : Group prog L base cap startOrdinal (directoryRows L) m ps
  phases : ps.map (fun p ↦ p.stage.phase) = (metaW).indices++(termW).indices++(dataW).indices
  baseFields : meta (metadata.flatMap SourceWalk.Packet.reports)
  published : PublishedHeads.Pair B base positions blocks t i.val cap (post m metadata) termVec headVec termW dataW
  image : post m ps = dataImage B base positions blocks t i (termImage B base positions blocks t i (post m metadata))
  tapes : ps.flatMap (fun p ↦ p.stage.choices) = List.replicate 21 []
  charge : RAMBuckets.cost Report.probes (ps.flatMap SourceWalk.Packet.reports) = 53

private theorem header_gap : oldHead+66 ≤ newHead := by
  have size : levelHeaderWords L = 66 := rfl
  rw [show first+(i.val+1)=(first+i.val)+1 by omega]
  simp only [levelStart,Nat.succ_mul,levelWords,size]
  omega

variable {B base positions blocks t cap i X m}

theorem Result.outside {ms ps : List Packet₀} (r : Result B base positions blocks t cap i X m ms ps) (x : ℕ)
    (metaOutside : x < oldHead+15 ∨ oldHead+27 ≤ x) (headOutside : x < oldHead+36 ∨ oldHead+54 ≤ x)
    (baseOutside : x ≠ newHead+14) (roleOutside : x ≠ newHead+27) :
    post m ps x = m x := by
  rw [r.image]
  have d := r.published.dataGroup.source.outside x (by unfold PublishedHeads.Outside; omega)
  have h := r.published.termGroup.source.outside x (by unfold PublishedHeads.Outside; omega)
  exact d.trans (h.trans (r.baseFields.outside x metaOutside baseOutside roleOutside))

theorem Result.metaCell {ms ps : List Packet₀} (r : Result B base positions blocks t cap i X m ms ps) (x : ℕ)
    (outside : x < oldHead+36 ∨ oldHead+54 ≤ x) : post m ps x = post m ms x := by
  rw [r.image]
  have d := r.published.dataGroup.source.outside x (by unfold PublishedHeads.Outside; omega)
  exact d.trans (r.published.termGroup.source.outside x (by unfold PublishedHeads.Outside; omega))

theorem Result.earlier {ms ps : List Packet₀} (r : Result B base positions blocks t cap i X m ms ps)
    (x : ℕ) (hx : x < oldHead) : post m ps x = m x := by
  have := header_gap B base positions blocks t i
  apply r.outside <;> omega

/-- Both this level's packed tables and the successor's canonical packed
incidence region lie outside the two scalar publication blocks. -/
theorem Result.old_data {ms ps : List Packet₀} (r : Result B base positions blocks t cap i X m ms ps)
    (x : ℕ) (lo : oldHead+54 ≤ x) (hi : x < newHead) : post m ps x = m x := by
  apply r.outside <;> omega

theorem Result.next_data {ms ps : List Packet₀} (r : Result B base positions blocks t cap i X m ms ps)
    (x : ℕ) (lo : newHead+28 ≤ x) : post m ps x = m x := by
  have := header_gap B base positions blocks t i
  apply r.outside <;> omega

theorem Result.length {ms ps : List Packet₀} (r : Result B base positions blocks t cap i X m ms ps) :
    ps.length = 21 := by
  have h := congrArg List.length r.phases
  simp only [Window.indices,List.length_map,List.length_append,List.length_ofFn] at h
  change ps.length = 3+4+14 at h
  exact h

private theorem metaTapes {p : Fin 5 → Word w} {s : Word w} {ls : List BlockPlanner.Visit} {raw : Memory w}
    {rs : List (Report w)} (walk : SourceWalk (BlockMetadata.Source p s) ls raw rs) :
    branchPaths rs = List.replicate rs.length [] := by
  induction walk with
  | done => rfl
  | @next v vs before xs ys call _ ih =>
    obtain ⟨f,r,rfl,_,_,_,hr⟩ := call
    have bits := (execute_iff.mp hr).2.2
    change choiceBits r.events :: branchPaths ys = _
    simp only [List.singleton_append,List.length_cons,List.replicate_succ,bits,ih]

variable (B base positions blocks t cap i X m)

/-- Run Parts 9, 10 and 11 at their fixed program ordinals from the
post-slot memory. All capacity bounds use the real table-zero allocation. -/
theorem run (T : IncidenceDirectory w)
    (header : ShrinkHeaderReads.Header i X T origin L (first) m) (sites : X.positions ≤ positions)
    (ht : t < blocks) (fit : endAddress L < 2^w) (rows : m (pt).rows.val = (directoryRows L : Word w))
    (pitch : m (pub 1-1).val = (levelWords L : Word w)) (clock : scanCap prog 42 ≤ cap) :
    ∃ ms ps : List Packet₀, Result B base positions blocks t cap i X m ms ps := by
  have entry : LevelFields.Entry L (first) pub st m := ⟨rfl,pitch⟩
  have old : (LevelFields.sites i.val).eval pub st m = (ShrinkPreimages.oldCount X : Word w) := by
    have hv := header.reads B entry
    change (LevelFields.vertices i.val).eval pub st m * (LevelFields.lanes i.val).eval pub st m = _
    rw [hv.vertices,hv.lanes,← Nat.cast_mul]
  obtain ⟨ms,mGroup,mPh,hMeta⟩ := BlockMetadata.shrink_group B base positions blocks t cap m i ht fit rows pitch clock _ old
  let afterMeta := post m ms
  have sep := header_gap B base positions blocks t i
  have below (x : ℕ) (hx : x < levelStart L 0) : afterMeta x = m x := by
    have := levelStart_mono L (show 0 ≤ first+i.val from Nat.zero_le _)
    exact hMeta.outside x (Or.inl (by omega)) (by omega) (by omega)
  have hold (j : ℕ) (hj : j ≤ 60) (free : j < 15 ∨ 27 ≤ j) : afterMeta (oldHead+j) = m (oldHead+j) :=
    hMeta.outside _ (by omega) (by omega) (by omega)
  have hdr : ShrinkHeaderReads.Header i X T origin L (first) afterMeta :=
    ⟨header.room,(hold 0 (by decide) (by decide)).trans header.vertices,
      (hold 1 (by decide) (by decide)).trans header.degree,(hold 2 (by decide) (by decide)).trans header.lanes,
      (hold 3 (by decide) (by decide)).trans header.residual,fun c ↦
        (hold (54+c.val) (by have := c.isLt; omega) (.inr (by omega))).trans (header.incidence c),
      (hold 60 (by decide) (by decide)).trans header.scratch⟩
  have low := Window.lowCells (A:=prog) L base rfl rfl ((levelStart_mono L (Nat.zero_le _)).trans_lt fit)
  have small : scanCap prog 7 ≤ scanCap prog 42 := by unfold scanCap; omega
  have ready : PublishedHeads.Ready B base positions blocks t cap afterMeta :=
    ⟨ht,fit,(below _ low.1).trans rows,(below _ low.2).trans pitch,small.trans clock⟩
  have pair := PublishedHeads.shrink_pair B i ready X T hdr sites
  obtain ⟨ps,pGroup,ph,logs,bits⟩ := pair.online
  have num : ms.length = 3 := by
    have e := congrArg List.length mPh
    simp only [Window.indices,List.length_map,List.length_ofFn] at e
    exact e.trans (by rfl)
  have ord : startOrdinal+ms.length = (prog).initial.length+t*(prog).block.length+(termW).before.length := by
    rw [num,BlockGroups.shrink_offset]
    unfold ShrinkForward.first ShrinkForward.visitsBefore
    have h : ((BlockGroups.parts B i).take 10).flatten.length = ((BlockGroups.parts B i).take 9).flatten.length+3 := by
      rw [List.take_succ_eq_append_getElem (show 9 < (BlockGroups.parts B i).length by rw [BlockGroups.parts_length]; decide)]
      rw [List.flatten_append,List.length_append,List.flatten_cons,List.flatten_nil,List.append_nil]
      rfl
    change _+3 = _+(_+((BlockGroups.parts B i).take 10).flatten.length)
    rw [h]
    omega
  have group := mGroup.append (ord ▸ pGroup)
  refine ⟨ms,ms++ps,group,?_,hMeta,pair,?_,?_,?_⟩
  · rw [List.map_append,mPh,ph]
    exact (List.append_assoc ..).symm
  · rw [post_append,post,logs,SourceWalk.after_append]
    rfl
  · have mbits := metaTapes hMeta.source
    rw [hMeta.length] at mbits
    rw [List.flatMap_append,PublishedHeads.chronological_tapes m ms mGroup.chronological,mbits,bits]
    rfl
  · rw [List.flatMap_append,RAMBuckets.cost_append,hMeta.charge,logs,PublishedHeads.pair_charge]

end CompressorRecords.ShrinkScheduledTail

end

end VPVNP
end Computability
end OAI
