import OAI.Computability.VPVNP.CompressorShrinkTermForward
import OAI.Computability.VPVNP.CompressorShrinkPublishedHeader
import OAI.Computability.VPVNP.CompressorRecordsShrinkBranch
import OAI.Computability.VPVNP.CompressorPublishedHeadWindows
import OAI.Computability.VPVNP.CompressorBlockGroups

/-!
# Term selection in the chronological shrinking branch

The physical deterministic prefix preserves the level header through the
absolute-ID scatter. The two following packets use the same source logs
and selector tapes as the chosen branch, at the corresponding ordinals of
the tight directory.
-/

namespace OAI
namespace Computability
namespace VPVNP

noncomputable section

namespace CompressorRecords.ShrinkTermOnline

open BurstRAM BlockPlanner Compression DescriptorSpace Schedule ShrinkBlockInputs ShrinkTermPackets
open scoped Fin.CommRing

variable {k : Type*} [_root_.Field k] {S : BlockSchedule k} (B : S.Templates) (i : Fin S.steps)
variable {w g : ℕ} (X : State (a i) (packingLaneBits (a i) g)) (T : IncidenceDirectory w) (start : ℕ)
variable (s : X.ShrinkSelection B.shrink) (fuel : ℕ) (base : Word w) (positions blocks t : ℕ)
local notation "A" => BlockProgram.script B
local notation "W" => window B i
local notation "L" => BlockProgram.layout B (Fin.val base) positions blocks
local notation "head" => levelStart L ((S.steps+1)*t+i.val)
local notation "Z" => ShrinkInput.plan X start
local notation "N" => ShrinkTermInputs.motifCount X

private theorem afterAbsolute {raw : Memory w} (p : ShrinkBranch.Prefix X T start fuel raw)
    (header : ShrinkHeaderReads.Header i X T start L ((S.steps+1)*t) raw) (before : head+60 < start) :
    ShrinkHeaderReads.Header i X T start L ((S.steps+1)*t) (after p.input.post (eventLog p.absolute)) := by
  have hr := ShrinkInput.range_bounds X start
  have leRank : start ≤ ShrinkInput.rankBase X start := hr.1.trans hr.2.1
  have leGather : ShrinkInput.rankBase X start ≤ (Z).gathered := by
    change ShrinkInput.rankBase X start ≤ ((ShrinkInput.rankBase X start+2*(Z).A)+2*(Z).B)+(Z).rectangleSize
    omega
  exact header.keep_below before fun x hx =>
    (p.absoluteRun.frame _ (.inl (hx.trans_le (leRank.trans leGather)))).trans (p.input.below _ hx)

theorem live (active : t < blocks) (j : Stage) : ordinal B i t j < directoryRows L := by
  have h := PublishedHeads.windowLive B base positions blocks t W active (localIndex B i j)
  rw [(W).ordinal_index] at h
  have before : (W).before.length = (BlockIndex.earlier B i).length+20 := by
    change (BlockIndex.earlier B i ++ prior B i).length = _
    rw [List.length_append,prior_length]
  change (A).initial.length+t*(A).block.length+((W).before.length+(localIndex B i j).val) < directoryRows L at h
  rw [before] at h
  unfold ordinal
  omega

theorem packet_views (m : Memory w) (gs ts : List (Report w)) :
    let ps := packetList B i X T start s fuel m gs ts
    ps.map (fun p => p.stage.phase) = (W).indices ∧
    ps.flatMap SourceWalk.Packet.reports = gs++ts ∧
    ps.flatMap (fun p => p.stage.choices) =
      List.replicate N [] ++ List.ofFn (ShrinkTermSelection.tapes B.shrink X s w) := by
  intro ps
  have phase : ps.map (fun p => p.stage.phase) = [index B i .gather,index B i .select] := rfl
  refine ⟨phase.trans ?_,?_,?_⟩
  · change _ = List.ofFn (fun j : Fin 2 => (W).index j)
    simp only [List.ofFn_succ,List.ofFn_zero]
    rfl
  · change gs++(ts++[]) = _
    rw [List.append_nil]
  · change List.replicate (ShrinkTermSelection.bundles X*ShrinkTermSelection.ranks (a i)) [] ++
      (List.ofFn (ShrinkTermSelection.tapes B.shrink X s w) ++ []) = _
    rw [List.append_nil]
    exact congrArg (fun n => List.replicate n [] ++ List.ofFn (ShrinkTermSelection.tapes B.shrink X s w))
      (ShrinkTermSelection.motifCount_eq X).symm

/-- The common third zero-based part in the twelve-group calendar. -/
abbrev partWindow : Window A (termVisits B i (BlockProgram.arena B i.val 0)) := BlockGroups.shrink B i 3

theorem part_before : (partWindow B i).before.length = (BlockIndex.earlier B i).length+20 := by
  rw [partWindow,BlockGroups.shrink_offset]
  change _ + ([BlockHeaderPlan.substep (BlockProgram.geometry B) i.val (.shrink (a i) (b i)),
    GreedyLevelPlan.visits (BlockProgram.geometry B) i.val (a i) (BlockProgram.arena B i.val 0),
    ShrinkBundlePlan.visits (BlockProgram.geometry B) i.val (a i) (BlockProgram.arena B i.val 0)] : List _).flatten.length = _
  simp only [List.flatten_cons,List.flatten_nil,List.length_append,List.length_nil,BlockHeaderPlan.substep_length,
    GreedyLevelPlan.visits_length,ShrinkBundlePlan.visits_length]

theorem part_indices : (W).indices = (partWindow B i).indices := by
  unfold Window.indices
  apply congrArg List.ofFn
  funext j
  apply Fin.ext
  rw [(W).index_val,(partWindow B i).index_val,part_before]
  change _ + (BlockIndex.earlier B i ++ prior B i).length + j.val = _
  rw [List.length_append,prior_length]

/-- The third zero-based group of the fixed shrinking substep. Its input
memory is the actual post-memory of the ranked absolute-ID scatter. -/
theorem branch_group (cap : ℕ) (raw : Memory w) (p : ShrinkBranch.Prefix X T start fuel raw)
    (selected : ShrinkBranch.Selected B X T start (10 : Word w) (B.shrink.selectorBits : Word w) fuel raw p s)
    (gatherClock : ShrinkDemandGather.cost < fuel) (space : ShrinkInput.termEnd X start 10 < 2^w)
    (header : ShrinkHeaderReads.Header i X T start L ((S.steps+1)*t) raw)
    (headerBefore : head+60 < start) (active : t < blocks) (clock : SourceOnline.scanCap A fuel ≤ cap) :
    let m := after p.input.post (eventLog p.absolute)
    let ps := packetList B i X T start s fuel m p.gather selected.terms
    SourceOnline.Group A L base cap ((A).initial.length+t*(A).block.length+(BlockIndex.earlier B i).length+20)
      (directoryRows L) m ps ∧ ps.map (fun q => q.stage.phase) = (partWindow B i).indices ∧
    ps.flatMap SourceWalk.Packet.reports = p.gather++selected.terms ∧
    ps.flatMap (fun q => q.stage.choices) =
      List.replicate N [] ++ List.ofFn (ShrinkTermSelection.tapes B.shrink X s w) := by
  intro m ps
  have hhead := afterAbsolute B i X T start fuel base positions blocks t p header headerBefore
  have ten : 10 < 2^w := by have h := header.room; omega
  have hten : (10 : Word w).val = 10 := Nat.mod_eq_of_lt ten
  have terms := selected.termRun
  rw [hten] at terms
  have clocks (j : Stage) := SourceOnline.scanCap_clocks (p := packet B i X T start s fuel j m []) fuel le_rfl clock
  have group := certify B i X T start s fuel L base t (directoryRows L) cap m p.gather selected.terms p.gatherRun
    terms gatherClock space hhead headerBefore rfl rfl rfl (live B i base positions blocks t active .select)
    (fun j => (clocks j).1) (fun j => (clocks j).2)
  have first : ordinal B i t .gather =
      (A).initial.length+t*(A).block.length+(BlockIndex.earlier B i).length+20 := by
    unfold ordinal; rw [show (localIndex B i .gather).val = 0 from rfl,Nat.add_zero]
  rw [first] at group
  have views := packet_views B i X T start s fuel m p.gather selected.terms
  exact ⟨group,views.1.trans (part_indices B i),views.2⟩

end CompressorRecords.ShrinkTermOnline

end

end VPVNP
end Computability
end OAI
