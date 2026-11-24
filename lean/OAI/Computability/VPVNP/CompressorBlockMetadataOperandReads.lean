import OAI.Computability.VPVNP.CompressorPublishedHeadWindows
import OAI.Computability.VPVNP.CompressorShrinkABSliceOperands
import OAI.Computability.VPVNP.CompressorGreedyPlannerFootprint

/-! # Planner reads for the three DFS metadata rows

The two successor-header writes use the runtime pitch. The current-header
publisher reads the input length at offset 29 of level zero and derives the
substep-specific placement and child-directory heads from the active header.
-/

namespace OAI
namespace Computability
namespace VPVNP

noncomputable section

namespace CompressorRecords.BlockMetadata

open BurstRAM Compression BlockPlanner DescriptorSpace PhaseRecipe LevelFields Schedule
open scoped Fin.CommRing
open private first atLevel from OAI.Computability.VPVNP.CompressorHeaderOperands

variable {w : ℕ} {k : Type*} [_root_.Field k] {S : BlockSchedule k} (B : S.Templates)
variable (base : Word w) (positions blocks t : ℕ)
local notation "A" => BlockProgram.script B
local notation "L" => BlockProgram.layout B base.val positions blocks
local notation "pt" => Workspace.ports (arity (Script.catalog A)) base
local notation "pub" => Schedule.Ports.data pt
local notation "firstLevel" => Script.levelsPerBlock A * t
local notation "st" => (levelStart L firstLevel : Word w)
local notation "D" => Window.operandRegion A L base
local notation "F" => BlockProgram.geometry B

private theorem scalar_reads (step : ℕ) (m : Memory w) (ht : t < blocks) (hs : step ≤ S.steps)
    (fit : endAddress L < 2^w) (pitch : m ((pt).directory-1).val = (levelWords L : Word w))
    (n : ℕ) (hn : n < 66) : (scalar step n).ReadsFrom D pub st m := by
  have room := PublishedHeads.level_room B base positions blocks t step ht hs fit
  have entry : Entry L firstLevel pub st m := ⟨rfl,pitch⟩
  have inside : levelStart L 0 ≤ levelStart L (firstLevel+step)+n :=
    (levelStart_mono L (Nat.zero_le _)).trans (Nat.le_add_right ..)
  exact GreedyVisit.scalar_support D L firstLevel step n entry (.inr (.inl rfl))
    (.inr (.inr inside)) ((Nat.add_lt_add_left hn _).trans_le room)

private theorem length_reads (m : Memory w) (ht : t < blocks) (fit : endAddress L < 2^w)
    (rows : m (pt).rows.val = (directoryRows L : Word w)) : lengthWord.ReadsFrom D pub st m := by
  have hf : BlockHeaderPlan.firstHeader.eval pub st m = (levelStart L 0 : Word w) :=
    BlockHeaderPlan.firstHeader_eval L base m st (Fin.ofNat_val_eq_self base).symm rows
  have room := PublishedHeads.level_room B base positions blocks 0 0 (by omega) (Nat.zero_le _) fit
  simp only [Nat.mul_zero,Nat.add_zero] at room
  refine ⟨⟨first D pub st m (.inl rfl),trivial⟩,?_⟩
  change D (BlockHeaderPlan.firstHeader.eval pub st m + (29 : Word w)).val
  rw [hf,← show ((levelStart L 0 + 29 : ℕ) : Word w) = (levelStart L 0 : Word w)+29 by simp,
    Fin.val_natCast,Nat.mod_eq_of_lt (by omega : levelStart L 0+29 < 2^w)]
  exact .inr (.inr (Nat.le_add_right ..))

private theorem visits_supported (step : ℕ) (m : Memory w) (v : Fields) (role : Role)
    (field : ∀ n < 66, (scalar step n).ReadsFrom D pub st m)
    (length : lengthWord.ReadsFrom D pub st m)
    (newSites : v.newSites.ReadsFrom D pub st m) (owner : v.owner.ReadsFrom D pub st m)
    (count : v.count.ReadsFrom D pub st m) (row : v.row.ReadsFrom D pub st m)
    (cap : v.cap.ReadsFrom D pub st m) (j : Visit)
    (hj : j ∈ visits F step B.recordLimit (slotDegree S) role v) :
    HeaderOperands.Supported D pub st m j := by
  have addr (k n : ℕ) : (address k n).ReadsFrom D pub st m :=
    ⟨atLevel D pub st m (.inr (.inl rfl)) k,trivial⟩
  have sites : (LevelFields.sites step).ReadsFrom D pub st m := ⟨field 0 (by decide),field 2 (by decide)⟩
  rcases List.mem_cons.mp hj with rfl | h
  · refine ⟨trivial,trivial,?_⟩
    intro p
    change Fin 13 at p
    cases p using Fin.cases with
    | zero => exact addr step 15
    | succ p =>
      change (fieldExprs F step B.recordLimit (slotDegree S) v p).ReadsFrom D pub st m
      fin_cases p
      exacts [trivial,field 1 (by decide),length,⟨⟨trivial,length⟩,trivial⟩,field 58 (by decide),
        field 59 (by decide),sites,newSites,owner,count,row,cap]
  rcases List.mem_cons.mp h with rfl | h
  · refine ⟨trivial,trivial,?_⟩
    intro p; change Fin 2 at p; fin_cases p
    · exact addr _ _
    · exact ⟨field 14 (by decide),trivial,sites⟩
  obtain rfl := List.mem_singleton.mp h
  refine ⟨trivial,trivial,?_⟩
  intro p; change Fin 2 at p; fin_cases p
  · exact addr _ _
  · trivial

/-- The shrink metadata visits in their installed substep window. -/
theorem shrink_operand_reads (i : Fin S.steps) (m : Memory w) (ht : t < blocks) (fit : endAddress L < 2^w)
    (rows : m (pt).rows.val = (directoryRows L : Word w)) (pitch : m ((pt).directory-1).val = (levelWords L : Word w))
    (v : Visit) (hv : v ∈ (BlockGroups.parts B i)[9]'(by rw [BlockGroups.parts_length]; decide)) : HeaderOperands.Supported D pub st m v := by
  let origin := BlockProgram.arena B i.val 0
  let I := ShrinkBlockInputs.selectedInputs B F i origin
  let fields := Fields.shrink (ShrinkBlockInputs.a i) I
  let reads := Expr.ReadsFrom D pub st m
  have field := scalar_reads B base positions blocks t i.val m ht i.isLt.le fit pitch
  have src : reads origin := field 60 (by decide)
  have ab := BlockSlices.ab_supported i D pub st m origin origin
    (fun j => field j.val (by have := j.isLt; omega)) src src
  have num : reads I.motifs := ⟨ab.rows,trivial⟩
  have term : reads I.termBase := ⟨⟨ab.newWidths,trivial,num⟩,trivial,num⟩
  have sites : reads I.oldSites := ⟨field 0 (by decide),field 2 (by decide)⟩
  have slots : reads I.oldSlots := ⟨sites,field 1 (by decide)⟩
  have newSites : reads I.newSites := ⟨field 0 (by decide),trivial,field 3 (by decide)⟩
  have place : reads (SelectedPlan.placementBase I) := ⟨⟨term,num,trivial⟩,trivial⟩
  have count : reads (SelectedPlan.roleEnd I) := ⟨⟨place,trivial,sites⟩,trivial,slots⟩
  exact visits_supported B base positions blocks t i.val m fields .shrink field
    (length_reads B base positions blocks t m ht fit rows)
    newSites ⟨place,trivial,sites⟩ count ⟨count,newSites⟩ trivial v hv

/-- The refresh metadata visits in their installed substep window. -/
theorem refresh_operand_reads (m : Memory w) (ht : t < blocks) (fit : endAddress L < 2^w)
    (rows : m (pt).rows.val = (directoryRows L : Word w)) (pitch : m ((pt).directory-1).val = (levelWords L : Word w))
    (v : Visit) (hv : v ∈ (BlockGroups.refreshParts B)[4]'(by rw [BlockGroups.refreshParts_length]; decide)) : HeaderOperands.Supported D pub st m v := by
  have field := scalar_reads B base positions blocks t S.steps m ht le_rfl fit pitch
  let head := BlockProgram.arena B S.steps 4
  have owner : head.ReadsFrom D pub st m := field 64 (by decide)
  have sites : (LevelFields.sites S.steps).ReadsFrom D pub st m := ⟨field 0 (by decide),field 2 (by decide)⟩
  exact visits_supported B base positions blocks t S.steps m (.refresh S.steps head) .refresh field
    (length_reads B base positions blocks t m ht fit rows)
    sites owner ⟨owner,sites⟩ ⟨⟨owner,sites⟩,sites⟩ trivial v hv

end CompressorRecords.BlockMetadata

end

end VPVNP
end Computability
end OAI
