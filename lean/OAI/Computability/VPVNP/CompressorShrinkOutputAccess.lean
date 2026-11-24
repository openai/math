import OAI.Computability.VPVNP.CompressorRecordsShrinkOutputBuild
import OAI.Computability.VPVNP.CompressorSlotSelectedAccess

/-!
# The bounded source walk on the actual shrinking allocation

The selected width sweep precedes the chronological slot workers. Its
constructor supplies the old-arc role words in their physical memory,
so all slot phases and the six canonical copies have explicit access
bounds in the concrete consecutive allocation.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.ShrinkOutput

open Compression Compression.PackingData Compression.ShrinkMotif Compression.ShrinkEnergy
open MotifBlocks MotifGrid MotifConversion Slots SlotLevel ShrinkSlots BurstRAM

variable {a b g w : ℕ} {k : Type*} [_root_.Field k] {factor δ : ℝ}
variable (X : State a (packingLaneBits a g))
variable (F : FixedBlock k demandSource demandTarget Compression.ShrinkMotif.supply
  (realWidths demandMass) (realWidths supplyMass) (31/16) factor)
variable (ready : Ready (2^a) (2*2^a+1) (2^b) δ) (sel : X.ShrinkSelection F)
variable (term : Word w) (stride role retained : ℕ)

local notation "s" => levelShape (b := b) X
local notation "h" => slotHeads (b := b) X term.val stride role retained
local notation "width" => widthBase X term.val stride role retained
local notation "last" => stop (b := b) X term.val stride role retained
local notation "side" => selectedLayout X F sel

/-- Numeric bounds for either a consecutive or separately placed slot workspace. -/
theorem FitsWords.slot_space_at (start : ℕ) (gap : (h).role ≤ start)
    (room : finish s (heads s role start) < 2^w) (hw : FitsWords (b := b) X F term stride role retained) :
    Build.Space s (heads s role start) width w := by
  have old : role+4*absoluteCount X ≤ (h).role :=
    (role_room X term stride role retained).trans (width_le_slots X term stride role retained)
  have splitRoom : width+(oldBaseArcCount (s).bases (s).tags (s).oldDegree (s).colors*(s).lanes)*4*
      (∑ t,(s).subdivisions t) ≤ (h).role := Nat.le_add_right ..
  exact ⟨old.trans gap,splitRoom.trans gap,le_rfl,le_rfl,le_rfl,room,hw.lanes,hw.tags,hw.profile,hw.degree⟩

theorem FitsWords.slot_space (hw : FitsWords (b := b) X F term stride role retained) :
    Build.Space s h width w := hw.slot_space_at X F term stride role retained (h).role le_rfl hw.room

/-- Both ways to look up any genuine or dummy field survive the selected physical slot output. -/
theorem Constructed.retained_tables_at (start : ℕ) (gap : (h).role ≤ start)
    (room : finish s (heads s role start) < 2^w) {initial out : Memory w} {r : Build.Construction w}
    (c : Constructed X F ready sel term stride role retained initial out r start)
    (hw : FitsWords (b := b) X F term stride role retained) :
    Build.OrderedTables X ready side (heads s role start) (r.final out) :=
  Build.retained_tables X F ready sel (heads s role start) width out r (hw.slot_space_at X F term stride role retained start gap room)
    c.inputRoles c.slots

/-- Both ways to look up any genuine or dummy field survive the selected physical slot output. -/
theorem Constructed.retained_tables {initial out : Memory w} {r : Build.Construction w}
    (c : Constructed X F ready sel term stride role retained initial out r)
    (hw : FitsWords (b := b) X F term stride role retained) :
    Build.OrderedTables X ready side h (r.final out) :=
  Build.retained_tables X F ready sel h width out r (hw.slot_space X F term stride role retained)
    c.inputRoles c.slots

/-- Each of the 22 physical stages reads within the current allocation and
writes only in the slot workspace or the next canonical incidence block. -/
theorem Constructed.sources_of_space (slotStart : ℕ) {initial out : Memory w} {r : Build.Construction w}
    (c : Constructed X F ready sel term stride role retained initial out r slotStart)
    (sp : Build.Space s (heads s role slotStart) width w)
    (P : ShrinkSlotPlan.Scheduled.Plan) (L : DescriptorSpace.Layout) (level : Fin L.levels) :
    let h₀ := heads s role slotStart
    let end₀ := finish s h₀
    let Y := X.shrinkNext F ready sel
    let start := DescriptorSpace.incidenceStart L level
    let U := DescriptorSpace.packedIncidence L w level (actualCount s)
    let copies := CopyIncidence.reports Y (directory s h₀ w) U CopyIncidence.allColumns (after out (eventLog r.all))
    DescriptorSpace.endAddress L < 2^w → actualCount s ≤ DescriptorSpace.slotCapacity L →
    (end₀ ≤ start ∨ start+6*actualCount s ≤ targetsHead s h₀) →
      SourceWalk (fun j m rs ↦ ShrinkSlotPlan.Scheduled.Source P s h₀ side width U j m rs ∧
        LogAccess (fun x ↦ role ≤ x ∧ x < end₀)
          (fun x ↦ (slotStart ≤ x ∧ x < end₀) ∨ start ≤ x ∧ x < start+6*actualCount s) rs)
        ShrinkSlotPlan.Scheduled.order out (r.all++copies) ∧ U.Represents Y (after out (eventLog (r.all++copies))) := by
  intro h₀ end₀ Y start U copies room cap apart
  have readHead : min h₀.oldArc width = role := min_eq_left (by
    change role ≤ width
    exact (Nat.le_add_right ..).trans (role_room X term stride role retained))
  have run := ShrinkSlotPlan.Scheduled.selected_sources X F ready sel P h₀ width out r L level
    sp c.inputRoles c.slots c.incidence room cap apart
  have rd : Build.readRegion s h₀ width = fun x ↦ role ≤ x ∧ x < end₀ := by
    funext x; simp only [Build.readRegion,readHead]; rfl
  rw [rd] at run
  exact run

/-- Each of the 22 physical stages reads within the current allocation and
writes only in the slot workspace or the next canonical incidence block. -/
theorem Constructed.sources_at (slotStart : ℕ) (gap : (h).role ≤ slotStart)
    (endFit : finish s (heads s role slotStart) < 2^w) {initial out : Memory w} {r : Build.Construction w}
    (c : Constructed X F ready sel term stride role retained initial out r slotStart)
    (hw : FitsWords (b := b) X F term stride role retained)
    (P : ShrinkSlotPlan.Scheduled.Plan) (L : DescriptorSpace.Layout) (level : Fin L.levels) :
    let h₀ := heads s role slotStart
    let end₀ := finish s h₀
    let Y := X.shrinkNext F ready sel
    let start := DescriptorSpace.incidenceStart L level
    let U := DescriptorSpace.packedIncidence L w level (actualCount s)
    let copies := CopyIncidence.reports Y (directory s h₀ w) U CopyIncidence.allColumns (after out (eventLog r.all))
    DescriptorSpace.endAddress L < 2^w → actualCount s ≤ DescriptorSpace.slotCapacity L →
    (end₀ ≤ start ∨ start+6*actualCount s ≤ targetsHead s h₀) →
      SourceWalk (fun j m rs ↦ ShrinkSlotPlan.Scheduled.Source P s h₀ side width U j m rs ∧
        LogAccess (fun x ↦ role ≤ x ∧ x < end₀)
          (fun x ↦ (slotStart ≤ x ∧ x < end₀) ∨ start ≤ x ∧ x < start+6*actualCount s) rs)
        ShrinkSlotPlan.Scheduled.order out (r.all++copies) ∧ U.Represents Y (after out (eventLog (r.all++copies))) :=
  c.sources_of_space X F ready sel term stride role retained slotStart
    (hw.slot_space_at X F term stride role retained slotStart gap endFit) P L level

/-- Each of the 22 physical stages reads within the current allocation and
writes only in the slot workspace or the next canonical incidence block. -/
theorem Constructed.sources {initial out : Memory w} {r : Build.Construction w}
    (c : Constructed X F ready sel term stride role retained initial out r)
    (hw : FitsWords (b := b) X F term stride role retained)
    (P : ShrinkSlotPlan.Scheduled.Plan) (L : DescriptorSpace.Layout) (level : Fin L.levels) :
    let Y := X.shrinkNext F ready sel
    let start := DescriptorSpace.incidenceStart L level
    let U := DescriptorSpace.packedIncidence L w level (actualCount s)
    let copies := CopyIncidence.reports Y (directory s h w) U CopyIncidence.allColumns (after out (eventLog r.all))
    DescriptorSpace.endAddress L < 2^w → actualCount s ≤ DescriptorSpace.slotCapacity L →
    (last ≤ start ∨ start+6*actualCount s ≤ targetsHead s h) →
      SourceWalk (fun j m rs ↦ ShrinkSlotPlan.Scheduled.Source P s h side width U j m rs ∧
        LogAccess (fun x ↦ role ≤ x ∧ x < last)
          (fun x ↦ ((h).role ≤ x ∧ x < last) ∨ start ≤ x ∧ x < start+6*actualCount s) rs)
        ShrinkSlotPlan.Scheduled.order out (r.all++copies) ∧ U.Represents Y (after out (eventLog (r.all++copies))) :=
  c.sources_at X F ready sel term stride role retained (h).role le_rfl hw.room hw P L level

end CompressorRecords.ShrinkOutput

end VPVNP
end Computability
end OAI
