import OAI.Computability.VPVNP.CompressorSlotPostAccess
import OAI.Computability.VPVNP.CompressorSlotCopyLayout

/-!
# Eventwise memory bounds for the full selected shrinking slot program

The 22-stage source walk records each chronological worker execution together
with every actual external address it read or wrote. The final six scans copy
the resulting graph into the canonical descriptor directory of the next level.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.ShrinkSlotPlan.Scheduled

open Compression Compression.State Compression.PackingData Compression.ShrinkMotif Compression.ShrinkEnergy
open MotifBlocks MotifGrid MotifConversion Slots SlotLevel ShrinkSlots BurstRAM

variable {a b g w : ℕ} {δ factor : ℝ} {k : Type*} [_root_.Field k]
variable (X : State a (packingLaneBits a g))
variable (B : FixedBlock k demandSource demandTarget supply (realWidths demandMass) (realWidths supplyMass) (31/16) factor)
variable (ready : Ready (2^a) (2*2^a+1) (2^b) δ) (sel : X.ShrinkSelection B)

/-- An address writable by the selected slot schedule, either in its construction workspace or
in the six-column packed incidence destination. -/
def writeData (s : SlotLevel.Shape) (h : Heads) (start x : ℕ) :=
  Build.writeRegion s h x ∨ start ≤ x ∧ x < start+6*actualCount s

set_option maxHeartbeats 1000000 in
/-- A fully bounded source execution of all 22 planner rows, with the exact
selected state's incidence directory in the destination after the last copy. -/
theorem selected_sources (P : Plan) (h : Heads) (splitHead : ℕ) (m : Memory w)
    (r : Build.Construction w) (L : DescriptorSpace.Layout) (level : Fin L.levels) :
    let s := levelShape (b := b) X
    let side := selectedLayout X B sel
    let Y := X.shrinkNext B ready sel
    let T := directory s h w
    let U := DescriptorSpace.packedIncidence L w level (actualCount s)
    let start := DescriptorSpace.incidenceStart L level
    let built := after m (eventLog r.all)
    let copies := CopyIncidence.reports Y T U CopyIncidence.allColumns built
    Build.Space s h splitHead w → DemandRAM.RoleColumns X side h.oldArc m →
    r.Native s h splitHead side m → T.Represents Y (r.final m) →
    DescriptorSpace.endAddress L < 2^w → actualCount s ≤ DescriptorSpace.slotCapacity L →
    (finish s h ≤ start ∨ start+6*actualCount s ≤ targetsHead s h) →
      SourceWalk (fun j mem rs ↦ Source P s h side splitHead U j mem rs ∧
        LogAccess (Build.readRegion s h splitHead) (writeData s h start) rs) order m (r.all++copies) ∧
      U.Represents Y (after m (eventLog (r.all++copies))) := by
  intro s side Y T U start built copies sp roles native rep room capacity apart
  obtain ⟨core,out,_⟩ := Build.post_access X B ready sel h splitHead m r sp roles native
  have counts := next_counts X B ready sel
  change Fintype.card Y.Base*2^b=baseArcs s ∧ Fintype.card Y.Base*2^g*2^b=actualCount s at counts
  have h0 := sp.old
  have h1 := sp.roles
  have h2 := sp.next
  have h3 := sp.subdiv
  have hs : h.scratch ≤ rowsHead s h := by unfold rowsHead; omega
  have hr : rowsHead s h ≤ targetsHead s h := by unfold targetsHead inverseHead; omega
  have ht : targetsHead s h ≤ finish s h := by
    unfold finish widthHead inHead outHead inverseBaseHead stopAddress shiftsHead; omega
  let rd := Build.readRegion s h splitHead
  let wr := writeData s h start
  have lower := min_le_left h.oldArc splitHead
  have core' : LogAccess rd wr r.passes.slots.all := LogAccess.mono core (fun _ ↦ id) (fun _ ↦ Or.inl)
  have out' : LogAccess rd wr (r.passes.mates.all++r.passes.widths) := LogAccess.mono out (fun _ ↦ id) (fun _ ↦ Or.inl)
  have srcBound := CopyIncidence.shrink_column_bounds Y s h counts.1 counts.2 sp.fit
  have dstBound := CopyIncidence.packed_column_bounds Y s L level counts.2 room capacity
  have endFit : start+6*actualCount s < 2^w := DescriptorSpace.packed_incidence_room L room level capacity
  have lengths (c : Fin 6) : CopyIncidence.rows Y c = (Stage.copy c).limit s :=
    CopyIncidence.shrink_rows Y s counts.1 counts.2 c
  have pre : ∀ x, h.role ≤ x → x < rowsHead s h → wr x := fun x hx hy ↦
    Or.inl (by change h.role ≤ x ∧ x < finish s h; omega)
  have src (x) (cell : CopyIncidence.ColumnCell Y T x) : rd x := by
    obtain ⟨c,hc⟩ := cell
    change (T.column c).val ≤ x ∧ x < (T.column c).val + CopyIncidence.rows Y c at hc
    have hs : targetsHead s h ≤ (T.column c).val ∧ (T.column c).val + CopyIncidence.rows Y c ≤ finish s h := srcBound c
    change min h.oldArc splitHead ≤ x ∧ x < finish s h; omega
  have dst (x) (cell : CopyIncidence.ColumnCell Y U x) : wr x := by
    obtain ⟨c,hc⟩ := cell
    have hd : (U.column c).val=start+c.val*actualCount s ∧
        (U.column c).val+CopyIncidence.rows Y c ≤ start+6*actualCount s := dstBound c
    exact Or.inr (by omega)
  have regs := CopyIncidence.Regions.shrink_to_level Y s h L level counts.1 counts.2 sp.fit room capacity apart
  have repBuilt : T.Represents Y built := by simpa only [built, ← r.final_eq m] using rep
  have copied := (CopyIncidence.copy_directory Y T U built regs repBuilt).2.1
  refine ⟨sources_with_footprints P s h side splitHead U Y r m native lengths h1 h2 h3
    ((by omega : rowsHead s h ≤ finish s h).trans_lt sp.fit) (fun c ↦ (srcBound c).2.trans sp.fit.le)
    (fun c ↦ (dstBound c).2.trans endFit.le) rd wr pre src dst core' out',?_⟩
  simpa only [eventLog,List.flatMap_append,after,List.foldl_append,built,copies] using copied

end CompressorRecords.ShrinkSlotPlan.Scheduled

end VPVNP
end Computability
end OAI
