import OAI.Computability.VPVNP.CompressorShrinkSlotBoundary
import OAI.Computability.VPVNP.CompressorShrinkSlotLaunch
import OAI.Computability.VPVNP.CompressorShrinkSlotPacketGroup
import OAI.Computability.VPVNP.CompressorShrinkSlotOperandTransport
import OAI.Computability.VPVNP.CompressorShrinkOutputAccess

/-!
# The selected shrinking slot group in the complete online script

Starting with the score and header words in the source memory, each
actual source visit preserves its planner's inputs. At that visit's
global calendar ordinal the recipe evaluates to its native worker bank,
including in every scheduler memory that agrees on the live data.
-/

namespace OAI
namespace Computability
namespace VPVNP

noncomputable section

namespace CompressorRecords.ShrinkSlotCalendar

open BurstRAM BlockPlanner DescriptorSpace PhaseRecipe SourceTransport Schedule Compression
open ShrinkSlots SlotLevel ShrinkSlotPlan.Scheduled
open scoped Fin.CommRing

variable {k : Type*} [_root_.Field k] {S : BlockSchedule k} (B : S.Templates) (i : Fin S.steps)
variable {g w : ℕ} (X : State (ShrinkBlockInputs.a i) (packingLaneBits (ShrinkBlockInputs.a i) g))
local notation "a₀" => ShrinkBlockInputs.a i
local notation "b₀" => ShrinkBlockInputs.b i
variable (sel : X.ShrinkSelection B.shrink)
variable (term : Word w) (stride role retained slotStart : ℕ)
local notation "s" => levelShape (b := b₀) X
local notation "h" => ShrinkOutput.heads s role slotStart
local notation "end₀" => finish s h
local notation "width" => ShrinkOutput.widthBase X term.val stride role retained
local notation "side" => selectedLayout X B.shrink sel
local notation "A" => BlockProgram.script B
local notation "P" => plan B i
local notation "W" => window B i

variable (L : DescriptorSpace.Layout) (base : Word w) (t : ℕ) (level : Fin L.levels)
local notation "pt" => Workspace.ports (arity (Script.catalog A)) base
local notation "first" => Script.levelsPerBlock A*t
local notation "state" => (levelStart L first : Word w)
local notation "pub" => Schedule.Ports.data pt
local notation "H" => levelStart L 0
local notation "dst" => packedIncidence L w level (actualCount s)
local notation "copyBase" => incidenceStart L level
local notation "pitchCell" => Fin.val (Schedule.Ports.directory pt-1)
local notation "labels" => ShrinkSlotPackets.packetVisit P W s h side width dst

set_option maxHeartbeats 1400000 in
/-- The twenty-two global rows are checked and prepared at their exact
ordinals. Their choices and report memories are those of the physical
construction and its six canonical copies. -/
theorem packet_group {initial raw : Memory w} {r : Build.Construction w}
    (c : ShrinkOutput.Constructed X B.shrink (S.shrink i) sel term stride role retained initial raw r slotStart)
    (sp : Build.Space s h width w) (room : endAddress L < 2^w) (capacity : actualCount s ≤ slotCapacity L)
    (total : raw (pt).rows.val = (directoryRows L : Word w))
    (pitch : raw pitchCell = (levelWords L : Word w))
    (values : ShrinkSlotPackets.Values P (Fintype.card X.Base) (2^g) h side width dst pub state raw)
    (bound : Boundary A L base t i.val role slotStart end₀ copyBase
      ((SelectedPlan.layoutCell (selected B i)).eval pub state raw).val)
    (cap : ℕ) (capFits : SourceOnline.scanCap A 49 ≤ cap) :
    let Y := X.shrinkNext B.shrink (S.shrink i) sel
    let copies := CopyIncidence.reports Y (directory s h w) dst CopyIncidence.allColumns (after raw (eventLog r.all))
    let ordinal := (A).initial.length+t*(A).block.length+(W).before.length
    ∃ ps : List (SourceOnline.Packet A w),
      ps.map SourceWalk.Packet.stage = List.ofFn labels ∧ ps.flatMap SourceWalk.Packet.reports = r.all++copies ∧
      SourceOnline.Group A L base cap ordinal (directoryRows L) raw ps ∧
      (dst).Represents Y (SourceOnline.post raw ps) := by
  intro Y copies ordinal
  let score := ((SelectedPlan.layoutCell (selected B i)).eval pub state raw).val
  let root := RootCell pitchCell (levelStart L (first+i.val)) (levelStart L (first+(i.val+1))) score
  let stable := fun x ↦ root x ∨ x=(pt).rows.val
  have entry : LevelFields.Entry L first pub state raw := ⟨rfl,pitch⟩
  have roots : Roots P root pub state raw := plan_roots B i entry bound.oldFits bound.nextFits
  have apart := bound.slotBefore.trans ((Nat.le_add_right _ 66).trans bound.headerBefore)
  obtain ⟨walk,rep⟩ := c.sources_of_space X B.shrink (S.shrink i) sel term stride role retained slotStart sp P L level
    room capacity (Or.inl apart)
  have startLe : slotStart ≤ end₀ := by
    simp only [finish,widthHead,inHead,outHead,inverseBaseHead,stopAddress,shiftsHead,targetsHead,inverseHead,
      rowsHead,ShrinkOutput.heads]; omega
  have live := (walk.with_invariant (I := fun mem ↦ Agree stable raw mem) (fun _ _ ↦ rfl) (by
    intro j mem logs hs agree x hx
    apply (agree x hx).trans
    symm
    apply after_outside mem hs.2.2
    intro inside
    exact bound.untouched startLe inside hx)).1
  have cert (n : Fin order.length) (mem : Memory w) (logs : List (Report w))
      (hs : Source P s h side width dst order[n.val] mem logs)
      (access : LogAccess (fun x ↦ role≤x ∧ x<end₀)
        (fun x ↦ (slotStart≤x ∧ x<end₀) ∨ copyBase≤x ∧ x<copyBase+6*actualCount s) logs)
      (agree : Agree stable raw mem) :
      (labels n).Runs mem logs ∧ SourceOnline.Checked A L cap ⟨labels n,mem,logs⟩ ∧
        SourceOnline.Prepared A L base (ordinal+n.val) (directoryRows L) ⟨labels n,mem,logs⟩ := by
    have rootAgree : Agree root raw mem := fun x hx ↦ agree x (Or.inl hx)
    have input := values.transport roots rootAgree
    have used := roots.transport rootAgree (rootCell_operandRegion A L base _ _ score bound.scoreHigh)
    have ev := ShrinkSlotPackets.evaluated P W L base t n mem input used
    let pos := (W).position (Fin.cast (List.length_map (f := Stage.visit P) (as := order)).symm n)
    have size : (A).initial.length+t*(A).block.length+pos.val < directoryRows L := by
      have end_ := bound.blockRoom
      rw [Nat.succ_mul] at end_
      have indexBound := pos.isLt
      omega
    have sameOrdinal : ordinal+n.val = (A).initial.length+t*(A).block.length+pos.val := by
      change ((A).initial.length+t*(A).block.length+(W).before.length)+n.val =
        (A).initial.length+t*(A).block.length+((W).before.length+n.val)
      omega
    have count : mem (pt).rows.val = (directoryRows L : Word w) :=
      (agree _ (Or.inr rfl)).symm.trans total
    have strideWord : mem pitchCell = (levelWords L : Word w) :=
      (rootAgree _ (Or.inl rfl)).symm.trans pitch
    have checked : LogAccess (H≤·) (H≤·) logs :=
      LogAccess.mono access (fun _ hx ↦ bound.roleHigh.trans hx.1) (fun _ hx ↦ hx.elim
        (fun h₁ ↦ (bound.roleHigh.trans bound.roleBefore).trans h₁.1)
        (fun h₁ ↦ (((bound.roleHigh.trans bound.roleBefore).trans startLe).trans apart).trans h₁.1))
    refine ⟨(ShrinkSlotPackets.runs P W s h side width dst n mem logs).2 hs,
      ShrinkSlotPackets.checked_source P W s h side width dst n L cap sp capFits mem logs hs checked,?_⟩
    rw [sameOrdinal]
    exact (W).prepared L base bound.arity bound.baseValue bound.fits _ t ⟨labels n,mem,logs⟩ mem
      (fun _ _ ↦ rfl) count strideWord size ev
  obtain ⟨ps,stages,reports,group⟩ := SourceOnline.Group.of_window_walk labels live
    (fun n mem logs hs ↦ cert n mem logs hs.1.1 hs.1.2 hs.2)
  exact ⟨ps,stages,reports,group,by simpa only [SourceOnline.post,reports] using rep⟩

end CompressorRecords.ShrinkSlotCalendar

end

end VPVNP
end Computability
end OAI
