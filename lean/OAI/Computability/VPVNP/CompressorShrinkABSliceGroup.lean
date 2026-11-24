import OAI.Computability.VPVNP.CompressorShrinkABTraceReplay
import OAI.Computability.VPVNP.CompressorShrinkABSlicePackets
import OAI.Computability.VPVNP.CompressorBlockCapacity
import OAI.Computability.VPVNP.CompressorScheduledSliceRates

/-!
# Complete AB packet group of the selected shrinking branch

The first scratch table holds the physical sorted widths and their starts.
The second table holds every AB interval record. The allocated block's end
bound suffices for both. The group uses the real shrinking numberings and
retains its exact external frame and resource bounds at its packet endpoint.
-/

namespace OAI
namespace Computability
namespace VPVNP

noncomputable section

namespace CompressorRecords.BlockSlices

open BurstRAM PhaseRecipe BlockPlanner Compression ShrinkBlockInputs DescriptorSpace
open ShrinkSliceArrays Schedule
open scoped Classical Fin.CommRing

variable {k : Type*} [_root_.Field k] {S : BlockSchedule k} (B : S.Templates) (i : Fin S.steps)
variable {g w : ℕ} (X : State (a i) (packingLaneBits (a i) g))
variable (base : Word w) (pos blocks round : ℕ)
local notation "scr" => BlockProgram.script B
local notation "F" => BlockProgram.geometry B
local notation "O" => BlockProgram.arena B i.val 0
local notation "AB" => BlockProgram.arena B i.val 1
local notation "L" => BlockProgram.layout B base.val pos blocks
local notation "pt" => Workspace.ports (arity (Script.catalog (BlockProgram.script B))) base
local notation "pub" => Ports.data pt
local notation "blockStart" => (S.steps+1)*round
local notation "cur" => blockStart+i.val
local notation "s" => ((levelStart L blockStart : ℕ) : Word w)
local notation "origin" => tableBase L cur (0 : Fin 6)
local notation "first" => tableBase L cur (1 : Fin 6)
local notation "W" => abWindow B i
local notation "Z" => ShrinkInput.plan X origin
local notation "T" => packedIncidence L w cur (DemandRAM.oldCount X)
local notation "t" => ShrinkInput.thickBank X T origin
local notation "u" => ShrinkInput.cdBank X T origin
local notation "p" => ShrinkInput.piecesBank X T origin
local notation "ns" => ShrinkBundlePlan.thickCount (a i)
local notation "nt" => ShrinkBundlePlan.cap (a i)
local notation "sites" => Shrink.packedIndex (a := a i) (g := g) X.baseIndex

set_option maxHeartbeats 1200000 in
/-- The source data come from the chosen geometry's current memory. Table
sizes, bundle indices and worker clocks are those of the compiled script. -/
private theorem build_packets_trace (m : Memory w) (hblock : round < blocks) (sitesFit : X.positions ≤ pos)
    (fit : endAddress L < 2^w) (widthFit : nt*X.maxWireWidth < 2^w)
    (rows : m (pt).rows.val = (directoryRows L : Word w))
    (pitch : m ((pt).directory-1).val = (levelWords L : Word w))
    (level : ShrinkBundlePlan.Reads X F i.val O pub s m origin T)
    (abHead : m (tableHead L cur (1 : Fin 6)) = (first : Word w))
    (stored : DemandWidths.Stored X.packingData sites X.packingWidth X.shrinkOrder X.shrinkNumber t u p m)
    (cap : ℕ) (clock : SourceOnline.scanCap scr 95 ≤ cap) :
    ∃ ps : List (SourceOnline.Packet scr w),
      ShrinkABSliceRecipe.Describes (abInputs i O AB) pub s m t p (Z).B first ∧
      SourceWalk (ShrinkABSliceRecipe.Source (abInputs i O AB) pub s m (Z).B 95) (ShrinkABSliceRecipe.phases ns nt)
        m (ps.flatMap SourceWalk.Packet.reports) ∧
      SourceOnline.Group scr L base cap ((scr).initial.length+round*(scr).block.length+(W).before.length)
        (directoryRows L) m ps ∧ ps.map (fun v => v.stage.phase)=(W).indices ∧
      (∀ b, IndexedStarts.Stored (ShrinkABSliceTable.bank first ns nt (BundleLists.portIndex sites b).val)
        (thickWidths X.packingData X.shrinkOrder X.packingWidth b) (abWidths X.packingData X.shrinkNumber X.packingWidth b)
        (SourceOnline.post m ps)) ∧
      (∀ x, x < first ∨ first+(Z).B*IndexedStarts.capacity ns nt ≤ x → SourceOnline.post m ps x = m x) ∧
      (ps.flatMap SourceWalk.Packet.reports).length = (Z).B*(ns+nt+2*(ns*nt)) ∧
      RAMBuckets.cost Report.probes (ps.flatMap SourceWalk.Packet.reports) ≤ (Z).B*(2*(ns+nt)+16*(ns*nt)) := by
  have active : cur < (L).levels := by
    change (S.steps+1)*round+i.val < 1+(S.steps+1)*blocks
    have bound := Nat.mul_le_mul_left (S.steps+1) hblock
    rw [Nat.mul_succ] at bound
    have hi := i.isLt
    omega
  let lev : Fin (L).levels := ⟨cur,active⟩
  have rate := (BlockProgram.field_rates B base.val pos blocks).1
  have amount : X.positions*ShrinkLevelSpace.tableFactor S ≤ tableWords L := by
    change _ ≤ pos*(L).shape.slots*(L).shape.fields
    rw [Nat.mul_assoc]; exact Nat.mul_le_mul sitesFit rate
  have bounds := ShrinkLevelSpace.packed_ends S i X origin first 0 0 w
  have room := tableStop_lt L lev (0 : Fin 6) amount fit
  have termRoom : ShrinkInput.termEnd X origin 10 < 2^w := bounds.2.1.trans_lt room
  have fresh : ShrinkInput.stop X origin ≤ first := bounds.1.trans
    ((Nat.add_le_add_left amount origin).trans (tableEnd_le_tableBase L cur (a := (0 : Fin 6)) (b := (1 : Fin 6)) (show (0 : Fin 6) < 1 from by decide)))
  have abRoom : first+(Z).B*IndexedStarts.capacity ns nt < 2^w :=
    bounds.2.2.2.2.1.trans_lt (tableStop_lt L lev (1 : Fin 6) amount fit)
  have headRoom : tableHead L cur (1 : Fin 6) < 2^w := by
    have le : tableHead L cur (1 : Fin 6) < first := by
      change levelStart L cur+54+6+1 < (levelStart L cur+66)+_+_; omega
    exact le.trans (Nat.lt_of_le_of_lt (Nat.le_add_right ..) abRoom)
  let : Nontrivial (Word w) := Fin.nontrivial_iff_two_le.mpr (by
    change levelStart L cur+54+6+1 < 2^w at headRoom; omega)
  have entry : LevelFields.Entry L blockStart pub s m := ⟨rfl,pitch⟩
  have arena : (AB).eval pub s m = (first : Word w) :=
    (LevelFields.eval_table entry i.val (1 : Fin 6) headRoom).trans abHead
  have rankFit : (Z).stop < 2^w := by
    change ShrinkInput.widthBase X origin < _
    change ShrinkInput.widthBase X origin+_+_+_+_ < _ at termRoom; omega
  have hd := ab_describes i X T origin level rankFit arena
  obtain ⟨rs,walk,ready,outside⟩ := ab_run i X T origin m stored level arena termRoom fresh abRoom widthFit 95 le_rfl
  have guarded := ab_guarded i X T origin m stored level arena termRoom fresh abRoom widthFit 95 le_rfl walk
  have counts := ScheduledRates.scheduledABCounts (abInputs i O AB) pub s m walk
  obtain ⟨ps,group,phase,reports⟩ := ab_packets B i base pos blocks round (Z).B _ t p m rs hblock active fit
    rows pitch hd guarded cap clock
  refine ⟨ps,hd,reports ▸ walk,group,phase,?_,?_,?_,?_⟩
  · simpa only [SourceOnline.post,reports] using ready
  · simpa only [SourceOnline.post,reports] using outside
  · rw [reports]; exact counts.1
  · rw [reports]; exact counts.2.1

/-- Build the group, endpoint descriptors, external frame and costs of the
physical AB calendar on the admitted state. -/
theorem build_packets (m : Memory w) (hblock : round < blocks) (sitesFit : X.positions ≤ pos)
    (fit : endAddress L < 2^w) (widthFit : nt*X.maxWireWidth < 2^w)
    (rows : m (pt).rows.val = (directoryRows L : Word w))
    (pitch : m ((pt).directory-1).val = (levelWords L : Word w))
    (level : ShrinkBundlePlan.Reads X F i.val O pub s m origin T)
    (abHead : m (tableHead L cur (1 : Fin 6)) = (first : Word w))
    (stored : DemandWidths.Stored X.packingData sites X.packingWidth X.shrinkOrder X.shrinkNumber t u p m)
    (cap : ℕ) (clock : SourceOnline.scanCap scr 95 ≤ cap) :
    ∃ ps : List (SourceOnline.Packet scr w),
      SourceOnline.Group scr L base cap ((scr).initial.length+round*(scr).block.length+(W).before.length)
        (directoryRows L) m ps ∧ ps.map (fun v => v.stage.phase)=(W).indices ∧
      (∀ b, IndexedStarts.Stored (ShrinkABSliceTable.bank first ns nt (BundleLists.portIndex sites b).val)
        (thickWidths X.packingData X.shrinkOrder X.packingWidth b) (abWidths X.packingData X.shrinkNumber X.packingWidth b)
        (SourceOnline.post m ps)) ∧
      (∀ x, x < first ∨ first+(Z).B*IndexedStarts.capacity ns nt ≤ x → SourceOnline.post m ps x = m x) ∧
      (ps.flatMap SourceWalk.Packet.reports).length = (Z).B*(ns+nt+2*(ns*nt)) ∧
      RAMBuckets.cost Report.probes (ps.flatMap SourceWalk.Packet.reports) ≤ (Z).B*(2*(ns+nt)+16*(ns*nt)) := by

  obtain ⟨ps,_,_,result⟩ := build_packets_trace B i X base pos blocks round m hblock sitesFit fit widthFit rows pitch level abHead stored cap clock
  exact ⟨ps,result⟩

/-- Attach the AB report list already present in an ordered shrinking
construction. Its source clock and saved planner header may differ from
the online clock and header; their eight physical operands coincide. -/
theorem build_packets_of_run (m : Memory w) (hblock : round < blocks) (sitesFit : X.positions ≤ pos)
    (fit : endAddress L < 2^w) (widthFit : nt*X.maxWireWidth < 2^w)
    (rows : m (pt).rows.val = (directoryRows L : Word w))
    (pitch : m ((pt).directory-1).val = (levelWords L : Word w))
    (level : ShrinkBundlePlan.Reads X F i.val O pub s m origin T)
    (abHead : m (tableHead L cur (1 : Fin 6)) = (first : Word w))
    (stored : DemandWidths.Stored X.packingData sites X.packingWidth X.shrinkOrder X.shrinkNumber t u p m)
    (ref : Memory w) (nativeCap : ℕ) (rs : List (Report w))
    (heads : ShrinkABSliceRecipe.Describes (abInputs i O AB) pub s ref t p (Z).B first)
    (trace : SourceWalk (ShrinkABSliceRecipe.Source (abInputs i O AB) pub s ref (Z).B nativeCap)
      (ShrinkABSliceRecipe.phases ns nt) m rs)
    (cap : ℕ) (clock : SourceOnline.scanCap scr 95 ≤ cap) :
    ∃ ps : List (SourceOnline.Packet scr w),
      ps.flatMap SourceWalk.Packet.reports = rs ∧
      SourceOnline.Group scr L base cap ((scr).initial.length+round*(scr).block.length+(W).before.length)
        (directoryRows L) m ps ∧ ps.map (fun v => v.stage.phase)=(W).indices ∧
      (∀ b, IndexedStarts.Stored (ShrinkABSliceTable.bank first ns nt (BundleLists.portIndex sites b).val)
        (thickWidths X.packingData X.shrinkOrder X.packingWidth b) (abWidths X.packingData X.shrinkNumber X.packingWidth b)
        (SourceOnline.post m ps)) ∧
      (∀ x, x < first ∨ first+(Z).B*IndexedStarts.capacity ns nt ≤ x → SourceOnline.post m ps x = m x) ∧
      (ps.flatMap SourceWalk.Packet.reports).length = (Z).B*(ns+nt+2*(ns*nt)) ∧
      RAMBuckets.cost Report.probes (ps.flatMap SourceWalk.Packet.reports) ≤ (Z).B*(2*(ns+nt)+16*(ns*nt)) := by

  obtain ⟨ps,localHeads,localWalk,result⟩ := build_packets_trace B i X base pos blocks round m hblock sitesFit fit widthFit rows pitch level abHead stored cap clock
  exact ⟨ps,(ShrinkABSliceRecipe.walk_unique (abInputs i O AB) heads localHeads trace localWalk).symm,result⟩

end CompressorRecords.BlockSlices

end

end VPVNP
end Computability
end OAI
