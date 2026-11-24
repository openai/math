import OAI.Computability.VPVNP.CompressorShrinkScheduledOutput
import OAI.Computability.VPVNP.CompressorShrinkScheduledCharges

/-! # Source traffic of the four post-selection shrinking windows

The directory, AB, surviving-role and ordered-slot packets all use empty
choice tapes. Their combined call count depends only on the incoming shape
and fixed degrees. The cost includes copying the six actual incidence columns
into the next level.
-/

namespace OAI
namespace Computability
namespace VPVNP

noncomputable section

namespace CompressorRecords.ScheduledShrink

open BurstRAM Compression ShrinkBlockInputs BlockPlanner DescriptorSpace SourceOnline
open SlotLevel ShrinkSlots ShrinkSlotPlan.Scheduled ShrinkOutput ShrinkScheduledCharges
open scoped Classical Fin.CommRing
open private positions_eq from OAI.Computability.VPVNP.CompressorShrinkLevelSpace

/-- Calls plus external probes per incoming position for Parts 5–8. -/
def outputRate (a b : ℕ) := 102*(2^a+1)+ShrinkScheduledCharges.rate a b

variable {k : Type*} [_root_.Field k] {S : BlockSchedule k} {B : S.Templates} {i : Fin S.steps}
variable {g w : ℕ} {X : State (a i) (packingLaneBits (a i) g)}
local notation "sh" => levelShape (b := b i) X

/-- Native worker count including the resident publications and the three
base-port and three actual-port transfers. -/
def outputCalls (i : Fin S.steps) {g : ℕ} (X : State (a i) (packingLaneBits (a i) g)) :=
  let s := levelShape (b := b i) X
  let q := ShrinkBundlePlan.cap (a i)
  let t := ShrinkBundlePlan.thickCount (a i)
  (ShrinkResidentLayout.layout X 0).calls + ShrinkTermSelection.bundles X*(t+q+2*(t*q)) +
    motifCount X*ShrinkLevelSpace.subdivisionSum (a i) (b i) +
    (constructionOrder.map (Stage.limit s)).sum + (3*baseArcs s+3*actualCount s)

variable {sel : SelectedScore.Selection B X} {base : Word w} {positions blocks round cap : ℕ}
variable {input : Memory w}
local notation "A" => BlockProgram.script B
local notation "L" => BlockProgram.layout B base.val positions blocks
local notation "old" => Script.levelsPerBlock A * round + i.val
local notation "tab" => (fun j : Fin 6 => tableBase L old j)
local notation "term" => ShrinkInput.termHead (w := w) X (tab (0 : Fin 6))
local notation "ids" => ShrinkResidentPackets.absoluteWord (w := w) X (tab (0 : Fin 6))
local notation "dst" => packedIncidence L w (old+1) (actualCount sh)
local notation "Y" => X.shrinkNext B.shrink (S.shrink i) sel
local notation "src" => directory sh (heads sh (SelectedArena.roleBase X term (10 : Word w)) (tab (3 : Fin 6))) w
variable {ps₅ ps₆ ps₇ ps₈ : List (SourceOnline.Packet (BlockProgram.script B) w)} {r : TablesRun w}
local notation "allPackets" => (((ps₅++ps₆)++ps₇)++ps₈)
local notation "cp" => CopyIncidence.reports Y src dst CopyIncidence.allColumns
  (after r.remainder.postWidths (eventLog r.remainder.slots.all))

private theorem Output.account (out : Output (S := S) (w := w) (g := g) B i X sel base positions blocks round cap input ps₅ ps₆ ps₇ ps₈ r) :
    Accounted B i X (S.shrink i) sel term 10 (tab 0) (tab 2) (tab 3) dst r :=
  accounted B i X (S.shrink i) sel term 10 ids (tab 0) (tab 2) (tab 3) dst r out.tables

private theorem Output.reports (out : Output (S := S) (w := w) (g := g) B i X sel base positions blocks round cap input ps₅ ps₆ ps₇ ps₈ r) :
    (allPackets).flatMap SourceWalk.Packet.reports = ps₅.flatMap SourceWalk.Packet.reports ++ (r.reports ++ cp) := by
  simp only [List.flatMap_append,out.abReports,out.widthReports,out.slotReports,TablesRun.reports,
    Passes.reports,List.append_assoc]

/-- Every source packet of all four windows supplies exactly one empty tape
per native worker invocation. The count is independent of the selected terms. -/
theorem Output.tapes (out : Output (S := S) (w := w) (g := g) B i X sel base positions blocks round cap input ps₅ ps₆ ps₇ ps₈ r) :
    (allPackets).flatMap (fun p => p.stage.choices) = List.replicate (outputCalls i X) [] := by
  have a := out.account
  have resident := out.residents.tapes
  rw [PublishedHeads.chronological_tapes input ps₅ out.residents.group.chronological] at resident
  rw [PublishedHeads.chronological_tapes input allPackets out.group.chronological,out.reports]
  have join (rs qs : List (Report w)) : branchPaths (rs++qs) = branchPaths rs++branchPaths qs := List.map_append
  simp only [TablesRun.reports,Passes.reports,join,resident,a.abTapes,a.widthTapes,a.slotTapes,a.copyTapes]
  obtain ⟨baseCount,actCount⟩ := next_counts X B.shrink (S.shrink i) sel
  have actual : (Y).positions*2^(b i) = actualCount sh := by
    simpa only [State.positions,Fintype.card_prod,Fintype.card_congr (bitWordFinEquiv g),Fintype.card_fin] using actCount
  rw [baseCount,actual]
  simp only [← List.replicate_add]
  apply congrArg (fun n => List.replicate n ([] : List Bool))
  unfold outputCalls
  simp only [Nat.add_assoc]
  rfl

/-- Calls plus probes of the original reports, with both resident and slot
publications charged to the current position count. -/
theorem Output.charge (out : Output (S := S) (w := w) (g := g) B i X sel base positions blocks round cap input ps₅ ps₆ ps₇ ps₈ r) :
    RAMBuckets.cost Report.probes ((allPackets).flatMap SourceWalk.Packet.reports) ≤
      X.positions*outputRate (a i) (b i) := by
  have h := (ShrinkResidentLayout.cost_units X (tab (5 : Fin 6))).1
  change _ ≤ 102*(ShrinkPreimages.oldCount X*(2^(a i)+1)) at h
  rw [show ShrinkPreimages.oldCount X = X.positions from positions_eq X] at h
  rw [out.reports,RAMBuckets.cost_append,out.residents.cost]
  calc
    _ ≤ 102*(X.positions*(2^(a i)+1))+X.positions*ShrinkScheduledCharges.rate (a i) (b i) :=
      Nat.add_le_add h out.account.linear
    _ = _ := by unfold outputRate; ring

end CompressorRecords.ScheduledShrink

end

end VPVNP
end Computability
end OAI
