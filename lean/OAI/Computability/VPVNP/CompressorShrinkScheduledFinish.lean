import OAI.Computability.VPVNP.CompressorShrinkScheduledOutput
import OAI.Computability.VPVNP.CompressorShrinkScheduledTail

/-! # The output graph and final history records of a scheduled shrinking step

The selected geometry feeds the resident-directory builders, interval scans and
canonical slot copies. The three final publications then run in the memory
produced by those copies. Their endpoint is the exact last visit of the
shrinking substep, including all static rectangle subdivisions.
-/

namespace OAI
namespace Computability
namespace VPVNP

noncomputable section

namespace CompressorRecords.ShrinkScheduledFinish

open BurstRAM Compression BlockPlanner DescriptorSpace SourceOnline
open ShrinkBlockInputs ShrinkOutput
open scoped Fin.CommRing

variable {k : Type*} [_root_.Field k] {S : BlockSchedule k} (B : S.Templates) (i : Fin S.steps)
variable {w g : ℕ} (X : State (a i) (packingLaneBits (a i) g)) (sel : SelectedScore.Selection B X)
variable (base : Word w) (positions blocks round cap : ℕ)
local notation "prog" => BlockProgram.script B
local notation "space" => BlockProgram.layout B (Fin.val base) positions blocks
local notation "pt" => Workspace.ports (Schedule.arity (Script.catalog prog)) base
local notation "fst" => Script.levelsPerBlock prog * round
local notation "idx" => fst+i.val
local notation "tab₀" => tableBase space idx (0 : Fin 6)
local notation "oldInc" => packedIncidence space w idx (DemandRAM.oldCount X)
local notation "P₀" => SourceOnline.Packet prog w
local notation "ord" => ShrinkForward.first B i round

/-- The four output windows occupy precisely the interval between the end
of selected geometry and the first metadata publication. -/
theorem output_length {m : Memory w} {a₅ a₆ a₇ a₈ : List P₀} {r : TablesRun w}
    (out : ScheduledShrink.Output B i X sel base positions blocks round cap m a₅ a₆ a₇ a₈ r) :
    36 + (((a₅++a₆)++a₇)++a₈).length = ShrinkForward.visitsBefore B i 9 := by
  let parts := BlockGroups.parts B i
  have sizes := congrArg List.length out.indices
  simp only [List.length_map,List.length_append] at sizes
  have first : ShrinkForward.visitsBefore B i 5 = 36 := by
    change ((BlockGroups.parts B i).take 5).flatten.length = 36
    rw [show ((BlockGroups.parts B i).take 5).flatten = ShrinkBlockInputs.beforeSlices B
      (BlockProgram.geometry B) i (BlockProgram.arena B i.val 0) by
        simp only [BlockGroups.parts,ShrinkBlockInputs.beforeSlices,List.take_succ_cons,
          List.take_zero,List.flatten_cons,List.flatten_nil,List.append_nil,List.append_assoc]]
    exact ShrinkBlockInputs.beforeSlices_length ..
  have offset (j : ℕ) (live : j < 12) :
      ShrinkForward.visitsBefore B i (j+1) = ShrinkForward.visitsBefore B i j +
        (parts[j]'(by change j < 12; exact live)).length := by
    simp only [ShrinkForward.visitsBefore,List.take_succ_eq_append_getElem
      (show j < (BlockGroups.parts B i).length by change j<12; exact live),List.flatten_append,
      List.flatten_cons,List.flatten_nil,List.append_nil,List.length_append,parts]
  have h₅ : (ShrinkResidentPackets.window B i).indices.length = (parts[5]'(by change 5<12; decide)).length := List.length_ofFn
  have h₆ : (BlockSlices.abWindow B i).indices.length = (parts[6]'(by change 6<12; decide)).length := List.length_ofFn
  have h₇ : (SurvivingPackets.window B i).indices.length = (parts[7]'(by change 7<12; decide)).length := List.length_ofFn
  have h₈ : (BlockGroups.shrink B i 8).indices.length = (parts[8]'(by change 8<12; decide)).length := List.length_ofFn
  rw [h₅,h₆,h₇,h₈] at sizes
  have e₅ := offset 5 (by decide)
  have e₆ := offset 6 (by decide)
  have e₇ := offset 7 (by decide)
  have e₈ := offset 8 (by decide)
  norm_num1 at e₅ e₆ e₇ e₈
  simp only [List.length_append]
  omega

/-- The twenty-one final deterministic calls close the substep. -/
theorem tail_length :
    ShrinkForward.visitsBefore B i 9 + 21 = (BlockProgram.shrink B i).length := by
  rw [← BlockGroups.parts_flatten]
  rw [← List.take_append_drop 9 (BlockGroups.parts B i),List.flatten_append,List.length_append]
  change ShrinkForward.visitsBefore B i 9 + 21 = ShrinkForward.visitsBefore B i 9 + _
  apply congrArg (ShrinkForward.visitsBefore B i 9 + ·)
  change 21 = 3+4+14
  decide

/-- All six output and publication lists retain their actual native executions.
The metadata subgroup is a prefix of the three final publication groups. -/
structure Finish (input : Memory w) (a₅ a₆ a₇ a₈ ms tail : List P₀) (r : TablesRun w) : Prop where
  output : ScheduledShrink.Output B i X sel base positions blocks round cap input a₅ a₆ a₇ a₈ r
  published : ShrinkScheduledTail.Result B base positions blocks round cap i X
    (post input (((a₅++a₆)++a₇)++a₈)) ms tail
  group : Group prog space base cap (ord+36) (directoryRows space) input ((((a₅++a₆)++a₇)++a₈)++tail)
  length : 36 + ((((a₅++a₆)++a₇)++a₈)++tail).length = (BlockProgram.shrink B i).length

theorem join {input : Memory w} {a₅ a₆ a₇ a₈ ms tail : List P₀} {r : TablesRun w}
    (out : ScheduledShrink.Output B i X sel base positions blocks round cap input a₅ a₆ a₇ a₈ r)
    (pubs : ShrinkScheduledTail.Result B base positions blocks round cap i X
      (post input (((a₅++a₆)++a₇)++a₈)) ms tail) :
    Finish B i X sel base positions blocks round cap input a₅ a₆ a₇ a₈ ms tail r := by
  have sizes := output_length B i X sel base positions blocks round cap out
  refine ⟨out,pubs,out.group.append ?_,?_⟩
  · have h := pubs.group
    change Group prog space base cap ((ord+36)+_) _ _ _
    rw [Nat.add_assoc,sizes]; exact h
  · rw [List.length_append,← Nat.add_assoc,sizes,pubs.length,tail_length]

end CompressorRecords.ShrinkScheduledFinish

end

end VPVNP
end Computability
end OAI
