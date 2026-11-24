import OAI.Computability.VPVNP.CompressorShrinkScheduledResidents
import OAI.Computability.VPVNP.CompressorShrinkTablesPhysical
import OAI.Computability.VPVNP.CompressorShrinkABSliceGroup
import OAI.Computability.VPVNP.CompressorShrinkSurvivingPackets
import OAI.Computability.VPVNP.CompressorShrinkSlotPhysicalGroup
import OAI.Computability.VPVNP.CompressorShrinkScheduledRetention

/-! # The four post-selection groups of a physical shrinking substep

On each admitted branch the hidden/map directory visits precede the AB
intervals, the four surviving-role scans and the ordered-slot/copy visits.
The AB and surviving packets use the actual reports of the same three-table
construction. The final memory carries the new canonical incidence directory
and all old-level data read by the backward traversal.
-/

namespace OAI
namespace Computability
namespace VPVNP

noncomputable section

namespace CompressorRecords.ScheduledShrink

open BurstRAM Compression ShrinkBlockInputs DescriptorSpace SourceOnline BlockPlanner ShrinkOutput
open SlotLevel ShrinkSlots ShrinkSliceSweep
open scoped Classical Fin.CommRing

variable {k : Type*} [_root_.Field k] {S : BlockSchedule k} (B : S.Templates) (i : Fin S.steps)
variable {w g : ℕ} (X : State (a i) (packingLaneBits (a i) g)) (sel : SelectedScore.Selection B X)
variable (base : Word w) (positions blocks round : ℕ)
local notation "prog" => BlockProgram.script B
local notation "space" => BlockProgram.layout B base.val positions blocks
local notation "pt" => Workspace.ports (Schedule.arity (Script.catalog prog)) base
local notation "pub" => Schedule.Ports.data pt
local notation "first₀" => Script.levelsPerBlock prog * round
local notation "old₀" => first₀+i.val
local notation "next₀" => old₀+1
local notation "tab" => (fun j : Fin 6 => tableBase space old₀ j)
local notation "st₀" => (levelStart space first₀ : Word w)
local notation "term" => ShrinkInput.termHead (w := w) X (tab 0)
local notation "abs₀" => ShrinkResidentPackets.absoluteWord (w := w) X (tab 0)
local notation "T" => packedIncidence space w old₀ (DemandRAM.oldCount X)
local notation "sh" => levelShape (b := b i) X
local notation "Pkt" => SourceOnline.Packet prog w
local notation "headWords" => PortRefresh.TraversalHeaders.HeadBank space
local notation "I" => BlockSlices.abInputs i (BlockProgram.arena B i.val 0) (BlockProgram.arena B i.val 1)
local notation "part₅" => ShrinkResidentPackets.window B i
local notation "part₆" => BlockSlices.abWindow B i
local notation "part₇" => SurvivingPackets.window B i
local notation "part₈" => BlockGroups.shrink B i 8
local notation "h" => ShrinkOutput.heads sh (SelectedArena.roleBase X term (10 : Word w)) (tab 3)
local notation "Y" => X.shrinkNext B.shrink (S.shrink i) sel
local notation "dst" => packedIncidence space w next₀ (actualCount sh)

private theorem offset_succ {j : ℕ} (hj : j+1 < 12) :
    (BlockGroups.shrink B i ⟨j+1,hj⟩).before.length =
    (BlockGroups.shrink B i ⟨j,by omega⟩).before.length+
      ((BlockGroups.parts B i)[j]'(by change j < 12; omega)).length := by
  rw [BlockGroups.shrink_offset,BlockGroups.shrink_offset]
  simp only [List.take_succ_eq_append_getElem (show j < (BlockGroups.parts B i).length by change j < 12; omega),
    List.flatten_append,List.flatten_cons,List.flatten_nil,List.append_nil,List.length_append,Nat.add_assoc]

/-- A consecutive trace and the native reports consumed by its calendar windows. -/
structure Output (cap : ℕ) (input : Memory w) (ps₅ ps₆ ps₇ ps₈ : List Pkt) (r : TablesRun w) : Prop where
  residents : Residents B i X sel base positions blocks round cap input ps₅
  tables : CompleteTables B i X (S.shrink i) sel term 10 abs₀ (tab 0) I pub st₀ (post input ps₅)
    (tab 1) (tab 2) (tab 3) cap (post input ps₅) r
  abReports : ps₆.flatMap SourceWalk.Packet.reports = r.intersections
  widthReports : ps₇.flatMap SourceWalk.Packet.reports = r.remainder.widthRows.flatten
  slotReports : ps₈.flatMap SourceWalk.Packet.reports = r.remainder.slots.all ++
    CopyIncidence.reports Y (directory sh h w) dst CopyIncidence.allColumns
      (after r.remainder.postWidths (eventLog r.remainder.slots.all))
  group : Group prog space base cap ((prog).initial.length+round*(prog).block.length+(BlockIndex.earlier B i).length+36)
    (directoryRows space) input (((ps₅++ps₆)++ps₇)++ps₈)
  indices : (((ps₅++ps₆)++ps₇)++ps₈).map (fun p => p.stage.phase) =
    (((part₅).indices++(part₆).indices)++(part₇).indices)++(part₈).indices
  postWidth : post input ((ps₅++ps₆)++ps₇) = r.remainder.postWidths
  readbacks : ScheduledReadbacks B i X sel base positions blocks round T (post input (((ps₅++ps₆)++ps₇)++ps₈))

set_option maxHeartbeats 2600000 in
theorem output (fuel cap : ℕ) {initial : Memory w} (p : ShrinkBranch.Prefix X T (tab 0) fuel initial)
    (v : ShrinkBranch.Selected B X T (tab 0) 10 (B.shrink.selectorBits : Word w) fuel initial p sel)
    (hp : ShrinkBranch.PrefixFits B X T (tab 0) 10 fuel)
    (header : ShrinkHeaderReads.Header i X T (tab 0) space first₀ v.beforeOutput)
    (oldHeads : headWords old₀ (DemandRAM.oldCount X) v.beforeOutput)
    (nextHeads : headWords next₀ (actualCount sh) v.beforeOutput)
    (rows : v.beforeOutput (pt).rows.val = (directoryRows space : Word w))
    (pitch : v.beforeOutput ((pt).directory-1).val = (levelWords space : Word w))
    (live : round < blocks) (sites : X.positions ≤ positions) (room : endAddress space < 2^w)
    (arithmetic : TableArithmetic B i X w) (clock : scanCap prog 95 ≤ cap) :
    ∃ ps₅ ps₆ ps₇ ps₈ r, Output B i X sel base positions blocks round cap v.beforeOutput ps₅ ps₆ ps₇ ps₈ r := by
  have clockAt (n : ℕ) (hn : n ≤ 95) : scanCap prog n ≤ cap := by unfold scanCap at *; omega
  have sourceCap : 95 ≤ cap := by unfold scanCap at clock; omega
  obtain ⟨ps₅,res⟩ := residents B i X sel base positions blocks round fuel cap p v hp header oldHeads nextHeads
    rows pitch sites room live (clockAt 40 (by decide))
  let m := post v.beforeOutput ps₅
  obtain ⟨r,native,abArgs⟩ := withAB_physical B i X base positions blocks round T m (S.shrink i) sel
    live sites room arithmetic res.header res.pitch (res.oldHeads.tables (1 : Fin 6)) res.tables cap sourceCap
    (lt_of_lt_of_le (by decide : SurvivingNative.ops.length < 95) sourceCap)
  have entry : LevelFields.Entry space first₀ pub st₀ m := ⟨rfl,res.pitch⟩
  obtain ⟨ps₆,logs₆,g₆,ids₆,_⟩ := BlockSlices.build_packets_of_run B i X base positions blocks round
    m live sites room arithmetic.widthRoom res.rows res.pitch (res.header.reads B entry)
    (res.oldHeads.tables (1 : Fin 6)) res.tables.demand m cap r.intersections abArgs native.abRun cap clock
  have post₆ : post m ps₆ = r.postAB m := by rw [post,logs₆]; rfl
  obtain ⟨ps₇,g₇,ids₇,logs₇,post₇⟩ := SurvivingPackets.group B i X T base positions blocks round sel
    (S.shrink i) m m cap cap r native live sites room res.header (res.oldHeads.tables (2 : Fin 6))
    res.rows res.pitch (clockAt _ (by decide))
  obtain ⟨ps₈,g₈,ids₈,logs₈,incidence,_⟩ := ShrinkSlotCalendar.physical_group B i X base positions blocks round
    T sel abs₀ I m m cap r live sites room res.rows res.pitch res.header (DemandRAM.oldCount X)
    res.oldHeads res.nextHeads res.tables native cap (clockAt 49 (by decide))
  have abLength : ps₆.length = ((BlockGroups.parts B i)[6]'(by change 6 < 12; decide)).length := by
    change ps₆.length = (BlockSlices.intersections i (BlockProgram.arena B i.val 0) (BlockProgram.arena B i.val 1)).length
    simpa only [List.length_map,Window.indices,List.length_ofFn] using congrArg List.length ids₆
  have widthLength : ps₇.length = ((BlockGroups.parts B i)[7]'(by change 7 < 12; decide)).length := by
    change ps₇.length = (BlockSlices.surviving B (BlockProgram.geometry B) i (BlockProgram.arena B i.val 0) (BlockProgram.arena B i.val 2)).length
    simpa only [List.length_map,Window.indices,List.length_ofFn] using congrArg List.length ids₇
  have e₆ := BlockSlices.abWindow_offset B i
  have e₇ : (part₇).before.length = (part₆).before.length+ps₆.length := by rw [abLength]; exact offset_succ B i (j := 6) (by decide)
  have e₈ : (part₈).before.length = (part₇).before.length+ps₇.length := by rw [widthLength]; exact offset_succ B i (j := 7) (by decide)
  have g₅₆ := res.group.append (show Group prog space base cap
      ((prog).initial.length+round*(prog).block.length+(BlockIndex.earlier B i).length+36+ps₅.length)
      (directoryRows space) m ps₆ by convert g₆ using 1; rw [e₆,res.length]; omega)
  have after₆ : post v.beforeOutput (ps₅++ps₆) = r.postAB m := (post_append ..).trans post₆
  have g₅₆₇ := g₅₆.append (show Group prog space base cap
      ((prog).initial.length+round*(prog).block.length+(BlockIndex.earlier B i).length+36+(ps₅++ps₆).length)
      (directoryRows space) (post v.beforeOutput (ps₅++ps₆)) ps₇ by
    rw [after₆]; convert g₇ using 1
    rw [List.length_append,res.length,e₇,e₆]; omega)
  have after₇ : post v.beforeOutput ((ps₅++ps₆)++ps₇) = r.remainder.postWidths := by
    rw [post_append,after₆,post₇]
  have all := g₅₆₇.append (show Group prog space base cap
      ((prog).initial.length+round*(prog).block.length+(BlockIndex.earlier B i).length+36+((ps₅++ps₆)++ps₇).length)
      (directoryRows space) (post v.beforeOutput ((ps₅++ps₆)++ps₇)) ps₈ by
    rw [after₇]; convert g₈ using 1
    rw [List.length_append,List.length_append,res.length,e₈,e₇,e₆]; omega)
  refine ⟨ps₅,ps₆,ps₇,ps₈,r,res,native,logs₆,logs₇,logs₈,all,?_,after₇,?_⟩
  · simp only [List.map_append,res.indices,ids₆,ids₇,ids₈]
  · rw [post_append,after₇]
    exact scheduled_readbacks B i X sel base positions blocks round T I m m cap r ps₈ live sites room res.tables
      ⟨res.published,res.directories⟩ native logs₈ incidence

end CompressorRecords.ScheduledShrink

end

end VPVNP
end Computability
end OAI
