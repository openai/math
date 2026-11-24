import OAI.Computability.VPVNP.CompressorRefreshSelectorLogs
import OAI.Computability.VPVNP.CompressorDeterministicGroup
import OAI.Computability.VPVNP.CompressorSourceGroupSplit

/-! # Three consecutive online windows around the refresh selector

Each native subwalk retains its reports while the dispatcher computes its
own rows. The earlier physical columns and the level header survive all
three subwalks, since every worker writes only to its refresh workspace.
-/

namespace OAI
namespace Computability
namespace VPVNP

noncomputable section
set_option quotPrecheck false

namespace CompressorRecords.RefreshCore

open BurstRAM Compression Compression.Refresh Compression.DegreeRefresh PhaseRecipe BlockPlanner Schedule
open DescriptorSpace PortRefresh PortRefresh.LevelRecipe PortRefresh.Allocation SourceTransport SourceOnline
open scoped Fin.CommRing

variable {k : Type*} [_root_.Field k] {S : BlockSchedule k} (B : S.Templates)
local notation "scr" => BlockProgram.script B
local notation "sh" => RefreshBlockPlan.shape B
local notation "I" => RefreshCore.input B
local notation "W" => BlockGroups.refresh B 1

private def lists : List (List (BlockPlanner.Visit)) :=
  [(RefreshPrepare.stages B).map (RefreshBlockPlan.stage B I),[RefreshBlockPlan.stage B I .term],
    (afterTerm B).map (RefreshBlockPlan.stage B I)]

private theorem flattened : (lists B).flatten = entries B := by
  change _ = (LevelRecipe.order sh).map (RefreshBlockPlan.stage B I)
  rw [stage_split]
  simp only [lists,List.flatten_cons,List.flatten_nil,List.append_nil,List.map_append,List.map_cons,
    List.cons_append,List.nil_append]

/-- The one-stage window for selecting a refresh term, immediately after the refresh
preparation stages. -/
def selectWindow : Window scr [RefreshBlockPlan.stage B I .term] :=
  BlockGroups.within W (lists B) (flattened B) ⟨1,show 1 < 3 by decide⟩

/-- The window for the remaining refresh stages after the selected term. -/
def finishWindow : Window scr ((afterTerm B).map (RefreshBlockPlan.stage B I)) :=
  BlockGroups.within W (lists B) (flattened B) ⟨2,show 2 < 3 by decide⟩

theorem select_before : (selectWindow B).before.length = (W).before.length+(RefreshPrepare.stages B).length := by
  change ((W).before ++ _).length = _
  rw [List.length_append]; congr 1
  simp [lists,List.length_map]

theorem finish_before : (finishWindow B).before.length =
    (W).before.length+(RefreshPrepare.stages B).length+1 := by
  change ((W).before ++ _).length = _
  rw [List.length_append]
  simp [lists,List.length_map,Nat.add_assoc]

theorem select_index : (selectWindow B).index 0 = RefreshCore.index B (CanonicalWorker.refreshTermIndex B) := by
  have len : (RefreshPrepare.stages B).length = 3+(sh).ties := by simp [RefreshPrepare.stages]; omega
  apply Fin.ext
  rw [Window.index_val,select_before,RefreshCore.index,Window.index_val,Fin.val_cast,CanonicalWorker.refreshTermIndex_val,len]
  change (scr).initial.length+((W).before.length+(3+(sh).ties))+0 =
    (scr).initial.length+(W).before.length+(3+(sh).ties)
  omega

variable {w g : ℕ} (base : BurstRAM.Word w) (positions blocks t : ℕ)
variable (X : State S.portExponent (S.portExponent+g))
variable (c : DyadicRefreshChoice X S.graph (Nat.two_pow_pos _) (S.port_bound.connected_and_pos S.port_order).1 B.refresh)
local notation "L" => BlockProgram.layout B base.val positions blocks
local notation "pt" => Workspace.ports (arity (Script.catalog scr)) base
local notation "cur" => Script.levelsPerBlock scr*t+S.steps
local notation "head" => levelStart L cur
local notation "H" => levelStart L 0
local notation "start" => arrayBase L cur
local notation "old" => packedIncidence L w cur (X.positions*2^S.portExponent)
local notation "P" => plan X (sh).a₀ (sh).dH (sh).ties (sh).stride start
local notation "hc" => (S.port_bound.connected_and_pos S.port_order).1
local notation "he" => Nat.two_pow_pos S.expanderExponent
local notation "hd" => S.degree_bounds.2
local notation "ties" => RefreshBlockPlan.order B

/-- The three incoming memory facts needed by all refresh subwindows. -/
structure EntryState (m : Memory w) : Prop where
  header : Header (Fintype.card X.Base) g head start old m
  rows : m (pt).rows.val = (directoryRows L : BurstRAM.Word w)
  pitch : m ((pt).directory-1).val = (levelWords L : BurstRAM.Word w)

variable (termCap : ℕ)
local notation "src" => Scheduled.Source X S.graph he hc B.refresh hd c ties old start (sh).stride termCap
local notation "bounded" => Scheduled.StageBounds (t := (sh).ties) X S.graph he hc B.refresh start (sh).stride H

/-- Attach one contiguous subwalk and retain its exact report list and
the state of the header needed by the next subwalk. -/
theorem attach_part (js : List (Stage sh)) (win : Window scr (js.map (RefreshBlockPlan.stage B I)))
    {m : Memory w} {rs : List (Report w)} (entry : EntryState B base positions blocks t X m)
    (ht : t < blocks) (fit : H < 2^w) (room : (P).stop < 2^w) (before : head+60 < start)
    (positive : 0 < termCap) (cap : ℕ) (clock : SourceOnline.scanCap scr (max 64 termCap) ≤ cap)
    (walk : SourceWalk (fun j m rs => src j m rs ∧ bounded j m rs) js m rs) :
    ∃ ps : List (SourceOnline.Packet scr w),
      Group scr L base cap ((scr).initial.length+t*(scr).block.length+win.before.length) (directoryRows L) m ps ∧
      ps.map (fun p => p.stage.phase) = win.indices ∧ ps.flatMap SourceWalk.Packet.reports = rs ∧
      EntryState B base positions blocks t X (after m (eventLog rs)) := by
  obtain ⟨raw,wr⟩ := raw_stages B X old start termCap base positions blocks t
    (Scheduled.tapes (t := (sh).ties) (w := w) X S.graph he hc B.refresh c start (sh).stride)
    js m rs entry.header entry.pitch positive room before fit walk
  have live (j : Fin (js.map (RefreshBlockPlan.stage B I)).length) : Window.ordinal (A:=scr) t (win.index j) < directoryRows L := by
    rw [win.ordinal_index,BlockProgram.directory_rows,(scr).calendar_total]
    have mul := Nat.mul_le_mul_right (scr).block.length ht
    rw [Nat.succ_mul] at mul
    have loc := (win.position j).isLt
    omega
  have clocks (j : Fin (scr).size) := scanCap_clocks
    (p := ⟨HeaderPacket.attach scr j (pt).data 0 m (max 64 termCap) [],m,[]⟩) _ le_rfl clock
  obtain ⟨ps,grp,labels,reports⟩ := win.group L base t rfl rfl fit cap (max 64 termCap) m rs raw
    entry.rows entry.pitch live (fun j _ => (clocks j).1) (fun j _ => (clocks j).2)
  have keep (x : ℕ) (lt : x < start) : after m (eventLog rs) x = m x :=
    after_outside m wr (fun h => (Nat.not_le_of_lt lt) h.1)
  have lo := levelStart_mono L (Nat.zero_le cur)
  have gap := Window.lowCells (A := scr) L base rfl rfl fit
  exact ⟨ps,grp,labels,reports,entry.header.keep (fun j hj => keep _ (by omega)),
    (keep _ (gap.1.trans (by omega))).trans entry.rows,(keep _ (gap.2.trans (by omega))).trans entry.pitch⟩

end CompressorRecords.RefreshCore

end

end VPVNP
end Computability
end OAI
