import OAI.Computability.VPVNP.CompressorShrinkResidentInterval
import OAI.Computability.VPVNP.CompressorResidentPhysicalGroup
import OAI.Computability.VPVNP.CompressorResidentPhysicalFrame
import OAI.Computability.VPVNP.CompressorBlockCapacity
import OAI.Computability.VPVNP.CompressorRefreshTraversalHeaders

/-! # Hidden and map directories on a selected shrinking branch

The twelve resident visits consume the score bit, role columns and compact
absolute-ID table on the same branch that chose the terms. The six header
writes precede the two slice calendars, with all their scratch inputs intact.
-/

namespace OAI
namespace Computability
namespace VPVNP

noncomputable section

namespace CompressorRecords.ScheduledShrink

open BurstRAM Compression ShrinkBlockInputs DescriptorSpace SourceOnline BlockPlanner
open ShrinkResidentRun ShrinkResidentLayout ShrinkOutput SlotLevel ShrinkSlots
open scoped Classical Fin.CommRing

variable {k : Type*} [_root_.Field k] {S : BlockSchedule k} (B : S.Templates) (i : Fin S.steps)
variable {w g : ℕ} (X : State (a i) (packingLaneBits (a i) g)) (sel : SelectedScore.Selection B X)
variable (base : Word w) (positions blocks round : ℕ)
local notation "prog" => BlockProgram.script B
local notation "space" => BlockProgram.layout B base.val positions blocks
local notation "pt" => Workspace.ports (Schedule.arity (Script.catalog prog)) base
local notation "first₀" => Script.levelsPerBlock prog * round
local notation "old₀" => first₀+i.val
local notation "next₀" => old₀+1
local notation "tab" => tableBase space old₀
local notation "head₀" => levelStart space old₀
local notation "start₀" => tableBase space old₀ (0 : Fin 6)
local notation "term" => ShrinkInput.termHead (w := w) X start₀
local notation "abs₀" => ShrinkResidentPackets.absoluteWord (w := w) X start₀
local notation "T" => packedIncidence space w old₀ (DemandRAM.oldCount X)
local notation "side₀" => SelectedFinish.chosen B X sel
local notation "sh" => levelShape (b := b i) X
local notation "Pkt" => SourceOnline.Packet prog w
local notation "heads₀" => PortRefresh.TraversalHeaders.HeadBank space old₀ (DemandRAM.oldCount X)
local notation "heads₁" => PortRefresh.TraversalHeaders.HeadBank space next₀ (actualCount sh)

/-- Certifies the twelve resident visits of a selected shrink branch. Their final memory
contains both per-site directories and their six header pointers, while preserving the data
needed by the following slice scans. -/
structure Residents (cap : ℕ) (mem : Memory w) (ps : List Pkt) : Prop where
  group : Group prog space base cap ((prog).initial.length+round*(prog).block.length+(BlockIndex.earlier B i).length+36)
    (directoryRows space) mem ps
  indices : ps.map (fun p => p.stage.phase) = (ShrinkResidentPackets.window B i).indices
  length : ps.length = 12
  tapes : ps.flatMap (fun p => p.stage.choices) = List.replicate (ShrinkResidentLayout.layout X (tab (5 : Fin 6))).calls []
  cost : RAMBuckets.cost Report.probes (ps.flatMap SourceWalk.Packet.reports) =
    (ShrinkResidentLayout.layout X (tab (5 : Fin 6))).charge
  published : ∀ j : Fin 6, post mem ps (head₀+(30+j.val)) =
    (ShrinkResidentsPlan.headValues (ShrinkResidentLayout.layout X (tab (5 : Fin 6))) j : Word w)
  preserved : ∀ x, ¬ ShrinkResidentPackets.Mutable (ShrinkResidentPackets.values (ShrinkResidentPackets.plan B i)
    X (tab (5 : Fin 6)) head₀ abs₀ (ShrinkResidentPackets.roleWord X start₀) side₀) x → post mem ps x = mem x
  directories : ∀ maps : Bool, ShrinkHistoryRows.Directory (ShrinkResidentDirectory.oldOrder X maps)
    (ShrinkHistoryRows.packedOrder X) (ShrinkResidentDirectory.place X maps side₀)
    (outputBank X (tab (5 : Fin 6)) maps) (post mem ps)
  rows : post mem ps (pt).rows.val = (directoryRows space : Word w)
  pitch : post mem ps ((pt).directory-1).val = (levelWords space : Word w)
  header : ShrinkHeaderReads.Header i X T start₀ space first₀ (post mem ps)
  oldHeads : heads₀ (post mem ps)
  nextHeads : heads₁ (post mem ps)
  tables : ShrinkOutput.Resident B i X sel term 10 abs₀ T start₀ (tab (2 : Fin 6)) (post mem ps)

set_option maxHeartbeats 1600000 in
theorem residents (fuel cap : ℕ) {initial : Memory w} (p : ShrinkBranch.Prefix X T start₀ fuel initial)
    (v : ShrinkBranch.Selected B X T start₀ 10 (B.shrink.selectorBits : Word w) fuel initial p sel)
    (hp : ShrinkBranch.PrefixFits B X T start₀ 10 fuel)
    (header : ShrinkHeaderReads.Header i X T start₀ space first₀ v.beforeOutput)
    (oldHeads : heads₀ v.beforeOutput) (nextHeads : heads₁ v.beforeOutput)
    (rows : v.beforeOutput (pt).rows.val = (directoryRows space : Word w))
    (pitch : v.beforeOutput ((pt).directory-1).val = (levelWords space : Word w))
    (sites : X.positions ≤ positions) (room : endAddress space < 2^w)
    (live : round < blocks) (clock : ShrinkResidentPackets.clock B ≤ cap) :
    ∃ ps, Residents B i X sel base positions blocks round cap v.beforeOutput ps := by
  have liveOld : old₀ < (space).levels := by
    change (S.steps+1)*round+i.val < 1+(S.steps+1)*blocks
    have bound := Nat.mul_le_mul_left (S.steps+1) live
    rw [Nat.mul_succ] at bound; have := i.isLt; omega
  let old : Fin (space).levels := ⟨_,liveOld⟩
  have amount : X.positions*ShrinkLevelSpace.tableFactor S ≤ tableWords space := by
    change _ ≤ positions*(BlockProgram.allocationShape B).slots*(BlockProgram.allocationShape B).fields
    rw [Nat.mul_assoc]; exact Nat.mul_le_mul sites (BlockProgram.field_rates B base.val positions blocks).1
  have bounds := ShrinkLevelSpace.packed_ends S i X start₀ (tab (1 : Fin 6)) (tab (2 : Fin 6)) (tab (3 : Fin 6)) w
  have word₀ := tableStop_lt space old (0 : Fin 6) amount room
  have termRoom : ShrinkInput.termEnd X start₀ 10 < 2^w := bounds.2.1.trans_lt word₀
  have selectedRoom : SelectedFinish.stop X term (10 : Word w) < 2^w := bounds.2.2.1.trans_lt word₀
  have within₀ : SelectedFinish.stop X term (10 : Word w) ≤ start₀+tableWords space :=
    bounds.2.2.1.trans (Nat.add_le_add_left amount _)
  have src := resident_of_branch B i X sel T start₀ 10 (B.shrink.selectorBits : Word w) fuel p v hp
    (tab (2 : Fin 6)) v.beforeOutput (fun _ _ => rfl)
  obtain ⟨ps,group,ids,heads,frame,dirs,charge,len,tapes⟩ := ShrinkResidentPackets.physical_group
    B i X base positions blocks round v.beforeOutput T side₀ header (oldHeads.tables (5 : Fin 6)) src.chosen
    src.directory src.roles sites room rows pitch live cap clock
  have fr := ShrinkResidentPackets.physical_frame B i X base positions blocks old sites room abs₀
    (ShrinkResidentPackets.roleWord X start₀) side₀ v.beforeOutput (post v.beforeOutput ps) frame
  have fields : ShrinkHeaderReads.Header i X T start₀ space first₀ (post v.beforeOutput ps) :=
    ⟨header.room,(fr.scalar 0 (by decide)).trans header.vertices,(fr.scalar 1 (by decide)).trans header.degree,
      (fr.scalar 2 (by decide)).trans header.lanes,(fr.scalar 3 (by decide)).trans header.residual,
      fun c => (fr.higher (54+c.val) (by omega) (by have := c.isLt; omega)).trans (header.incidence c),(fr.tables 0).trans header.scratch⟩
  have oldWords : heads₀ (post v.beforeOutput ps) :=
    ⟨fun c => (fr.incidence c).trans (oldHeads.incidence c),fun c => (fr.tables c).trans (oldHeads.tables c)⟩
  have newWords := nextHeads.keep (fun n _ => fr.next _ (Nat.le_add_right ..))
  have retained := resident_of_branch_interval B i X sel T start₀ (B.shrink.selectorBits : Word w) fuel p v hp
    termRoom selectedRoom.le (tab (2 : Fin 6)) (post v.beforeOutput ps)
    (fun x low high => fr.tableZero x low (high.trans_le within₀))
  exact ⟨ps,group,ids,len,tapes,charge,heads,frame,dirs,fr.rows.trans rows,fr.pitch.trans pitch,fields,oldWords,newWords,retained⟩

end CompressorRecords.ScheduledShrink

end

end VPVNP
end Computability
end OAI
