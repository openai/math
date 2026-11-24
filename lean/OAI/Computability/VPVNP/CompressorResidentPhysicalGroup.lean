import OAI.Computability.VPVNP.CompressorResidentGeometry
import OAI.Computability.VPVNP.CompressorResidentPacketGroup
import OAI.Computability.VPVNP.CompressorPublishedHeadWindows

/-! # Resident rows at an actual selected shrinking level

A fitted descriptor allocation and the published old header are sufficient
to locate both input tables, the selected score, and the six output heads.
The next phase receives the same old graph and selected term data outside
these two resident rectangles.
-/

namespace OAI
namespace Computability
namespace VPVNP

noncomputable section

namespace CompressorRecords.ShrinkResidentPackets

open Compression BurstRAM BlockPlanner PhaseRecipe SourceTransport SourceOnline DescriptorSpace
open ShrinkResidentRun ShrinkResidentLayout
open scoped Classical Fin.CommRing


private theorem pass_bits {a g w : ℕ} {Y : State a (packingLaneBits a g)} {arena : ℕ} {abs role : Word w}
    {side maps : Bool} {m : Memory w} {r : Passes w} (h : Built Y arena abs role side maps m r) :
    branchPaths r.all = List.replicate (2*(layout Y arena).size maps+(layout Y arena).sites) [] := by
  have x := ((runSegment_iff ..).mp h.owners.native).2.2
  have y := ((runSegment_iff ..).mp h.clear).2.2
  have z := ((runSegment_iff ..).mp h.collect).2.2
  change branchPaths r.owners = List.replicate ((layout Y arena).size maps) [] at x
  change branchPaths ((r.owners++r.clear)++r.collect) = _
  rw [show branchPaths ((r.owners++r.clear)++r.collect) =
    (branchPaths r.owners++branchPaths r.clear)++branchPaths r.collect by simp only [branchPaths,List.map_append]]
  rw [x,y,z,← List.replicate_add,← List.replicate_add]
  congr 1
  omega

variable {k : Type*} [_root_.Field k] {S : BlockSchedule k} (B : S.Templates) (i : Fin S.steps)
  {g w : ℕ} (X : State (ShrinkBlockInputs.a i) (packingLaneBits (ShrinkBlockInputs.a i) g))
variable (base : Word w) (positions blocks t : ℕ)
local notation "A" => BlockProgram.script B
local notation "L" => BlockProgram.layout B base.val positions blocks
local notation "H" => levelStart L 0
local notation "W" => window B i
local notation "pt" => Workspace.ports (Schedule.arity (BlockPlanner.Script.catalog A)) base
local notation "pub" => Schedule.Ports.data pt
local notation "blockFirst" => BlockPlanner.Script.levelsPerBlock A*t
local notation "st" => (levelStart L blockFirst : Word w)
local notation "stepLevel" => blockFirst+i.val
local notation "oldHead" => levelStart L stepLevel
local notation "first" => tableBase L stepLevel (5 : Fin 6)
local notation "start" => tableBase L stepLevel (0 : Fin 6)
local notation "P" => plan B i
local notation "term" => ShrinkInput.termHead (w := w) X start
local notation "D" => values P X first oldHead (absoluteWord (w := w) X start) (roleWord (w := w) X start)

theorem physical_group (m : Memory w) (inc : IncidenceDirectory w) (side : Bool)
    (fields : ShrinkHeaderReads.Header i X inc start L blockFirst m)
    (head : m (tableHead L stepLevel (5 : Fin 6)) = (first : Word w))
    (chosen : m (scoreAddr (w := w) X start) = (side.toNat : Word w))
    (dir : ShrinkResidentDirectory.Absolute X (absoluteWord X start) m)
    (roles : DemandRAM.RoleColumns X side (SelectedArena.roleBase X term (10 : Word w)) m)
    (size : X.positions ≤ positions) (fits : endAddress L < 2^w)
    (rows : m (pt).rows.val = (directoryRows L : Word w)) (pitch : m ((pt).directory-1).val = (levelWords L : Word w))
    (ht : t < blocks) (cap : ℕ) (hc : clock B ≤ cap) :
    ∃ ps : List (SourceOnline.Packet A w),
      Group A L base cap ((A).initial.length+t*(A).block.length+(BlockIndex.earlier B i).length+36)
        (directoryRows L) m ps ∧ ps.map (fun p => p.stage.phase) = (W).indices ∧
      (∀ j : Fin 6, post m ps (oldHead+(30+j.val)) = (ShrinkResidentsPlan.headValues (layout X first) j : Word w)) ∧
      (∀ x, ¬ Mutable (D side) x → post m ps x = m x) ∧
      (∀ maps : Bool, ShrinkHistoryRows.Directory (ShrinkResidentDirectory.oldOrder X maps) (ShrinkHistoryRows.packedOrder X)
        (ShrinkResidentDirectory.place X maps side) (outputBank X first maps) (post m ps)) ∧
      RAMBuckets.cost Report.probes (ps.flatMap SourceWalk.Packet.reports) = (layout X first).charge ∧
      ps.length=12 ∧ ps.flatMap (fun p => p.stage.choices) = List.replicate (layout X first).calls [] := by
  have within : stepLevel < (L).levels := by
    change (S.steps+1)*t+i.val < 1+(S.steps+1)*blocks
    have h := Nat.mul_le_mul_left (S.steps+1) ht
    rw [Nat.mul_succ] at h
    have := i.isLt
    omega
  let old : Fin (L).levels := ⟨stepLevel,within⟩
  obtain ⟨space,absLow,roleLow,scoreLow,scoreHigh,termFit,ten,headerFit,roleValue⟩ :=
    geometry B i X base positions blocks old size fits
  have entry : LevelFields.Entry L blockFirst pub st m := ⟨rfl,pitch⟩
  have selected := (SelectedTailPackets.header_values B i X inc start pub st m fields entry termFit ten
    (fun _ => True) trivial (fun _ _ => trivial)).1
  have score := SelectedPlan.score_head (P).chosen X (ShrinkInput.placementBank X inc start) inc term pub st m selected
  have arenaFit : first < 2^w := by
    have bound := (layout X first).ranges false
    obtain ⟨o,c,r,stop⟩ := bound
    change first ≤ (layout X first).owner false at o
    have top : (layout X first).endAddr < 2^w := space.fit
    omega
  have cell : ((SelectedPlan.layoutCell (P).chosen).eval pub st m).val = scoreAddr (w := w) X start := by
    have eq : (SelectedPlan.layoutCell (P).chosen).eval pub st m = (scoreAddr (w := w) X start : Word w) := by
      change (SelectedPlan.scoreBase (P).chosen).eval pub st m+2 =
        ((SelectedArena.origin X term (10 : Word w)+2 : ℕ) : Word w)
      rw [score,Nat.cast_add]
      rfl
    exact (congrArg Fin.val eq).trans (Nat.mod_eq_of_lt (scoreHigh.trans arenaFit))
  have values := header_values B i X base positions blocks t m inc start side entry headerFit fields termFit ten
    head (by rw [cell]; exact chosen)
  obtain ⟨h,r,ps,hh,hr,checked,stages,logs,heads,keep,dirs,cost⟩ := group B i X base positions blocks t m
    (absoluteWord (w := w) X start) (roleWord (w := w) X start) side space dir (roleValue.symm ▸ roles)
    absLow roleLow values (by rw [cell]; exact scoreLow) (by rw [cell]; exact scoreHigh) rows pitch ht cap hc
  have num : ps.length = 12 := by
    have len := congrArg List.length stages
    simp only [Window.indices,List.length_map,List.length_ofFn] at len
    exact len.trans (ShrinkResidentsPlan.visits_length ..)
  have quiet : ps.flatMap (fun p => p.stage.choices) = List.replicate (layout X first).calls [] := by
    rw [PublishedHeads.chronological_tapes m ps checked.chronological,logs]
    have headBits : branchPaths (List.ofFn (ShrinkResidentsPlan.headerReport oldHead (layout X first) w)) =
        List.replicate 6 [] := rfl
    rw [show branchPaths (h.all++r.all++List.ofFn (ShrinkResidentsPlan.headerReport oldHead (layout X first) w)) =
      (branchPaths h.all++branchPaths r.all)++branchPaths (List.ofFn (ShrinkResidentsPlan.headerReport oldHead (layout X first) w))
      by simp only [branchPaths,List.map_append]]
    rw [pass_bits hh,pass_bits hr,headBits,← List.replicate_add,← List.replicate_add]
    congr 1
    change 2*((layout X first).motifs*4)+(layout X first).sites+(2*((layout X first).motifs*6)+(layout X first).sites)+6 =
      20*(layout X first).motifs+2*(layout X first).sites+6
    omega
  refine ⟨ps,checked,stages,heads,?_,dirs,cost,num,quiet⟩
  intro x outside
  have apart (maps : Bool) : x < (layout X first).owner maps ∨
      (layout X first).rows maps+(layout X first).size maps ≤ x := by
    obtain ⟨lo,_,_,hi⟩ := (layout X first).ranges maps
    by_cases h : x < (layout X first).owner maps
    · exact .inl h
    · exact .inr (le_of_not_gt fun hx => outside (.inl ⟨lo.trans (Nat.le_of_not_gt h),hx.trans_le hi⟩))
  have header : x<oldHead+30 ∨ oldHead+36≤x := by
    by_cases before : x<oldHead+30
    · exact .inl before
    · exact .inr (le_of_not_gt fun h => outside (.inr ⟨Nat.le_of_not_gt before,h⟩))
  exact (keep x header).trans ((hr.frame x (apart true)).trans (hh.frame x (apart false)))

end CompressorRecords.ShrinkResidentPackets

end

end VPVNP
end Computability
end OAI
