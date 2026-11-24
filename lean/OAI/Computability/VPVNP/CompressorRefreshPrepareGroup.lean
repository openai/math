import OAI.Computability.VPVNP.CompressorRefreshCoreBuild
import OAI.Computability.VPVNP.CompressorRefreshBeforeSelector

/-!
# Native refresh prefix before reading the selected term

The gather, bundle, offset and demand scans execute from the current graph
with empty choice tapes. They produce the numerical input to the motif
worker even when the caller has not selected a term.
-/

namespace OAI
namespace Computability
namespace VPVNP

noncomputable section
set_option quotPrecheck false

namespace CompressorRecords.RefreshPrepare

open BurstRAM BlockPlanner Schedule DescriptorSpace Compression Compression.DegreeRefresh
open Compression.Refresh
open PortRefresh PortRefresh.Allocation PortRefresh.LevelRecipe SourceTransport SourceOnline
open scoped Fin.CommRing

variable {k : Type*} [_root_.Field k] {S : BlockSchedule k} (B : S.Templates)
variable {w g : ℕ} (base : BurstRAM.Word w) (positions blocks t : ℕ)
variable (X : State S.portExponent (S.portExponent + g))

local notation "s₀" => RefreshBlockPlan.shape B
local notation "scr" => BlockProgram.script B
local notation "L" => BlockProgram.layout B base.val positions blocks
local notation "pt" => Workspace.ports (arity (Script.catalog scr)) base
local notation "cur" => Script.levelsPerBlock scr * t + S.steps
local notation "start" => arrayBase L cur
local notation "P" => plan X (S.degreeExponent 0) (s₀).dH (s₀).ties (s₀).stride start
local notation "ties" => RefreshBlockPlan.order B
local notation "hC" => (S.port_bound.connected_and_pos S.port_order).1
local notation "hE" => Nat.two_pow_pos S.expanderExponent
local notation "N" => X.positions * 2 ^ S.portExponent
local notation "old" => packedIncidence L w cur N
local notation "Q" => Plan.scratch P w
local notation "D" => NewSlots.word (bits := w) (Plan.demand P)
local notation "I" => RefreshBlockPlan.input (BlockProgram.geometry B) S.steps (0 : Fin 6)

/-- The deterministic refresh prefix, consisting of the gather, bundle and offset scans
followed by one demand scan for each tie. -/
def stages : List (Stage s₀) := [.gather,.bundles,.offsets] ++ (List.finRange
    (s₀).ties).map Stage.demand

/-- Refresh stages after demand preparation, in the order of term selection, supply, expander
table rows, output slots and the base scan. -/
def rest : List (Stage s₀) := [.term,.supply] ++ (List.finRange ((s₀).ports *
    (s₀).dH)).map Stage.rom
    ++
  (List.finRange (s₀).degree).map Stage.slot ++ [.base]

theorem stages_rest : stages B ++ rest B = order s₀ := by
  simp only [stages,rest,order,List.append_assoc]

/-- The actual contiguous block interval before the selector. -/
def window : Window scr ((stages B).map (RefreshBlockPlan.stage B I)) where
  before := (BlockGroups.refresh B 1).before
  after := (rest B).map (RefreshBlockPlan.stage B I) ++ (BlockGroups.refresh B 1).after
  block := by
    have h := (BlockGroups.refresh B 1).block
    change (scr).block = (BlockGroups.refresh B 1).before ++
      (order s₀).map (RefreshBlockPlan.stage B I) ++ (BlockGroups.refresh B 1).after at h
    simpa only [← stages_rest B,List.map_append,List.append_assoc] using h

/-- The reported prefix run materializes the segment fields and the actual block demand widths
in its post-memory, writes within the planned arena, uses empty choice tapes and incurs its
stated exact charge. -/
structure Prepared (m : Memory w) (rs : List (Report w)) : Prop where
  fits : (P).segments ≤ 2 ^ w
  run : PrepareRun X old Q D ties (NewSlots.word (2 ^ g)) fits m (after m (eventLog rs)) rs
  segments : SegmentFields X Q fits (after m (eventLog rs))
  demands : ∀ b, DemandPreparation.demandAt ties (DemandScan.rowBase X (s₀).ties D b) (after m
    (eventLog rs)) =
    blockDemandWidths (splitSlots X) (bitWordFinEquiv S.portExponent) (splitWidths X) b
  writes : Writes (TermDataFrame.InArena P) (eventLog rs)
  quiet : branchPaths rs = List.replicate rs.length []
  charge : RAMBuckets.cost Report.probes rs = 6 * (P).sites + 12 * (P).segments + 3 * (P).blocks *
    (s₀).ties

private theorem quiet {js : List (Stage s₀)} {m : Memory w} {rs : List (Report w)} {cap : ℕ}
    (walk : SourceWalk (fun j mem logs ↦
      Scheduled.PreSource X S.graph hE hC B.refresh S.degree_bounds.2 ties old start
        (s₀).stride cap j mem logs ∧
      Scheduled.StageBounds (t := (s₀).ties) X S.graph hE hC B.refresh start (s₀).stride
        (levelStart L 0) j mem logs) js m rs) : branchPaths rs = List.replicate rs.length [] := by
  have empty {logs : List (Report w)} {n : ℕ} (h : branchPaths logs = List.replicate n []) :
      branchPaths logs = List.replicate logs.length [] := by
    have hn : logs.length = n := by
      simpa only [branchPaths,List.length_map,List.length_replicate] using congrArg List.length h
    rwa [hn]
  induction walk with
  | done => rfl
  | @next j js u xs ys h _ ih =>
    have head := empty (((runSegment_iff ..).mp h.1).2.2)
    simpa only [branchPaths,List.map_append,List.length_append,List.replicate_add] using congrArg₂
      (· ++ ·) head ih

set_option maxHeartbeats 900000 in
-- The demand walk is attached at dependent global indices of the actual script.
/-- Execute the complete deterministic refresh prefix without receiving a
choice. The compiled program sees the block's dense demand coordinates at
the post - memory of these exact packets. -/
theorem install (termCap cap : ℕ) (m : Memory w) (ht : t < blocks) (size : X.positions ≤ positions)
    (fit : endAddress L < 2 ^ w) (rows : m (pt).rows.val = (directoryRows L : BurstRAM.Word w))
    (pitch : m ((pt).directory - 1).val = (levelWords L : BurstRAM.Word w))
    (clock : scanCap scr (max 64 termCap) ≤ cap)
    (header : RefreshCore.Header (Fintype.card X.Base) g (levelStart L cur) start old m)
    (represented : (old).Represents X m) (width : 2 ^ S.portExponent * X.maxWireWidth < 2 ^ w)
    (positive : 0 < termCap) :
    let win := window B
    ∃ ps : List (Packet scr w), SourceOnline.Group scr L base cap
      ((scr).initial.length + t * (scr).block.length + win.before.length) (directoryRows L) m ps ∧
      ps.map (fun p ↦ p.stage.phase) = win.indices ∧ Prepared B base positions blocks t X m
        (ps.flatMap SourceWalk.Packet.reports) := by
  intro win
  have idx : cur < (L).levels := by
    have bound := Nat.mul_le_mul_left (S.steps + 1) ht
    rw [Nat.mul_succ] at bound
    change (S.steps + 1) * t + S.steps < 1 + (S.steps + 1) * blocks
    omega
  let current : Fin (L).levels := ⟨cur,idx⟩
  have source := RefreshCore.source_region B base positions blocks t X current rfl size fit
  have room := (BlockLevelFit.refresh B base.val positions blocks current rfl X size fit).1.word
  change (plan X (S.degreeExponent 0) (s₀).dH (s₀).ties (s₀).stride (start + 0 * tableWords
    L)).stop <
    2 ^ w at room
  simp only [Nat.zero_mul,Nat.add_zero] at room
  let alloc := prepare_layout X old (S.degreeExponent 0) (s₀).dH (s₀).ties (s₀).stride start
    (fun j ↦ (source j).2) room
  obtain ⟨rs,run,pr,seg,dem,_,cost⟩ := Scheduled.prepare_verified X S.graph hE hC B.refresh
    S.degree_bounds.2
    ties old start (s₀).stride (levelStart L 0) termCap alloc m represented (fun j ↦ (source j).1)
    (fun j ↦ (source j).2) room width
  have before : levelStart L cur + 60 < start := by
    change levelStart L cur + 60 < levelStart L cur + 66 + 6 * slotCapacity L
    omega
  have Hfit := (levelStart_mono L (Nat.zero_le _)).trans_lt fit
  obtain ⟨raw,wr⟩ := RefreshCore.raw_stages B X old start termCap base positions blocks t
    (fun j ↦ List.replicate (j.limit X start - j.first) []) (stages B) m rs header pitch
    positive room before Hfit run
  have clocks (j : Fin (scr).size) := scanCap_clocks
    (p := ⟨HeaderPacket.attach scr j (pt).data 0 m (max 64 termCap) [],m,[]⟩) _ le_rfl clock
  have live (j : Fin ((stages B).map (RefreshBlockPlan.stage B I)).length) :
      Window.ordinal (A := scr) t (win.index j) < directoryRows L := by
    rw [win.ordinal_index,BlockProgram.directory_rows,(scr).calendar_total]
    have pos := (win.position j).isLt
    have mul := Nat.mul_le_mul_right (scr).block.length ht
    rw [Nat.succ_mul] at mul
    omega
  obtain ⟨ps,grp,phases,logs⟩ := win.group L base t rfl rfl Hfit cap (max 64 termCap) m rs raw
    rows pitch live (fun j _ ↦ (clocks j).1) (fun j _ ↦ (clocks j).2)
  refine ⟨ps,grp,phases,?_⟩
  rw [logs]
  exact ⟨alloc.regions.fits,pr,seg,dem,wr,quiet B base positions blocks t X run,cost⟩

end CompressorRecords.RefreshPrepare

end

end VPVNP
end Computability
end OAI
