import OAI.Computability.VPVNP.CompressorRefreshWindowRun
import OAI.Computability.VPVNP.CompressorBlockLevelFit

/-!
# Online realization of the selected refresh's descriptor arrays

The graph at the old canonical incidence columns is the only graph read by
the source. Its size controls the packed allocation. The resulting packets
occupy exactly group one of the refresh calendar and retain both the
successor incidence and the chosen local motif records.
-/

namespace OAI
namespace Computability
namespace VPVNP

noncomputable section

set_option quotPrecheck false

namespace CompressorRecords.RefreshCore

open BurstRAM BlockPlanner Schedule DescriptorSpace Compression Compression.DegreeRefresh
open Compression.Refresh
open PortRefresh PortRefresh.Allocation PortRefresh.LevelRecipe SourceTransport SourceOnline
open scoped Fin.CommRing

variable {k : Type*} [_root_.Field k] {S : BlockSchedule k} (B : S.Templates)
variable {w g : ℕ} (base : BurstRAM.Word w) (positions blocks t : ℕ)
variable (X : State S.portExponent (S.portExponent + g))
variable (c : DyadicRefreshChoice X S.graph (Nat.two_pow_pos _) (S.port_bound.connected_and_pos
    S.port_order).1 B.refresh)
local notation "scr" => BlockProgram.script B
local notation "L" => BlockProgram.layout B base.val positions blocks
local notation "pt" => Workspace.ports (arity (Script.catalog scr)) base
local notation "cur" => Script.levelsPerBlock scr * t + S.steps
local notation "start" => arrayBase L cur
local notation "s₀" => RefreshBlockPlan.shape B
local notation "ties" => RefreshBlockPlan.order B
local notation "P" => plan X (S.degreeExponent 0) (s₀).dH (s₀).ties (s₀).stride start
local notation "hC" => (S.port_bound.connected_and_pos S.port_order).1
local notation "hE" => Nat.two_pow_pos S.expanderExponent
local notation "Y" => dyadicRefreshNext X S.graph hE hC B.refresh S.port_order S.degree_bounds.2 c
local notation "N" => X.positions * 2 ^ S.portExponent
local notation "old" => packedIncidence L w cur N
local notation "W" => BlockGroups.refresh B 1

/-- Certificate that the native refresh implements the selected branch, stores its terms,
represents its output incidence, and confines writes to the arena. The total charge, one
per report plus its probes, is bounded by a fixed factor times the number of input
positions. -/
structure Built (termCap : ℕ) (m : Memory w) (rs : List (Report w)) : Prop where
  fits : (P).segments ≤ 2 ^ w
  source : ∃ alloc, Build.Run X S.graph hE hC B.refresh S.port_order S.degree_bounds.2 c ties old
    start
    (s₀).stride termCap alloc m rs
  represents : ((P).output w).Represents Y (after m (eventLog rs))
  stored : Build.Stored X S.graph hE hC B.refresh c ties start (s₀).stride fits (after m
    (eventLog rs))
  writes : Writes (TermDataFrame.InArena P) (eventLog rs)
  charge : RAMBuckets.cost Report.probes rs ≤ Build.chargeFactor S.graph hE hC B.refresh
    (s₀).ties * X.positions

/-- The upper bound and origin of every old source column, with room for all
physical slots of the incoming graph before the first scratch cell. -/
theorem source_region (current : Fin (L).levels) (idx : current.val = cur)
    (size : X.positions ≤ positions) (fit : endAddress L < 2 ^ w) (j : Fin 6) :
    levelStart L 0 ≤ ((old).column j).val ∧ ((old).column j).val + (P).segments ≤ start := by
  have degree : 2 ^ S.portExponent ≤ slotDegree S := le_max_left ..
  have capacity : N ≤ slotCapacity L := Nat.mul_le_mul size degree
  have room := packed_incidence_room L fit current capacity
  rw [idx] at room
  have hj := Nat.mul_le_mul_right (N) j.isLt
  rw [Nat.succ_mul] at hj
  have head : ((old).column j).val = incidenceStart L cur + j.val * (N) := by
    rw [packed_column]
    exact Nat.mod_eq_of_lt (by change incidenceStart L cur + j.val * (N) < 2 ^ w; omega)
  have seg : (P).segments = N := congrArg (· * 2 ^ S.portExponent)
    (bundleCount_positions X (IncidenceDirectory.baseOrder X))
  rw [head,seg]
  refine ⟨(levelStart_mono L (Nat.zero_le _)).trans ((Nat.le_add_right ..).trans
    (Nat.le_add_right ..)),?_⟩
  change incidenceStart L cur + j.val * (N) + (N) ≤ incidenceStart L cur + 6 * slotCapacity L
  exact (by omega : incidenceStart L cur + j.val * (N) + (N) ≤ incidenceStart L cur + 6 * (N)).trans
    (Nat.add_le_add_left (Nat.mul_le_mul_left 6 capacity) _)

set_option maxHeartbeats 900000 in
-- The calendar walk reuses the chosen graph and its typed motif grid.
theorem build_group (termCap cap : ℕ) (m : Memory w) (ht : t < blocks) (size : X.positions ≤
    positions)
    (fit : endAddress L < 2 ^ w) (rows : m (pt).rows.val = (directoryRows L : BurstRAM.Word w))
    (pitch : m ((pt).directory - 1).val = (levelWords L : BurstRAM.Word w))
    (clock : scanCap scr (max 64 termCap) ≤ cap)
    (header : Header (Fintype.card X.Base) g (levelStart L cur) start old m)
    (represented : (old).Represents X m)
    (termBits : termConstant S.graph hE hC B.refresh ties + 4 * Nat.clog 2 (X.maxWireWidth + 1) ≤ w)
    (nextWidth : (Y).maxWireWidth < 2 ^ w)
    (budget : TermWorker.budget B.refresh (s₀).ties ((s₀).ports * (s₀).dH) w X.maxWireWidth ≤
      termCap)
    (positive : 0 < termCap) :
    ∃ ps : List (Packet scr w), SourceOnline.Group scr L base cap ((scr).initial.length + t *
      (scr).block.length + (W).before.length)
      (directoryRows L) m ps ∧ ps.map (fun p ↦ p.stage.phase) = (W).indices ∧
      Built B base positions blocks t X c termCap m (ps.flatMap SourceWalk.Packet.reports) := by
  have idx : cur < (L).levels := by
    have bound := Nat.mul_le_mul_left (S.steps + 1) ht
    rw [Nat.mul_succ] at bound
    change (S.steps + 1) * t + S.steps < 1 + (S.steps + 1) * blocks
    omega
  let current : Fin (L).levels := ⟨cur,idx⟩
  have source := source_region B base positions blocks t X current rfl size fit
  have room := (BlockLevelFit.refresh B base.val positions blocks current rfl X size fit).1.word
  change (plan X (S.degreeExponent 0) (s₀).dH (s₀).ties (s₀).stride (start + 0 * tableWords
    L)).stop < 2 ^ w at room
  simp only [Nat.zero_mul,Nat.add_zero] at room
  let alloc := prepare_layout X old (S.degreeExponent 0) (s₀).dH (s₀).ties (s₀).stride start
    (fun j ↦ (source j).2) room
  obtain ⟨rs,run,rep,stored,_,charge⟩ := Build.build X S.graph hE hC B.refresh S.port_order
    S.degree_bounds.2 c
    ties old start (s₀).stride m represented (fun j ↦ (source j).2) le_rfl room termBits nextWidth
      termCap budget
  have native := Scheduled.verified_sources X S.graph hE hC B.refresh S.port_order
    S.degree_bounds.2 c
    ties old start (s₀).stride (levelStart L 0) termCap alloc m rs represented
    (fun j ↦ (source j).1) (fun j ↦ (source j).2) le_rfl room termBits nextWidth budget run
  have before : levelStart L cur + 60 < start := by
    change levelStart L cur + 60 < levelStart L cur + 66 + 6 * slotCapacity L
    omega
  have Hfit := (levelStart_mono L (Nat.zero_le _)).trans_lt fit
  obtain ⟨raw,wr⟩ := raw_window B X c old start termCap base positions blocks t m rs header pitch
    positive room before Hfit native
  have clocks (j : Fin (scr).size) := scanCap_clocks
    (p := ⟨HeaderPacket.attach scr j (pt).data 0 m (max 64 termCap) [],m,[]⟩) _ le_rfl clock
  have existsPart : 1 < (BlockGroups.refreshParts B).length := by
    rw [BlockGroups.refreshParts_length]
    decide
  have live (j : Fin ((BlockGroups.refreshParts B)[1]'existsPart).length) :
      Window.ordinal (A := scr) t ((W).index j) < directoryRows L := by
    rw [(W).ordinal_index,BlockProgram.directory_rows,(scr).calendar_total]
    have pos := ((W).position j).isLt
    have mul := Nat.mul_le_mul_right (scr).block.length ht
    rw [Nat.succ_mul] at mul
    omega
  obtain ⟨ps,grp,phases,logs⟩ := (W).group L base t rfl rfl Hfit cap (max 64 termCap) m rs raw
    rows pitch live (fun j _ ↦ (clocks j).1) (fun j _ ↦ (clocks j).2)
  refine ⟨ps,grp,phases,?_⟩
  rw [logs]
  exact ⟨alloc.regions.fits,⟨alloc,run⟩,rep,stored,wr,charge.trans
    (Build.charge_le_positions (t := (s₀).ties) X S.graph hE hC B.refresh S.port_order
      S.degree_bounds.2 c)⟩

end CompressorRecords.RefreshCore

end

end VPVNP
end Computability
end OAI
