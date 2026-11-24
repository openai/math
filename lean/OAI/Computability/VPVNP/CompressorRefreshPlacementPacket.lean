import OAI.Computability.VPVNP.CompressorRefreshPlacementTrace
import OAI.Computability.VPVNP.CompressorRefreshLevelDirectory
import OAI.Computability.VPVNP.CompressorBlockHeadWindows
import OAI.Computability.VPVNP.CompressorRefreshTraversalHeaders
import OAI.Computability.VPVNP.CompressorBlockCapacity

/-!
# The selected refresh placement packet

The fourth refresh window fills three consecutive arrays in table four.
The old scalar header gives the number of sites and its native table-head
bank gives the base. The output identifies the singleton preimages of the
selected term and retains the headers and controller words.
-/

namespace OAI
namespace Computability
namespace VPVNP

noncomputable section

namespace CompressorRecords.RefreshPlacement

open BurstRAM BlockPlanner Compression Compression.DegreeRefresh
open DescriptorSpace PhaseRecipe Schedule SourceTransport SourceOnline
open PairSimulation.TraversalRows
open scoped Fin.CommRing

variable {k : Type*} [_root_.Field k] {S : BlockSchedule k} (B : S.Templates)
variable {g w : ℕ} (base : Word w) (positions blocks t : ℕ)

/-- The refresh pass that installs the singleton immediate-preimage directory in table four of
the refresh level. -/
abbrev stage := BlockProgram.refreshPlacement S.steps (BlockProgram.arena B S.steps 4)

/-- Occurrence of the singleton-directory scan in the compiled block. -/
def window : Window (BlockProgram.script B) [stage B] := BlockGroups.refresh B 3

local notation "scr" => BlockProgram.script B
local notation "L" => BlockProgram.layout B base.val positions blocks
local notation "pt" => Workspace.ports (arity (Script.catalog scr)) base
local notation "pub" => Schedule.Ports.data pt
local notation "first" => Script.levelsPerBlock scr * t
local notation "cur" => (first) + S.steps
local notation "st" => (levelStart L (first) : Word w)
local notation "H" => levelStart L 0
local notation "D" => Window.operandRegion scr L base
local notation "start" => tableBase L (cur) (4 : Fin 6)
local notation "V" => stage B
local notation "W" => window B

private theorem space {N : ℕ} (hN : N ≤ positions) (live : t < blocks)
    (fit : endAddress L < 2 ^ w) :
    start + 3 * N ≤ levelStart L (cur + 1) ∧ levelStart L (cur + 1) < 2 ^ w := by
  have size : 3 * N ≤ tableWords L := by
    rw [Nat.mul_comm]
    change N * 3 ≤ positions * (L).shape.slots * (L).shape.fields
    rw [Nat.mul_assoc]
    exact Nat.mul_le_mul hN (BlockProgram.field_rates B base.val positions blocks).2.2.2
  have active : cur + 1 ≤ (L).levels := by
    have bound := Nat.mul_le_mul_left (S.steps + 1) live
    change (S.steps + 1) * t + S.steps + 1 ≤ 1 + (S.steps + 1) * blocks
    rw [Nat.mul_succ] at bound; omega
  exact ⟨(Nat.add_le_add_left size _).trans (tableEnd_le_nextLevel L (cur) (4 : Fin 6)),
    (levelStart_mono L active).trans_lt fit⟩

/-- The packed owner column is beyond the metadata publishers' header cells
and the row array ends before the successor header. -/
theorem packed_geometry (N : ℕ) (size : N ≤ positions) (live : t < blocks)
    (fit : endAddress L < 2 ^ w) (one : 1 < 2 ^ w) :
    let p := packed w start N
    levelStart L (cur) + 28 ≤ (p 1).val ∧ (p 5).val + (p 2).val ≤ levelStart L (cur + 1) := by
  intro p
  obtain ⟨span, next⟩ := space B base positions blocks t size live fit
  obtain ⟨_, owner, count, _, _, row⟩ := packed_values (span.trans_lt next) one
  rw [show p = packed w start N from rfl, owner, count, row]
  have header : levelHeaderWords L = 66 := rfl
  constructor
  · unfold tableBase arrayBase incidenceStart; omega
  · omega

open private field from OAI.Computability.VPVNP.CompressorBlockHeadReads

/-- The native singleton-row run together with the reads of its physical planner. -/
theorem raw (N : ℕ) (m : Memory w) (entry : LevelFields.Entry L (first) pub st m)
    (room : levelStart L (cur) + 66 ≤ 2 ^ w) (fit : start + 3 * N < 2 ^ w)
    (count : (LevelFields.sites S.steps).eval pub st m = (N : Word w))
    (arena : (BlockProgram.arena B S.steps 4).eval pub st m = (start : Word w)) :
    Window.Raw (A := scr) L base t 13 V m (log (packed w start N) 0 N) := by
  let p := packed w start N
  have args : (fun j => ((V).params j).eval pub st m) = bank p := by
    funext j
    fin_cases j
    · exact arena
    · change (BlockProgram.arena B S.steps 4).eval pub st m +
        (LevelFields.sites S.steps).eval pub st m = ((start + N : ℕ) : Word w)
      rw [arena, count, Nat.cast_add]
    · change (BlockProgram.arena B S.steps 4).eval pub st m +
        (2 : Word w) * (LevelFields.sites S.steps).eval pub st m =
        ((start + 2 * N : ℕ) : Word w)
      rw [arena, count, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
  have ss : (V).stop.eval pub st m = (N : Word w) := count
  have rs := packed_log_access fit (Nat.zero_add N).le
  have low : H ≤ start := (levelStart_mono L (Nat.zero_le (cur))).trans (by
    unfold tableBase arrayBase incidenceStart; omega)
  have fuel : HeaderPacket.Run L pub st V m (log p 0 N) 13 (List.replicate N []) := by
    refine ⟨by decide, ?_, ?_, fun a v hv => (rs.1 a v hv).elim,
      fun a v hv => low.trans (rs.2 a v hv).1⟩
    · dsimp only
      rw [args]
      exact run p 0 N m
    · rw [ss]
      change Progress (N : Word w) ((0 : ℕ) : Word w) _
      simpa only [Nat.zero_add] using log_progress p 0 N (by omega)
  have sites : (LevelFields.sites S.steps).ReadsFrom D pub st m :=
    ⟨field entry room 0 (by decide),
      field entry room 2 (by decide)⟩
  have table : (BlockProgram.arena B S.steps 4).ReadsFrom D pub st m :=
    field entry room 64 (by decide)
  refine ⟨13, List.replicate N [], le_rfl, fuel, ⟨trivial, sites, ?_⟩⟩
  intro j
  fin_cases j
  · exact table
  · exact ⟨table, sites⟩
  · exact ⟨table, trivial, sites⟩

variable {R : Type*} [CommRing R] (f : B.Entry → R) (hf : B.IsSolution f)
variable (X : State S.portExponent (S.portExponent + g))
variable (c : Compression.Refresh.DyadicRefreshChoice X S.graph (Nat.two_pow_pos _)
  (S.port_bound.connected_and_pos S.port_order).1 B.refresh) (sel : List Bool)

/-- The chosen pass with its actual promoted port order and branch selector. -/
abbrev selectedLevel : SelectedLevel B f hf :=
  ⟨_, _, _, _, X, _, PassOrigin.refresh (B := B) (f := f) (hf := hf) X, c, sel⟩

local notation "level" => selectedLevel B f hf X c sel
local notation "heads" => PortRefresh.TraversalHeaders.HeadBank
local notation "data" => packed w start X.positions
local notation "trace" => log data 0 X.positions

/-- Metadata offsets six through eleven name the six words of the
physical preimage directory, in the order used by the DFS handler. -/
theorem metadata_values (m : Memory w) (dH : ℕ)
    (entry : LevelFields.Entry L (first) pub st m)
    (header : LevelFields.Published L (cur) level dH m)
    (pointers : heads L (cur) (level).oldSlots m)
    (room : levelStart L (cur) + 66 ≤ 2 ^ w) :
    let vals := BlockMetadata.fieldExprs (L).shape S.steps B.recordLimit (slotDegree S)
      (.refresh S.steps (BlockProgram.arena B S.steps 4))
    let ev := fun j : Fin 12 => (vals j).eval pub st m
    ev 6 = data 0 ∧ ev 7 = data 2 ∧ ev 8 = data 1 ∧ ev 9 = data 3 ∧ ev 10 = data 5 ∧
      ev 11 = data 4 := by
  intro vals ev
  have n := (LevelFields.eval_dimensions entry header).1
  have a : (BlockProgram.arena B S.steps 4).eval pub st m = (start : Word w) :=
    (LevelFields.eval_scalar entry S.steps 64 (by omega)).trans (pointers.tables (4 : Fin 6))
  refine ⟨n, n, a, ?_, ?_, rfl⟩
  · change (BlockProgram.arena B S.steps 4).eval pub st m +
      (LevelFields.sites S.steps).eval pub st m = ((start + X.positions : ℕ) : Word w)
    rw [a, n, Nat.cast_add]
  · change (BlockProgram.arena B S.steps 4).eval pub st m +
      (LevelFields.sites S.steps).eval pub st m + (LevelFields.sites S.steps).eval pub st m =
      ((start + 2 * X.positions : ℕ) : Word w)
    rw [a, n, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]; ring

/-- The online group uses the complete native scan. In its output memory the
traversal can read the chosen term's directory with the exact packed bases.
The frame states which cells are available to every subsequent group. -/
theorem install (cap : ℕ) (m : Memory w) (live : t < blocks) (size : X.positions ≤ positions)
    (fit : endAddress L < 2 ^ w) (rows : m (pt).rows.val = (directoryRows L : Word w))
    (pitch : m (pub 1 - 1).val = (levelWords L : Word w)) (clock : scanCap scr 13 ≤ cap)
    (dH : ℕ) (header : LevelFields.Published L (cur) level dH m)
    (pointers : heads L (cur) (level).oldSlots m) :
    ∃ ps : List (SourceOnline.Packet scr w),
      Group scr L base cap ((scr).initial.length + t * (scr).block.length + (W).before.length)
        (directoryRows L) m ps ∧
      ps.map (fun p => p.stage.phase) = (W).indices ∧
      ps.flatMap SourceWalk.Packet.reports = trace ∧
      (∃ dir : LevelDirectory level (post m ps) (levelStart L (cur + 1)),
        dir.pub = data) ∧
      LevelFields.Published L (cur) level dH (post m ps) ∧
      heads L (cur) (level).oldSlots (post m ps) ∧
      (∀ x, x < start ∨ start + 3 * X.positions ≤ x → post m ps x = m x) := by
  obtain ⟨endBound, nextFit⟩ := space B base positions blocks t size live fit
  have fit₃ := endBound.trans_lt nextFit
  have hdrFit := PublishedHeads.level_room B base positions blocks t S.steps live le_rfl fit
  have entry : LevelFields.Entry L (first) pub st m := ⟨rfl, pitch⟩
  have sites := (LevelFields.eval_dimensions entry header).1
  have arena : (BlockProgram.arena B S.steps 4).eval pub st m = (start : Word w) :=
    (LevelFields.eval_scalar entry S.steps 64 (by omega)).trans (pointers.tables (4 : Fin 6))
  have rawRun := raw B base positions blocks t X.positions m entry hdrFit fit₃ sites arena
  have rawWalk : SourceWalk (Window.Raw (A := scr) L base t 13) [V] m trace := by
    simpa only [List.append_nil] using SourceWalk.next rawRun (SourceWalk.done _)
  have budgets (j : Fin (scr).size) :
      ((scr).plan.recipes j).2.code.length + 1 + 2 * Online.N (scr).size (scr).size + 5 ≤ cap ∧
      13 + 3 + 4 * (((scr).catalog j).params + 1) + 2 * Online.N (scr).size (scr).size + 5 ≤
        cap := by
    let p := HeaderPacket.attach scr j pub st m 13 (List.replicate X.positions [])
    exact SourceOnline.scanCap_clocks (p := ⟨p, m, []⟩) 13 le_rfl clock
  obtain ⟨ps, group, phases, logs⟩ := (W).group L base t rfl rfl
    ((levelStart_mono L (Nat.zero_le (L).levels)).trans_lt fit) cap 13 m trace rawWalk rows pitch
    (PublishedHeads.windowLive B base positions blocks t W live)
    (fun j _ => (budgets j).1) (fun j _ => (budgets j).2)
  have same : post m ps = after m (eventLog trace) := by rw [post, logs]
  have access := packed_log_access fit₃ (Nat.zero_add X.positions).le
  have frame (x : ℕ) (outside : x < start ∨ start + 3 * X.positions ≤ x) :
      post m ps x = m x := by
    rw [same]
    exact after_outside _ access.2 (by omega)
  have old (n : ℕ) (hn : n < levelHeaderWords L) :
      post m ps (levelStart L (cur) + n) = m (levelStart L (cur) + n) := by
    apply frame _ (.inl ?_)
    unfold tableBase arrayBase incidenceStart; omega
  have len : levelHeaderWords L = 66 := rfl
  have kept : LevelFields.Published L (cur) level dH (post m ps) :=
    ⟨header.room, (old 0 (by omega)).trans header.vertices, (old 1 (by omega)).trans header.degree,
      (old 2 (by omega)).trans header.lanes, (old 3 (by omega)).trans header.residual,
      (old 4 (by omega)).trans header.nextDegree, (old 5 (by omega)).trans header.expander⟩
  refine ⟨ps, group, phases, logs, ?_, kept, pointers.keep old, frame⟩
  rw [same]
  have one : 1 < 2 ^ w := by omega
  obtain ⟨h₀, _, h₂, _, h₄, h₅⟩ := packed_values fit₃ one
  exact ⟨directory f hf X c sel data m (levelStart L (cur + 1)) (packed_regions fit₃) h₀ h₂ h₄
    (by rw [h₅, h₂]; omega), rfl⟩

end CompressorRecords.RefreshPlacement

end

end VPVNP
end Computability
end OAI
