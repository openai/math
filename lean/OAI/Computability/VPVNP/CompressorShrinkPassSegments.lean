import OAI.Computability.VPVNP.CompressorPacketPassRun
import OAI.Computability.VPVNP.CompressorNativePassRates
import OAI.Computability.VPVNP.CompressorShrinkScheduledRunRate
import OAI.Computability.VPVNP.CompressorShrinkFinishedResident
import OAI.Computability.VPVNP.CompressorShrinkSourceWorker
import OAI.Computability.VPVNP.CompressorCanonicalNativeTapes
import OAI.Computability.VPVNP.CompressorScheduledPassCases
import OAI.Computability.VPVNP.CompressorPassWindowBounds

/-! # A physical shrinking pass on the concrete resident graph

The default term supplies the common deterministic prefix and its actual
post-gather input. Each selected term supplies its own source packet and
suffix, which publish the chosen preimage history and successor incidence
columns. The source and live executions have the same selected state.
-/

namespace OAI
namespace Computability
namespace VPVNP

noncomputable section

namespace CompressorRecords.ShrinkScheduledRun

open BurstRAM Compression ShrinkBlockInputs BlockPlanner DescriptorSpace
open SourceOnline SourceTransport
open PairSimulation.LocalHistory PairSimulation.TraversalRows PairSimulation.TraversalRoles
open ShrinkOutput ScheduledTrace PassTimeline Schedule
open scoped Fin.CommRing

variable {k R : Type*} [_root_.Field k] [CommRing R] {S : BlockSchedule k}
  (B : S.Templates) (f : B.Entry → R) (hf : B.IsSolution f) (i : Fin S.steps)
  {g w : ℕ} (X : GreedyArena.ShrinkingState (a i) g) (pub : Fin 11 → Word w)
  (positions blocks round n : ℕ) (live : round < blocks) (initial : TaggedLayer)
  (initialFrame : Fin 8 → Word w)
  (fuel cap small refreshRate : ℕ) (past : List (SelectedLevel B f hf)) (m : Memory w)
  (encode : SelectedScore.Selection B X → List Bool)
set_option quotPrecheck false
local notation "base" => pub 2
local notation "layout" => BlockProgram.layout B (Fin.val (pub 2)) positions blocks
local notation "script" => BlockProgram.script B
local notation "loc" => (⟨round, .shrink i⟩ : Located S.steps)
local notation "o" => (PassOrigin.shrink i rfl X : PassOrigin B f hf (B.shrinkPassAt f hf i rfl X))
local notation "src" => old B i (Fin.val (pub 2)) positions blocks round live
local notation "dst" => next B i (Fin.val (pub 2)) positions blocks round live
local notation "inc" => packedIncidence layout w src (DemandRAM.oldCount X)
local notation "begin" => tableBase layout src (0 : Fin 6)
local notation "total" => directoryRows layout
local notation "resident" =>
  CompiledResident.resident B f hf (pub 2) positions blocks n initial initialFrame
local notation "rawRate" => commonRawRate (fixedRate B) refreshRate
local notation "rate" => nativePassRate (BlockProgram.script B) rawRate * positions
local notation "Choice" => SelectedScore.Selection B X
local notation "pkt" => SourceOnline.Packet script w
local notation "pt" => Workspace.ports (arity (BlockProgram.script B).catalog) (pub 2)

private theorem slot_count_le {c h : ℕ} {Y : State c h} (bound : Y.positions ≤ positions)
    (degree : 2 ^ c ≤ slotDegree S) :
    IncidenceDirectory.slotCount Y ≤
      slotCapacity (BlockProgram.layout B (Fin.val (pub 2)) positions blocks) := by
  have eqn : Y.positions = Fintype.card Y.Base * 2 ^ h := by
    simp [State.positions, BitWord]
  change Fintype.card Y.Base * 2 ^ h * 2 ^ c ≤ positions * slotDegree S
  rw [← eqn]
  exact Nat.mul_le_mul bound degree

private theorem block_degree (j : Fin (S.steps + 1)) : 2 ^ S.degreeExponent j ≤ slotDegree S :=
  (Finset.le_sup (f := fun x : Fin (S.steps + 1) => 2 ^ S.degreeExponent x)
    (Finset.mem_univ j)).trans (le_max_right ..)

set_option maxHeartbeats 2400000 in
-- Checking the dependent source windows and both resident memories exceeds the default budget.
set_option maxRecDepth 5000 in
/-- The real selected packet groups, fixed inner clocks and word geometry
construct the shrinking case of the scheduled execution. -/
theorem ofSources
    (common : ShrinkCurrentBranch.Common B f hf i X base positions blocks src dst m fuel)
    (fits : ShrinkBranch.PrefixFits B X inc begin (10 : Word w) fuel)
    (index : past.length = (src).val) (size : X.positions ≤ positions)
    (room : endAddress layout < 2 ^ w)
    (width : SelectedTermWorker.fitConstant B + 4 * Nat.clog 2 (X.maxWireWidth + 1) ≤ w)
    (clock : small ≤ cap) (large : Online.Run.ControlBounds (script).plan cap (w := w))
    (little : Online.Run.ControlBounds (script).plan small (w := w))
    (ready : ScheduledTrace.Boundary resident pub (levelWords layout : Word w) total
      ((loc).first B) past X m)
    (pre : Choice → List pkt) (marker : Choice → pkt)
    (geom p₅ p₆ p₇ p₈ ms tail : Choice → List pkt) (tables : Choice → TablesRun w)
    (result : ∀ s, Result B i positions blocks round live f hf X base m fuel small common s
      (encode s) (pre s) (marker s) (geom s) (p₅ s) (p₆ s) (p₇ s) (p₈ s) (ms s) (tail s)
      (tables s)) :
    Nonempty (ScheduledTrace.PassRun resident pub (levelWords layout : Word w) total cap small rate
      loc o encode past m) := by
  classical
  let d := defaultSelection o
  let posts (s : SelectedScore.Selection B X) :=
    geom s ++ ((((p₅ s ++ p₆ s) ++ p₇ s) ++ p₈ s) ++ tail s)
  let ord := ShrinkForward.first B i round
  have hd := (result d).geometry
  have hpre : (pre d).length = 21 := hd.prefixLength
  have ordEq : (loc).first B = ord := rfl
  have lastLen (s) : (loc).first B + (pre d).length + 1 + (posts s).length = (loc).finish B := by
    rw [hpre]
    have e := (result s).suffixLength
    change 22 + (posts s).length = (BlockProgram.shrink B i).length at e
    change _ = (loc).first B + (BlockProgram.shrink B i).length
    omega
  have endFits : (loc).finish B ≤ total := by
    rw [BlockProgram.directory_rows]
    exact (loc).finish_le_calendar B live
  have preFits : (loc).first B + (pre d).length < total := by have e := lastLen d; omega
  let worker := ShrinkCurrentBranch.workerInput B f hf i X inc begin fuel common.pre fits
  have floor : levelStart layout 0 ≤ begin := by
    have lower := levelStart_mono layout (Nat.zero_le (src).val)
    unfold tableBase arrayBase incidenceStart; omega
  have matchMarker : marker d = ShrinkTermOnline.packet B i X inc begin d fuel .select
      common.pre.beforeTerm (marker d).reports := by
    have inputEq : (marker d).input = common.pre.beforeTerm := hd.selectInput
    rw [← inputEq]
    simp only [ShrinkTermOnline.packet, ← hd.selectStage]
  have physical : ScheduledTrace.SelectorSite.SourceWorker worker layout (marker d) := by
    rw [matchMarker]
    exact ShrinkCurrentBranch.sourceWorker B f hf i X inc begin fuel common.pre fits layout d
      (marker d).reports floor width
  refine ScheduledTrace.PassRun.ofPacketGroups (B := B) (f := f) (hf := hf)
    (p := B.shrinkPassAt f hf i rfl X)
    («o» := o) («resident» := resident) («loc» := loc) (L := layout) (pub := pub)
    (past := past) (m := m) (raw := m)
    (encode := encode) (cap := cap) (small := small) («total» := total) («rate» := rate)
    (pre d) marker posts hd.prefixGroup
    (fun s => ?_) (fun s => ?_) (fun q hq => List.eq_replicate_length.mpr (hd.prefixEmpty q hq))
    (fun s q hq => List.eq_replicate_length.mpr ((result s).quiet q hq))
    (fun s => ((result s).geometry.selectChoices).trans
      (congrArg List.ofFn (CanonicalWorker.shrink_tapes B f hf i X s w)))
    clock large little rfl rfl
    (lt_of_le_of_lt (levelStart_mono layout (Nat.zero_le (layout).levels)) room)
    preFits endFits lastLen le_rfl (fun _ _ => rfl) ready worker
    physical
    (fun s => ?_) (fun s u v agree stored => ?_) (fun s => ?_)
  · rw [ordEq, hpre, hd.prefixPost]
    dsimp only [ord, ShrinkForward.first]
    exact (result s).geometry.selected
  · rw [ordEq, hpre]
    exact (result s).suffix
  · dsimp only [posts]
    rw [(result s).final]
    exact (result s).finish.advance (Classical.choice (common.selected s)) live size room src dst
      rfl rfl index
      ready.stored (common.header s (encode s)) (result s).geometry.frame
  · have ix : (past ++ [ScheduledTrace.level o encode s]).length < (layout).levels := by
      simp only [List.length_append, List.length_singleton, index]
      exact (dst).isLt
    have outSize := ((o).next_positions_le s).trans size
    exact DetailedResident.transfer stored ix room (by change 14 ≤ 54; decide)
      (slot_count_le (B := B) (pub := pub) (positions := positions) (blocks := blocks)
        outSize (block_degree i.succ)) agree
  · have ch := Result.rate_shared (B := B) (common := common) (sel := s) (other := d)
      (result s) (result d)
    have coef := rawRate_le (PassTimeline.Pass.shrink i) (fixedRate B) refreshRate
    have larger : rawRate ≤ nativePassRate script rawRate := by
      unfold nativePassRate
      have pos : 0 < arity (script).catalog + 3 := Nat.zero_lt_succ _
      exact (Nat.le_mul_of_pos_right _ pos).trans (Nat.le_add_right ..)
    exact ch.trans ((Nat.mul_comm X.positions (fixedRate B i)).le.trans
      (Nat.mul_le_mul (coef.trans larger) size))

end CompressorRecords.ShrinkScheduledRun

end

end VPVNP
end Computability
end OAI
