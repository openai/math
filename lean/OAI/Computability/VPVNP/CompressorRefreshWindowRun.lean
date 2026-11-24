import OAI.Computability.VPVNP.CompressorRefreshCoreHeader
import OAI.Computability.VPVNP.CompressorRefreshVerifiedStages
import OAI.Computability.VPVNP.CompressorBlockGroups
import OAI.Computability.VPVNP.CompressorWindowPackets
import OAI.Computability.VPVNP.CompressorSourceScanned

/-!
# Selected native reports for the full expander-refresh window

At each chronological worker, the six input formulas read the previously
published counts and pointer bank. Its source program uses the same words
as the expander - refresh construction. Its stores are confined to the new
arrays, retaining the header for the next worker in the window.
-/

namespace OAI
namespace Computability
namespace VPVNP

noncomputable section

set_option quotPrecheck false

namespace CompressorRecords.RefreshCore

open BurstRAM Compression Compression.DegreeRefresh Compression.Refresh
open PortRefresh PortRefresh.LevelRecipe PhaseRecipe BlockPlanner Schedule
open DescriptorSpace SourceTransport NewSlots
open scoped Fin.CommRing

variable {k : Type*} [_root_.Field k] {S : BlockSchedule k} (B : S.Templates)
variable {w g : ℕ} (X : State S.portExponent (S.portExponent + g))
local notation "hd" => S.degree_bounds.2
private abbrev portConnected := (S.port_bound.connected_and_pos S.port_order).1
local notation "hc" => portConnected (S := S)
local notation "sh" => RefreshBlockPlan.shape B
local notation "ties" => RefreshBlockPlan.order B
local notation "I" => RefreshBlockPlan.input (BlockProgram.geometry B) S.steps (0 : Fin 6)
local notation "scr" => BlockProgram.script B

private theorem fuel_bounds {s : LevelRecipe.Shape} (d : s.dH + 1 ≤ s.degree) {cap : ℕ}
    (pos : 0 < cap)
    (j : Stage s) : 0 < Scheduled.fuel d cap j ∧ Scheduled.fuel d cap j ≤ max 64 cap := by
  cases j with
  | term => exact ⟨pos,Nat.le_max_right ..⟩
  | slot k =>
    change 0 < 1 + (code (kindOf ((refreshSlots d).symm k))).length ∧
      1 + (code (kindOf ((refreshSlots d).symm k))).length ≤ max 64 cap
    exact ⟨by omega,(by cases kindOf ((refreshSlots d).symm k) <;> decide :
      1 + (code (kindOf ((refreshSlots d).symm k))).length ≤ 64).trans (Nat.le_max_left ..)⟩
  | _ => simp only [Scheduled.fuel]; omega

variable (c : DyadicRefreshChoice X S.graph (Nat.two_pow_pos _)
  (S.port_bound.connected_and_pos S.port_order).1 B.refresh)
variable (old : IncidenceDirectory w) (start cap : ℕ)
local notation "p" => Allocation.plan X (sh).a₀ (sh).dH (sh).ties (sh).stride start
local notation "native" => Scheduled.Source X S.graph (Nat.two_pow_pos _) hc B.refresh hd c ties
  old start (sh).stride cap
local notation "region" => TermDataFrame.InArena p
local notation "bounds" => Scheduled.StageBounds (t := (sh).ties) X S.graph
  (Nat.two_pow_pos _) hc B.refresh start (sh).stride

/-- An actual worker run with the tape supplied for this calendar stage. -/
def StageRun (j : Stage sh) (bits : List (List Bool)) (m : Memory w) (rs : List
    (Report w)) : Prop :=
  let term := RefreshBlockPlan.term B
  let data := fun i ↦ j.nativeBank hd S.graph ties X start old
    (TermWorker.motifData B.refresh ties finProdFinEquiv.symm w) (Fin.cast
      (j.worker_params hd term) i)
  runSegment ((j.worker hd term).table.instantiate w data).program (Scheduled.fuel hd cap j)
    (some (word j.first)) m bits = some rs

variable (base : BurstRAM.Word w) (positions blocks t : ℕ)
local notation "L" => BlockProgram.layout B base.val positions blocks
local notation "pt" => Workspace.ports (arity (Script.catalog scr)) base
local notation "pub" => Schedule.Ports.data pt
local notation "firstLevel" => Script.levelsPerBlock scr * t
local notation "st" => (levelStart L firstLevel : BurstRAM.Word w)
local notation "head" => levelStart L (firstLevel + S.steps)
local notation "H" => levelStart L 0
local notation "D" => Window.operandRegion scr L base
local notation "R" => Window.Raw (A := scr) L base t (max 64 cap)

set_option maxHeartbeats 800000 in
-- The native bank and compiled bank have dependent arities in each of the nine cases.
private theorem stage_raw (bits : List (List Bool)) (m : Memory w) (rs : List (Report w))
    (j : Stage sh)
    (h : Header (Fintype.card X.Base) g head start old m)
    (pitch : m ((pt).directory - 1).val = (levelWords L : BurstRAM.Word w))
    (pos : 0 < cap) (room : (p).stop < 2 ^ w) (low : H ≤ start)
    (r : StageRun B X old start cap j bits m rs) (b : bounds H j m rs) : R
      (RefreshBlockPlan.stage B I j) m rs := by
  let C : Context w := ⟨pub,st,m⟩
  have entry : LevelFields.Entry L firstLevel C.pub C.state C.memory := ⟨rfl,pitch⟩
  have describes : Describes (s := sh) I C X start old := Header.describes
    (F := BlockProgram.geometry B) (s := sh) (X := X) (step := S.steps) rfl (0 : Fin 6) rfl entry h
  have support : InputReads D C.pub C.state C.memory I := Header.reads (F := BlockProgram.geometry
    B) (step := S.steps) rfl (0 : Fin 6) rfl entry h
    (.inr (.inl rfl)) (fun n _ ↦ .inr (.inr ((levelStart_mono L (Nat.zero_le _)).trans
      (Nat.le_add_right ..))))
  have ec := counters I C X start old describes j
  have eb := motif_workerBank_eq I hd S.graph ties C X start old (Nat.two_pow_pos _) hc B.refresh
    describes j
  let data := fun i ↦ j.nativeBank hd S.graph ties X start old
    (TermWorker.motifData B.refresh ties finProdFinEquiv.symm w) (Fin.cast (j.worker_params hd
      (RefreshBlockPlan.term B)) i)
  have bank : (fun i ↦ C.eval ((RefreshBlockPlan.stage B I j).params i)) = data := funext eb
  have fuel := fuel_bounds hd pos j
  refine ⟨Scheduled.fuel hd cap j,bits,fuel.2,⟨fuel.1,?_,?_,b.2.1,?_⟩,stage_supported D pub st m B
    support j⟩
  · change runSegment (((RefreshBlockPlan.stage B I j).worker.table.instantiate w
      (fun i ↦ C.eval ((RefreshBlockPlan.stage B I j).params i))).program) _ (some
        (C.eval j.initial)) m bits = some rs
    rw [bank,ec.1]
    exact r
  · change SourceOnline.Progress (C.eval (j.stop I)) (C.eval j.initial) rs
    rw [ec.1,ec.2]
    have fit := limit_fits (s := sh) (w := w) (g := g) hd X start room.le j
    exact b.1.toProgress fit
  · exact fun a v ha ↦ low.trans (b.2.2 a v ha).1

set_option maxHeartbeats 800000 in
-- The induction threads the full typed layout and the worker index through each stage.
/-- Transform the verified chronological native execution into the actual
worker recipes. The entire interval writes only the allocated refresh arena. -/
theorem raw_stages (bits : Stage sh → List (List Bool)) (js : List (Stage sh)) (m : Memory w)
    (rs : List (Report w))
    (header : Header (Fintype.card X.Base) g head start old m)
    (pitch : m ((pt).directory - 1).val = (levelWords L : BurstRAM.Word w)) (pos : 0 < cap)
    (room : (p).stop < 2 ^ w) (before : head + 60 < start) (fit : H < 2 ^ w)
    (run : SourceWalk (fun j mem logs ↦ StageRun B X old start cap j (bits j) mem logs
      ∧ bounds H j mem logs) js m rs) :
    SourceWalk R (js.map (RefreshBlockPlan.stage B I)) m rs ∧ Writes region (eventLog rs) := by
  have below := Window.lowCells (A := scr) L base rfl rfl fit
  have hhead := levelStart_mono L (show 0 ≤ firstLevel + S.steps from Nat.zero_le _)
  have low : H ≤ start := by omega
  have loop (js : List (Stage sh)) (mem : Memory w) (logs : List (Report w))
      (walk : SourceWalk (fun j u ls ↦ StageRun B X old start cap j (bits j) u ls
        ∧ bounds H j u ls) js mem logs)
      (hh : Header (Fintype.card X.Base) g head start old mem)
      (hp : mem ((pt).directory - 1).val = (levelWords L : BurstRAM.Word w)) :
      SourceWalk R (js.map (RefreshBlockPlan.stage B I)) mem logs ∧ Writes region
        (eventLog logs) := by
    induction walk with
    | done => exact ⟨.done _,fun _ _ h ↦ by cases h⟩
    | @next j js u xs ys h _ ih =>
      have w₀ := h.2.2.2
      have keep (addr : ℕ) (lt : addr < start) : after u (eventLog xs) addr = u addr :=
        after_outside u w₀ (fun inside ↦ (Nat.not_le_of_lt lt) inside.1)
      have next := ih (hh.keep (fun i hi ↦ keep _ (by omega))) ((keep _
        (below.2.trans_le low)).trans hp)
      refine ⟨.next (stage_raw B X old start cap base positions blocks t
        (bits j) u xs j hh hp pos room low h.1 h.2) next.1,?_⟩
      intro a v h
      simp only [eventLog,List.flatMap_append,List.mem_append] at h
      exact h.elim (w₀ a v) (next.2 a v)
  exact loop _ _ _ run header pitch

theorem raw_window (m : Memory w) (rs : List (Report w))
    (header : Header (Fintype.card X.Base) g head start old m)
    (pitch : m ((pt).directory - 1).val = (levelWords L : BurstRAM.Word w)) (pos : 0 < cap)
    (room : (p).stop < 2 ^ w) (before : head + 60 < start) (fit : H < 2 ^ w)
    (run : SourceWalk (fun j mem logs ↦ native j mem logs ∧ bounds H j mem logs) (order sh) m rs) :
    SourceWalk R ((order sh).map (RefreshBlockPlan.stage B I)) m rs ∧ Writes region (eventLog rs) :=
  raw_stages B X old start cap base positions blocks t
    (Scheduled.tapes (t := (sh).ties) (w := w) X S.graph (Nat.two_pow_pos _) hc B.refresh c start
      (sh).stride)
    (order sh) m rs header pitch pos room before fit run

end CompressorRecords.RefreshCore

end

end VPVNP
end Computability
end OAI
