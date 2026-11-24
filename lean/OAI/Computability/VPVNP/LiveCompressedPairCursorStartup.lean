import OAI.Computability.VPVNP.LiveProgramCompressedPair
import OAI.Computability.VPVNP.CompressorTransferredStartup
import OAI.Computability.VPVNP.LiveStageSegments

/-!
# Executing the compressed pair's native startup stages

Each initializer reads the memory left by the preceding linked call, including
the enclosing stage tag. A successful initializer hands off at cursor zero.
Their concatenation gives the deterministic prefix of every accepting pair
path and the actual memory passed to the online descriptor calendar.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace LiveProgram.CompressedPair

open BurstRAM BurstRAM.PrivateRAM CompressorRecords CompressorRecords.Schedule
open scoped Fin.CommRing

variable {w : ℕ}

/-- Concatenate a fixed number of verified calls whose persistent return is zero. -/
private theorem calls {Q : Type*} (P : BurstRAM.Program w Q) (cap k : ℕ)
    (entry : Fin (k+1) → Memory w) (rs : Fin k → Report w)
    (run : ∀ i, execute P cap (P.start 0) (entry i.castSucc) [] = some (rs i))
    (state : ∀ i, (rs i).result = some 0)
    (memory : ∀ i, after (entry i.castSucc) (rs i).events = entry i.succ) :
    runSegment P cap (some 0) (entry 0) (List.replicate k []) = some (List.ofFn rs) ∧
      endState (some 0) (List.ofFn rs) = some 0 ∧
      after (entry 0) (eventLog (List.ofFn rs)) = entry (Fin.last k) := by
  induction k with
  | zero => simp [runSegment, endState, eventLog, after]
  | succ k ih =>
    obtain ⟨rt, st, mt⟩ := ih (fun j => entry j.succ) (fun i => rs i.succ)
      (fun i => run i.succ) (fun i => state i.succ) (fun i => memory i.succ)
    have r0 := run 0
    have m0 := memory 0
    change execute P cap (P.start 0) (entry 0) [] = some (rs 0) at r0
    change after (entry 0) (rs 0).events = entry (0 : Fin (k+1)).succ at m0
    rw [List.ofFn_succ, List.replicate_succ, runSegment, r0]
    simp only [state, m0, rt, Option.map_some, endState, st, true_and]
    change after (entry 0) ((rs 0).events ++ eventLog _) = _
    rw [show ∀ m : Memory w, ∀ es fs, after m (es++fs) = after (after m es) fs from
      fun _ _ _ => List.foldl_append, m0]
    exact mt

variable {d initial phases : ℕ} {C : Catalog d} (b : Bootstrap)
    (plan : Online.Config C initial phases) (terminal : PairTable) (pub : Fin 11 → Word w)

/-- Link a sequence of accepting component calls on its actual successive
memories. Each handoff returns cursor zero and installs the destination tag.
The probe count includes both the tag lookup and the transfer. -/
theorem linked_startup {k : ℕ} (stage : Fin (k+1) → Stage)
    (source : Fin k → Report w) (fuel : Fin k → ℕ) (entry : Fin (k+1) → Memory w)
    (cap : ℕ) (fit : 10 ≤ 2^w) (clock : ∀ i, fuel i+30 ≤ cap)
    (step : ∀ i : Fin k, next (stage i.castSucc) = some (stage i.succ))
    (tag : ∀ i : Fin k, entry i.castSucc (PairTag.address pub).val = LiveStageLink.tagWord w (stage i.castSucc))
    (closed : ∀ i, (source i).result = none)
    (run : ∀ i, let S := original b plan terminal pub (stage i.castSucc)
      execute S (fuel i) (S.start 0) (entry i.castSucc) [] = some (source i))
    (transfer : ∀ i, writeMemory (after (entry i.castSucc) (source i).events)
      (PairTag.address pub) (LiveStageLink.tagWord w (stage i.succ)) = entry i.succ) :
    let rs := fun i : Fin k => report pub (stage i.castSucc) (source i)
    runSegment (program b plan terminal pub) cap (some 0) (entry 0) (List.replicate k []) =
      some (List.ofFn rs) ∧ endState (some 0) (List.ofFn rs) = some 0 ∧
      after (entry 0) (eventLog (List.ofFn rs)) = entry (Fin.last k) ∧
      branchPaths (List.ofFn rs) = List.replicate k [] ∧
      ∀ i, (rs i).probes = (source i).probes+2 ∧ (rs i).events.length ≤ (source i).events.length+30 := by
  intro rs
  have run' (i : Fin k) := execute_stage b plan terminal pub (stage i.castSucc) fit
    (fuel i) cap (clock i) 0 (entry i.castSucc) (tag i) [] (source i) (run i)
  have state (i : Fin k) : (rs i).result = some 0 := by
    change (LiveStageLink.linkedReport next (PairTag.address pub) (stage i.castSucc) (source i)).result = _
    rw [LiveStageLink.linkedReport_result, closed i, step i]
    rfl
  have effects (i : Fin k) := report_effect pub (stage i.castSucc) (source i) (entry i.castSucc)
  have hm (i : Fin k) : after (entry i.castSucc) (rs i).events = entry i.succ := by
    have h := (effects i).2.2.2
    rw [closed i, step i] at h
    exact h.trans (transfer i)
  obtain ⟨hr, hs, he⟩ := calls (program b plan terminal pub) cap k entry rs run' state hm
  refine ⟨hr, hs, he, (runSegment_iff ..).mp hr |>.2.2, fun i => ?_⟩
  have hp := (effects i).2.1
  rw [closed i, step i] at hp
  exact ⟨hp, (effects i).2.2.1⟩

/-- Instruction caps of the eight source calls, in their actual stage order. -/
def sourceFuel (b : Bootstrap) (initial phases n : ℕ) : Fin 8 → ℕ :=
  ![CalendarRows.ticks (OnlineWorkspace.rowsSpec initial phases b.numerator b.denominator) n + 2,
    (DescriptorParameters.raw b.shape b.degreeBits initial phases b.lanesPerBlock).recipe.code.length+1,
    VirtualParameters.ticks n+43+4*17, (DescriptorParameters.copy b.shape).recipe.code.length+1,
    1+DescriptorStride.cost b.shape, 1+HistoryArenaBase.cost b.shape initial phases b.steps, 42, 6]

private theorem clock_bound (D : CalendarRows.Spec) (fixed extra n : ℕ) :
    max (CalendarRows.ticks D n + 2) (max (VirtualParameters.ticks n+43+4*17) fixed) + extra ≤
      (142+6*D.p+fixed+extra)*(n.log2+1) := by
  have count := CalendarRows.ticks_le D n
  have virtual := VirtualParameters.ticks_le n
  have small := clog_le_log2_succ n
  have a : Nat.clog 2 n * D.p ≤ (n.log2+1) * D.p := Nat.mul_le_mul_right _ small
  simp only [Nat.add_mul, Nat.one_mul] at a
  rw [← max_add_add_right, ← max_add_add_right]
  apply max_le _ (max_le _ _)
  all_goals nlinarith
/-- Every startup cap is bounded by a fixed multiple of the logarithm of the
input length, uniformly in the selected stage and in the group. -/
theorem sourceFuel_log (b : Bootstrap) (initial phases extra : ℕ) :
    ∃ K, ∀ n (i : Fin 8), sourceFuel b initial phases n i + extra ≤ K*(n.log2+1) := by
  let D := OnlineWorkspace.rowsSpec initial phases b.numerator b.denominator
  let fixed := max ((DescriptorParameters.raw b.shape b.degreeBits initial phases b.lanesPerBlock).recipe.code.length+1)
    (max ((DescriptorParameters.copy b.shape).recipe.code.length+1)
      (max (1+DescriptorStride.cost b.shape) (max (1+HistoryArenaBase.cost b.shape initial phases b.steps) 42)))
  refine ⟨142+6*D.p+fixed+extra, fun n i => ?_⟩
  apply le_trans _ (clock_bound D fixed extra n)
  dsimp only [fixed]
  fin_cases i
  · change CalendarRows.ticks D n+2+extra ≤ _
    omega
  · change (DescriptorParameters.raw b.shape b.degreeBits initial phases b.lanesPerBlock).recipe.code.length+1+extra ≤ _
    omega
  · change VirtualParameters.ticks n+43+4*17+extra ≤ _
    omega
  · change (DescriptorParameters.copy b.shape).recipe.code.length+1+extra ≤ _
    omega
  · change 1+DescriptorStride.cost b.shape+extra ≤ _
    omega
  · change 1+HistoryArenaBase.cost b.shape initial phases b.steps+extra ≤ _
    omega
  · change 42+extra ≤ _
    omega
  · change 6+extra ≤ _
    omega

/-- The linked prefix fits the private clock for every sufficiently large input. -/
theorem eventually_sourceFuel (b : Bootstrap) (initial phases extra : ℕ) :
    ∀ᶠ n : ℕ in Filter.atTop, ∀ i : Fin 8, sourceFuel b initial phases n i + extra ≤ n := by
  obtain ⟨K, hk⟩ := sourceFuel_log b initial phases extra
  filter_upwards [eventually_polylog_le K 1] with n h
  exact fun i => (hk n i).trans (by simpa only [pow_one] using h)

private theorem probes_le_length (es : List (Event w)) : countProbes es ≤ es.length := by
  induction es with
  | nil => rfl
  | cons e es ih => cases e <;> simp only [countProbes, List.length_cons] <;> omega

/-- The startup specification for the initial rows and repeated block phases using the
bootstrap's block ratio. -/
abbrev bootstrapRows (b : Bootstrap) (initial phases : ℕ) :=
  OnlineWorkspace.rowsSpec initial phases b.numerator b.denominator

/-- The cursor workspace layout with its directory sized to the exact calendar row count for
this input. -/
noncomputable def startupLayout (b : Bootstrap) (initial phases B n base : ℕ) :=
  LevelFields.tightDirectory (DescriptorSpace.cursorLayout b.shape B b.steps
    ((b.numerator : ℝ)/b.denominator) base n) (CalendarRows.rows (bootstrapRows b initial phases) n)

private def startupStage (i : Fin 9) : Stage := i.castLE (by decide)

variable (B n base : ℕ) (m : Memory w)

/-- The eight transferred initializer calls on the pair's actual tag, public operands, and
input memory. -/
noncomputable abbrev startupTrace (initial phases d : ℕ) := TransferredStartup.trace
  (bootstrapRows b initial phases) d (startupLayout b initial phases B n base) B n
  b.degreeBits b.lanesPerBlock b.steps pub (PairTag.address pub) m

/-- Wrap one initializer's source report with the dispatch and transfer events for its linked
startup stage. -/
noncomputable def startupReport (initial phases d : ℕ) (i : Fin 8) : Report w :=
  report pub (startupStage i.castSucc) ((startupTrace b pub B n base m initial phases d).source i)

/-- The eight linked startup reports in call order, whose combined effects supply the online
calendar's entry memory. -/
noncomputable abbrev cursorStartupLogs (initial phases d : ℕ) :=
  List.ofFn (startupReport b pub B n base m initial phases d)

/-- The original reports with the stage labels used by the live group's
resource accounting. -/
noncomputable def cursorStartupSources (initial phases d : ℕ) : List (Stage × Report w) :=
  List.ofFn fun i : Fin 8 =>
    (startupStage i.castSucc, (startupTrace b pub B n base m initial phases d).source i)

theorem cursorStartupLogs_eq (initial phases d : ℕ) :
    cursorStartupLogs b pub B n base m initial phases d =
      (cursorStartupSources b pub B n base m initial phases d).map (fun p => report pub p.1 p.2) := by
  rw [cursorStartupSources, List.map_ofFn]
  rfl

local notation "D" => bootstrapRows b initial phases
local notation "L" => startupLayout b initial phases B n base
local notation "logs" => cursorStartupLogs b pub B n base m initial phases d
local notation "out" => after m (eventLog logs)

/-- Observable state at the boundary between the bootstrap and online calls. -/
structure StartupResult (cap : ℕ) : Prop where
  executed : runSegment (program b plan terminal pub) cap (some 0) m (List.replicate 8 []) = some logs
  cursor : endState (some 0) logs = some 0
  choices : branchPaths logs = List.replicate 8 []
  tagged : out (PairTag.address pub).val = 8
  ready : OnlineWorkspace.Ready d (arity C) (pub 2) (CalendarRows.rows D n) (DescriptorSpace.levelWords L) out
  saved : Frame.data (DescriptorParameters.saved L w) out = DescriptorParameters.outputs L B n
    b.degreeBits (roundedDown b.numerator b.denominator n*b.lanesPerBlock) w
  arena : (out (DescriptorSpace.levelStart L 0+14)).val = DescriptorSpace.endAddress L
  levels : (out (DescriptorSpace.levelStart L 0+28)).val = (L).levels
  length : (out (DescriptorSpace.levelStart L 0+29)).val = n
  cost : ∀ i, let r := startupReport b pub B n base m initial phases d i
    r.probes+1 ≤ sourceFuel b initial phases n i+30 ∧ r.events.length+1 ≤ sourceFuel b initial phases n i+30

  sourceCost : ∀ p ∈ cursorStartupSources b pub B n base m initial phases d, ∃ i : Fin 8,
    p.2.probes < sourceFuel b initial phases n i ∧ p.2.events.length < sourceFuel b initial phases n i

/-- The eight concrete components reach the online tag on the same memory
that holds the saved cursor geometry and history-arena bounds. -/
theorem cursor_startup (cap : ℕ) (arityEq : b.shape.arity = arity C) (fit : 10 ≤ 2^w)
    (clock : ∀ i : Fin 8, sourceFuel b initial phases n i+30 ≤ cap)
    (initialTag : m (PairTag.address pub).val = 0)
    (runs : TransferredStartup.Runs D d L B n b.degreeBits b.lanesPerBlock b.steps pub (PairTag.address pub) m)
    (hn : n < 2^w) (hs : 30 ≤ b.shape.scalarFields) (alloc : DescriptorSpace.endAddress L < 2^w) :
    StartupResult b plan terminal pub B n base m cap := by
  let t := startupTrace b pub B n base m initial phases d
  let tag := PairTag.address pub
  have run (i : Fin 8) : let S := original b plan terminal pub (startupStage i.castSucc)
      execute S (sourceFuel b initial phases n i) (S.start 0) (t.entry tag m i.castSucc) [] = some (t.source i) := by
    fin_cases i
    · exact runs.frame.callRow
    · exact runs.frame.callRaw
    · exact runs.frame.callLoad
    · exact runs.frame.callCopy
    · exact runs.calendar.callStride
    · exact runs.calendar.callArena
    · have h := runs.calendar.callBank
      change OnlineCursorStartup.Call (Workspace.initTable b.shape.arity) pub 42 0
        (t.entry tag m 6) (t.source 6) at h
      rw [arityEq] at h
      exact h
    · exact runs.calendar.callArm
  have tagged (i : Fin 9) : t.entry tag m i tag.val = LiveStageLink.tagWord w (startupStage i) := by
    cases i using Fin.cases with
    | zero => exact initialTag
    | succ j => rw [t.transfer]; exact ite_eq_left rfl
  have steps (i : Fin 8) : next (startupStage i.castSucc) = some (startupStage i.succ) := by
    have h : (startupStage i.castSucc).val+1 < 10 := by change i.val+1 < 10; omega
    exact dite_eq_left h
  obtain ⟨hr,hc,hm,hb,cost⟩ := linked_startup b plan terminal pub startupStage t.source
    (sourceFuel b initial phases n) (t.entry tag m) cap fit clock steps
    (fun i => tagged i.castSucc) (fun i => TransferredStartup.source_closed D d L B n b.degreeBits b.lanesPerBlock b.steps pub tag m i) run
    (fun i => (t.transfer tag m i).symm)
  change out = t.entry tag m (Fin.last 8) at hm
  have positive : 0 < (L).levels := Nat.add_pos_left (by decide : 0 < 1) _
  obtain ⟨ready, saved, arena, levels, len, tagged'⟩ := runs.output hn positive hs alloc
  change OnlineWorkspace.Ready d b.shape.arity _ _ _ _ at ready
  rw [arityEq] at ready
  have sourceBudget (i : Fin 8) : (t.source i).events.length < sourceFuel b initial phases n i :=
    (BurstRAM.execute_spec (run i)).1.length_lt
  refine ⟨hr,hc,hb,hm ▸ tagged',hm ▸ ready,hm ▸ saved,hm ▸ arena,hm ▸ levels,hm ▸ len,?_,?_⟩
  · intro i
    obtain ⟨hp,hl⟩ := cost i
    dsimp only at hp hl
    have probes : (t.source i).probes ≤ (t.source i).events.length := probes_le_length _
    have budget := sourceBudget i
    change (report pub _ (t.source i)).probes+1 ≤ _ ∧ (report pub _ (t.source i)).events.length+1 ≤ _
    omega
  · intro p hp
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hp
    exact ⟨i, (probes_le_length _).trans_lt (sourceBudget i), sourceBudget i⟩

end LiveProgram.CompressedPair

end VPVNP
end Computability
end OAI
