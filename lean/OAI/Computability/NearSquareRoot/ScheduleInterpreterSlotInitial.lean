import OAI.Computability.NearSquareRoot.ScheduleInterpreterSlotDriver
import OAI.Computability.NearSquareRoot.ScheduleInterpreterSlotBootstrap
import Batteries.Tactic.OpenPrivate

/-! # Literal input and the common-blank physical scheduler frame -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Uniform.IndexedSlot.Source
open IntegerMultiplication TM ScheduleMachine SlotLayout Timed
open private mapTape from OAI.Computability.NearSquareRoot.ScheduleInterpreterTimed
variable {A Q G I : Type} [DecidableEq I]
variable (s : Source A Q I)

omit [DecidableEq I] in
private theorem perm_raw (j : I) :
    SlotBlank.perm s.blank (literal s.blank) (.inr (some (.inl j))) = Equiv.refl _ := by
  classical
  change Equiv.swap (symbol s.blank) (symbol s.blank) = Equiv.refl _
  simp

private theorem tags_empty (j : Bank I) (p : ℤ) : tags s.idx 0 0 j p = none := by
  obtain _ | (k|b) := j
  · rfl
  · simp [tags,RoundExpose.word]
  · cases b <;> simp [tags,RoundExpose.word]

theorem marked_ready (n : ℕ) (x : Input n) (lo hi : I → ℤ) (distinct : s.idx ≠ s.inp) :
    SlotBoot.ready (literal s.blank) (fun j => Fence.markedTape (lo j) (hi j) (s.input n x j)) =
      frame s.start (s.input n x) s.idx s.blank s.unary (literal s.blank) lo hi 0 0 0 0 := by
  have empty : (raw s.start (s.input n x) s.idx s.blank s.unary 0).tape = s.input n x := by
    funext k
    by_cases hk : k=s.idx
    · subst k
      simp [raw,input,initialConfig,distinct,RoundExpose.word,Tape.loaded,Tape.mk.injEq]
      funext p
      cases p <;> rfl
    · simp [raw,hk]
  have origins := s.input_origins n x
  funext j
  obtain b | (_ | (k|b)) := j
  · rw [cursor_eq]
    cases b <;> simp [SlotBoot.ready,SlotTracks.tape,code,RoundExpose.cursor,RoundControl.cursor,
      RoundExpose.letter]
  · apply congrArg (Tape.mk _)
    funext p
    cases p <;> rfl
  · simp [frame,counters,ScheduleMachine.mount,work,SlotTracks.dataCfg,SlotTracks.dataTape,tags_empty,
      published,Release.active,Copy.beginCopy,Restart.start,Restart.active,Frontier.config,Frontier.tape,
      Rollback.origins,Rollback.snapshot,Tape.absolute,Attempt.entry,Timed.pack,mapTape,Fence.marked,
      Fence.markedTape,SlotBoot.ready,SlotBoot.cell,empty,origins]
  · cases b <;>
      simp [frame,counters,ScheduleMachine.mount,work,SlotTracks.dataCfg,SlotTracks.dataTape,tags_empty,
        published,Release.active,Copy.beginCopy,Restart.start,Restart.active,Frontier.config,Frontier.tape,
        Rollback.origins,Rollback.snapshot,Tape.absolute,Attempt.entry,Timed.pack,mapTape,clock,
        SlotBoot.ready,SlotBoot.cell,RoundExpose.word,Tape.loaded] <;>
      funext p <;> cases p <;> rfl

def unmarked (t : Tape A) : Tape (Fence.Symbol A) := ⟨t.pos,fun p => (t.view p,false,false)⟩

omit [DecidableEq I] in
private theorem initialized_tape (w : List A) :
    let raw := unmarked (Tape.loaded s.blank w)
    (⟨raw.pos,fun p => SlotBoot.park (raw.view p)⟩ : Tape (Letter A)) =
      Tape.loaded (symbol s.blank) (w.map symbol) := by
  apply congrArg (Tape.mk _)
  funext p
  cases p with
  | negSucc => rfl
  | ofNat k =>
    simp only [TM.Tape.loaded,List.getElem?_map,unmarked]
    cases w[k]? <;> rfl

theorem literal_start (n : ℕ) (x : Input n) (first : G) :
    SlotBlank.config (SlotBlank.perm s.blank (literal s.blank))
      (⟨some first,SlotBoot.staged (literal s.blank) (fun j => unmarked (s.input n x j))⟩ :
        Config (Letter A) (Option G) (Axis I)) =
    initialConfig (some first) (.inr (some (.inl s.inp)) : Axis I) (fun b => symbol (s.bit b))
      (symbol s.sep) (symbol s.blank) (xbits x) (ybits x) := by
  apply congrArg (Config.mk _)
  funext j
  obtain b | (_ | (k|b)) := j
  · apply congrArg (Tape.mk _)
    funext p
    simp [SlotBoot.staged,symbol]
    cases p <;> rfl
  · apply congrArg (Tape.mk _)
    funext p
    simp [SlotBoot.staged,symbol]
    cases p <;> rfl
  ·
    rw [perm_raw,SlotBlank.tape_refl]
    change (⟨_,fun p => SlotBoot.park ((unmarked (s.input n x k)).view p)⟩ : Tape _) = _
    simp only [input,initialConfig]
    rw [initialized_tape]
    by_cases hk : k=s.inp <;> simp [hk,List.map_map,Function.comp_def]
  · apply congrArg (Tape.mk _)
    funext p
    change SlotBlank.perm s.blank (literal s.blank) (.inr (some (.inr b)) : Axis I)
      (SlotBlank.background s.blank (literal s.blank) (.inr (some (.inr b)) : Axis I)) = _
    rw [SlotBlank.perm_background]
    simp [symbol]
    cases p <;> rfl

/-- Lift a raw finite fence installer to the literal input interface. One
stationary transition installs both cursor tags and all rollback origins. -/
theorem initialize_frame [Fintype I] (n : ℕ) (x : Input n) (lo hi : ℕ → I → ℤ) (distinct : s.idx ≠ s.inp)
    (m : Rule (Fence.Symbol A) G I) (first : G) {k y}
    (run : Trace (advance m) ⟨first,fun j => unmarked (s.input n x j)⟩ k y)
    (halt : advance m y=none)
    (installs : y.tape=fun j => Fence.markedTape (lo n j) (hi n j) (s.input n x j)) :
    let perm := SlotBlank.perm (I:=I) s.blank (literal s.blank)
    let pre := SlotBlank.rule perm (SlotBoot.rule s.blank m)
    let d := s.driver (lo) (hi) pre (some first)
    ∃ z, Trace (advance pre) (d.initial n x) (k+1) z ∧ advance pre z=none ∧
      z.tape = counters (symbol s.blank) (some true,literal s.blank) 0 0 (d.work n x) := by
  let e := SlotBlank.perm (I:=I) s.blank (literal s.blank)
  let pre := SlotBoot.rule s.blank m
  let physical := SlotBlank.rule e pre
  let d := s.driver lo hi physical (some first)
  have tr := SlotBoot.bootstrap s.blank m (literal s.blank) run halt
  have hist := SlotBlank.trace e pre tr
  rw [s.literal_start] at hist
  refine ⟨_,hist,?_,?_⟩
  · rw [SlotBlank.advance_config,SlotBoot.halt];rfl
  · change (fun j => SlotBlank.tape (e j) (SlotBoot.ready (literal s.blank) y.tape j)) = _
    rw [installs,s.marked_ready n x (lo n) (hi n) distinct]
    apply SlotBlank.counters_coded e (SlotBlank.perm_cursor_eq s.blank (literal s.blank))

end Uniform.IndexedSlot.Source

end NearSquareRoot
end Computability
end OAI
