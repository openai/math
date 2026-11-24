import OAI.Computability.VPVNP.RAMTapeSpaceNamed

/-!
# All-branch stopping of the literal stack interpreter

The deterministic seek and restore sequences implementing each stack operation
are followed along their actual table records. Each binary virtual choice
branches at a single literal row. Thus the same quadratic clock that bounds
the accepting-leaf count also bounds the duration of rejecting paths.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace UniversalMachine

/-- Every path of the literal table has stopped within the given clock.
A row with no successor rejects; the two distinguished terminal states halt
immediately, independently of the remaining clock. -/
def AllHalt (p : Program) : ℕ → Config p.extra → Prop
  | 0, c => c.state.val < 2
  | n+1, c => c.state.val < 2 ∨
    match branches p c with
    | .stop => True
    | .one a => AllHalt p n (advance c a)
    | .two a b => AllHalt p n (advance c a) ∧ AllHalt p n (advance c b)

theorem allHalt_terminal (p : Program) (n : ℕ) (c : Config p.extra) (h : c.state.val < 2) :
    AllHalt p n c := by cases n with
  | zero => exact h
  | succ => exact Or.inl h

end UniversalMachine

namespace RAMTape

open UniversalMachine Turing

variable {Q : Type*} [Fintype Q]

private def haltAfter (start : Q) (code : Control Q) (ticks : ℕ) (t u : Tape Symbol) : Command Q → Prop
  | .halt _ => True
  | .next q a d b e => AllHalt (compile start code) ticks (running start q (updateTape t a d) (updateTape u b e))

private theorem allHalt_advance (start : Q) (code : Control Q) (n : ℕ) (q : Q)
    (t u : Tape Symbol) (cmd : Command Q) :
    AllHalt (compile start code) n (advance (running start q t u) (instruction start cmd)) ↔
      haltAfter start code n t u cmd := by
  cases cmd with
  | next => rfl
  | halt b =>
    change _ ↔ True
    refine iff_true_intro (allHalt_terminal _ _ _ ?_)
    cases b <;> simp [advance, instruction]

private theorem allHalt_step (start : Q) (code : Control Q) (n : ℕ) (q : Q) (t u : Tape Symbol) :
    AllHalt (compile start code) (n+1) (running start q t u) ↔
      match code q t.head u.head with
      | .stop => True
      | .one a => haltAfter start code n t u a
      | .two a b => haltAfter start code n t u a ∧ haltAfter start code n t u b := by
  rw [AllHalt, or_iff_right (not_lt_of_ge (running_state_ge_two ..)), lookup]
  cases code q t.head u.head <;> simp only [records, allHalt_advance]

/-- A deterministic tape macro consumes exactly its run length. -/
theorem Runs.allHalt {code : Control Q} {n q t u q' x y} (h : Runs code n q t u q' x y)
    (start : Q) (fuel : ℕ) : AllHalt (compile start code) (fuel+n) (running start q t u) ↔
      AllHalt (compile start code) fuel (running start q' x y) := by
  induction h with
  | nil => rfl
  | cons hs _ ih => rw [Nat.add_succ, allHalt_step, hs]; exact ih

namespace StackCompiler

theorem HeadBox.mono {r R : ℕ} {dx dy : ℤ} (h : HeadBox r dx dy) (hr : r ≤ R) : HeadBox R dx dy := by
  unfold HeadBox at h ⊢
  omega

variable {k : ℕ} (code : StackCode (Fin k) Q) (start : Q)

private abbrev halted (ticks : ℕ) (q : Q) (s : Stacks (Fin k)) :=
  AllHalt (compile (.ready start) (rows code)) ticks
    (running (.ready start) (.ready q) (tapeList (packed s)) (tapeList []))

private theorem allHalt_of_step {t B ticks : ℕ} {q s q' s'}
    (h : StackStep code q s q' s') (hsize : (packed s).length+t+1 ≤ B)
    (hclock : (t+1)*(6*B+4) ≤ ticks)
    (ih : ∀ left, (packed s').length+t ≤ B → t*(6*B+4) ≤ left → halted code start left q' s') :
    halted code start ticks q s := by
  obtain ⟨d, hd, run⟩ := step_run code h
  have hg := step_size code h
  rw [Nat.succ_mul] at hclock
  have h' := (run.allHalt (.ready start) (ticks-d)).mpr (ih _ (by omega) (by omega))
  rwa [Nat.sub_add_cancel (by omega)] at h'

/-- Lift the virtual all-path bound to the binary transition table. -/
theorem physical_allHalt (t : ℕ) (q : Q) (s : Stacks (Fin k)) (B ticks : ℕ)
    (stops : StopsWithin code t q s) (hsize : (packed s).length+t ≤ B)
    (hclock : t*(6*B+4) ≤ ticks) : halted code start ticks q s := by
  induction t generalizing q s ticks with
  | zero => exact stops.elim
  | succ t ih =>
    cases h : code q with
    | push i b r | pop i f | goto r =>
      simp only [StopsWithin, h] at stops
      apply allHalt_of_step code start _ (by omega) hclock (fun _ ↦ ih _ _ _ stops)
      first | exact .push h | exact .pop h | exact .goto h
    | choose low high =>
      simp only [StopsWithin, h] at stops
      rw [Nat.succ_mul] at hclock
      obtain ⟨ticks, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : ticks ≠ 0)
      apply (allHalt_step ..).mpr
      simp only [rows, h, haltAfter, update_stay]
      exact ⟨ih _ _ _ stops.1 (by omega) (by omega), ih _ _ _ stops.2 (by omega) (by omega)⟩
    | halt b =>
      rw [Nat.succ_mul] at hclock
      obtain ⟨ticks, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : ticks ≠ 0)
      apply (allHalt_step ..).mpr
      simp [rows, h, haltAfter]

/-- On the actual raw input, every branch of a named stack program has halted
by the same quadratic clock used for its exact integer path count. -/
theorem input_allHalt_labeled {K : Type*} [Fintype K] [DecidableEq K] (input : K)
    (code : StackCode K Q) (start : Q) (raw : Word) (T ticks : ℕ)
    (stops : StopsWithin code T start (labeledInput input raw))
    (clock : T*(6*(raw.length+(Fintype.card K+1)+T)+4) ≤ ticks) :
    let p := labeledProgram input code start
    AllHalt p ticks (initial p raw) := by
  have h := (stopsWithin_lift (target := labeledCode input code) (labeledPort input)
    (labeledPort_injective input) id (inputStacks raw) (fun _ ↦ rfl) T start _).2 stops
  rw [installedInput] at h
  dsimp only
  rw [physical_initial]
  apply physical_allHalt _ start T start _ _ ticks h _ clock
  simp [packed_input]

end StackCompiler
end RAMTape

end VPVNP
end Computability
end OAI
