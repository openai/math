import OAI.ThreeFlat.RAM.Weighted

namespace OAI
/-! # Padding a branching RAM execution with a unique row sequence

A moving row exposes its current registers and one guessed event. The next
row receives the registers computed from that event. The first halting row
records the terminal word, and all subsequent rows have the single padding
value. The original choice bit remains in every branching row.
-/

namespace ThreeFlat.Diagonal.TraceRows

open Computability.VPVNP.BurstRAM

variable {C : Type*} {w : ℕ}

/-- A physical time row. The unused suffix of a bounded computation has a
single representation. -/
inductive Row (w : ℕ) (C : Type*) where
  | move (before : C) (event : Event w)
  | halt (before : C) (out : Option (Word w))
  | pad
  deriving DecidableEq

/-- Compute the next register file from a single claimed event. Reads use the
claimed word, later checked by the sorted-memory factors. -/
def next? : CallAction w C → Event w → Option C
  | .localStep c, .tick => some c
  | .branch next, .choice b => some (next b)
  | .read a next, .read b v => if a = b then some (next v) else none
  | .write a v c, .write b u => if a = b ∧ v = u then some c else none
  | _, _ => none

/-- Local transition and padding constraints. -/
inductive Local (P : Program w C) : C → List (Row w C) → Prop
  | halt {c f out} (step : P.step c = .finish out) :
      Local P c (.halt c out :: List.replicate f .pad)
  | move {c d e rs} (step : next? (P.step c) e = some d) (tail : Local P d rs) :
      Local P c (.move c e :: rs)

/-- Recover the original report from a valid sequence; padding has no events. -/
def report : List (Row w C) → Report w
  | [] => ⟨[], none⟩
  | .halt _ out :: _ => ⟨[], out⟩
  | .move _ e :: rs => (report rs).prepend e
  | .pad :: rs => report rs

/-- Render the uniquely determined register rows for a reported sequence of
steps. A report failing an opcode check produces no valid row sequence. -/
def render (P : Program w C) : ℕ → C → List (Event w) → Option (Word w) → List (Row w C)
  | 0, _, _, _ => []
  | f+1, c, [], out => .halt c out :: List.replicate f .pad
  | f+1, c, e :: es, out =>
    match next? (P.step c) e with
    | none => []
    | some d => .move c e :: render P f d es out

private theorem guessed_move {P : Program w C} {c d : C} {e es out f}
    (hs : next? (P.step c) e = some d) (ht : Guessed P f d es out) :
    Guessed P (f+1) c (e :: es) out := by
  cases ha : P.step c with
  | localStep z =>
    cases e <;> simp [next?, ha] at hs
    subst d
    exact .step ha ht
  | branch g =>
    cases e <;> simp [next?, ha] at hs
    subst d
    exact .branch ha ht
  | read a g =>
    cases e with
    | tick | choice | write => simp [next?, ha] at hs
    | read b v =>
      by_cases h : a = b
      · subst b
        simp [next?, ha] at hs
        subst d
        exact .read ha ht
      · simp [next?, ha, h] at hs
  | write a v z =>
    cases e with
    | tick | choice | read => simp [next?, ha] at hs
    | write b u =>
      by_cases h : a = b ∧ v = u
      · obtain ⟨rfl, rfl⟩ := h
        simp [next?, ha] at hs
        subst d
        exact .write ha ht
      · simp [next?, ha, h] at hs
  | finish | reject => cases e <;> simp [next?, ha] at hs

/-- The local register checks recover a valid guessed execution. The report
reconstructs the complete row sequence, so the register and padding guesses
add no multiplicities. -/
theorem local_spec {P : Program w C} {c : C} {rows : List (Row w C)} (h : Local P c rows) :
    Guessed P rows.length c (report rows).events (report rows).result ∧
      render P rows.length c (report rows).events (report rows).result = rows := by
  induction h with
  | halt h => exact ⟨by simpa [report] using (Guessed.done (f := _) h), by simp [report, render]⟩
  | @move c d e rs hs _ ih =>
    refine ⟨guessed_move hs ih.1, ?_⟩
    simpa [render, report, Report.prepend, hs] using congrArg (List.cons (.move c e)) ih.2

/-- Every valid guessed execution has its canonical sequence of exactly the
given number of rows. -/
theorem render_spec {P : Program w C} {f c es out} (h : Guessed P f c es out) :
    let rs := render P f c es out
    rs.length = f ∧ Local P c rs ∧ report rs = ⟨es, out⟩ := by
  induction h with
  | done hs => exact ⟨by simp [render], .halt hs, rfl⟩
  | step hs _ ih | branch hs _ ih | read hs _ ih | write hs _ ih =>
    simp only [render, hs, next?, eq_self, and_self, ite_true]
    refine ⟨by simpa using congrArg Nat.succ ih.1, .move (by simp [hs, next?]) ih.2.1, ?_⟩
    simp [report, ih.2.2, Report.prepend]

/-- Once chronological read consistency is imposed, the locally checked
rows coincide with native accepting reports, including the final word. -/
theorem existsUnique_rows_iff (P : Program w C) (f : ℕ) (c : C) (m : Memory w) (r : Report w) :
    (∃! rows : List (Row w C), rows.length = f ∧ Local P c rows ∧
      report rows = r ∧ Correct m (report rows).events) ↔ r ∈ RAM.reports P f c m := by
  rw [RAM.mem_reports_iff]
  constructor
  · rintro ⟨rs, ⟨hf, hl, hr, hc⟩, _⟩
    exact ⟨hf ▸ hr ▸ (local_spec hl).1, hr ▸ hc⟩
  · rintro ⟨hg, hc⟩
    obtain ⟨hf, hl, hr⟩ := render_spec hg
    have eqr : (⟨r.events, r.result⟩ : Report w) = r := rfl
    refine ⟨_, ⟨hf, hl, hr.trans eqr, hr.symm ▸ hc⟩, ?_⟩
    rintro other ⟨hf', hl', hr', _⟩
    have he := (local_spec hl').2
    rw [hf', hr'] at he
    exact he.symm

end ThreeFlat.Diagonal.TraceRows

end OAI
