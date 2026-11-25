import OAI.Computability.NearSquareRoot.VisitedCells
import Mathlib.Data.Finset.Prod

/-! # Extending a machine to a common set of physical tapes

Every extra head stays still and preserves the symbol under it. Thus embedding the old
tape indices preserves the exact step count. Each additional head contributes just its
initial position to the visited-cell count.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace CommonTapes

open IntegerMultiplication TM
variable {A Q I J : Type} (e : I ↪ J)

noncomputable def extend {B : Type} (f : I → B) (other : J → B) (j : J) : B := by
  classical
  exact if h : ∃ i, e i = j then f h.choose else other j

@[simp] theorem extend_apply {B : Type} (f : I → B) (other : J → B) (i : I) :
    extend e f other (e i) = f i := by
  classical
  let h : ∃ k, e k = e i := ⟨i, rfl⟩
  simp only [extend, dite_eq_left h]
  exact congrArg f (e.injective h.choose_spec)

theorem extend_off {B : Type} (f : I → B) (other : J → B) (j : J) (h : ¬ ∃ i, e i = j) :
    extend e f other j = other j := by simp [extend, h]

/-- A finite-table rule on the extended set of tapes. -/
noncomputable def rule (m : Rule A Q I) : Rule A Q J := fun q r =>
  (m q (r ∘ e)).map fun (q', op) =>
    (q', extend e op (fun j => (r j, Move.stay)))

noncomputable def config (other : J → Tape A) (c : Config A Q I) : Config A Q J :=
  ⟨c.pc, extend e c.tape other⟩

private theorem tape_skip (t : Tape A) : t.apply (t.view 0, .stay) = t := by
  cases t with
  | mk p v =>
    simp only [Tape.apply, Move.shift, add_zero, Tape.mk.injEq, true_and]
    funext i
    split <;> simp_all

theorem advance_config (m : Rule A Q I) (other : J → Tape A) (c : Config A Q I) :
    advance (rule e m) (config e other c) = (advance m c).map (config e other) := by
  simp only [advance, rule, config, Function.comp_def, extend_apply, Option.map_map]
  cases h : m c.pc (fun i => (c.tape i).view 0) with
  | none => rfl
  | some action =>
    rcases action with ⟨q, op⟩
    simp only [Option.map_some, Option.some.injEq, Config.mk.injEq, true_and]
    funext j
    by_cases h : ∃ i, e i = j
    · obtain ⟨i, rfl⟩ := h
      simp only [extend_apply]
    · simp only [extend_off e _ _ _ h, tape_skip]

theorem trace (m : Rule A Q I) (other : J → Tape A) {c f : Config A Q I} {t : ℕ}
    (h : Trace (advance m) c t f) :
    Trace (advance (rule e m)) (config e other c) t (config e other f) := by
  induction h with
  | nil => exact .nil _
  | cons h _ ih => exact .cons (by rw [advance_config, h]; rfl) ih

theorem reflectTrace (m : Rule A Q I) (other : J → Tape A) {c : Config A Q I}
    {f : Config A Q J} {t : ℕ} (h : Trace (advance (rule e m)) (config e other c) t f) :
    ∃ g, Trace (advance m) c t g ∧ config e other g = f := by
  generalize eq : config e other c = x at h
  induction h generalizing c with
  | nil => exact ⟨c, .nil _, eq⟩
  | cons step _ ih =>
    rw [← eq, advance_config] at step
    cases hv : advance m c with
    | none => simp [hv] at step
    | some c' =>
      obtain ⟨g, rest, rfl⟩ := ih (c := c') (by simpa [hv] using step)
      exact ⟨g, .cons hv rest, rfl⟩

theorem visits [Fintype J] (m : Rule A Q I) (other : J → Tape A) (c : Config A Q I) (t s : ℕ)
    (h : VisitsAtMost m c t s) :
    VisitsAtMost (rule e m) (config e other c) t (s + Fintype.card J) := by
  classical
  obtain ⟨v, hv, mem⟩ := h
  let f : I × ℤ → J × ℤ := fun z => (e z.1, z.2)
  let extra : J → J × ℤ := fun j => (j, (other j).pos)
  refine ⟨v.image f ∪ Finset.univ.image extra, ?_, ?_⟩
  · exact (Finset.card_union_le ..).trans (Nat.add_le_add (Finset.card_image_le.trans hv)
      (by simpa using (Finset.card_image_le (s := (Finset.univ : Finset J)) (f := extra))))
  · intro u hu x hx j
    obtain ⟨g, hg, rfl⟩ := reflectTrace e m other hx
    by_cases h : ∃ i, e i = j
    · obtain ⟨i, rfl⟩ := h
      apply Finset.mem_union_left
      simpa [config, f] using Finset.mem_image_of_mem f (mem u hu g hg i)
    · apply Finset.mem_union_right
      simp [config, extend_off e _ _ _ h, extra, Finset.mem_image]


/-- Preserve literal I/O at the designated heads and initialize every added tape blank. -/
theorem run_on_common_tapes [Fintype J] (m : Rule A Q I) (blank : A) (inp out : I)
    (start : Q) (input output : List A) (steps cells : ℕ)
    (run : ∃ (load : I → Tape A) (done : Config A Q I),
      load inp = Tape.loaded blank input ∧ (∀ i, i ≠ inp → load i = Tape.loaded blank []) ∧
      Trace (advance m) ⟨start, load⟩ steps done ∧ advance m done = none ∧
      whole blank output (done.tape out) ∧ VisitsAtMost m ⟨start, load⟩ steps cells) :
    ∃ (load : J → Tape A) (done : Config A Q J),
      load (e inp) = Tape.loaded blank input ∧
      (∀ j, j ≠ e inp → load j = Tape.loaded blank []) ∧
      Trace (advance (rule e m)) ⟨start, load⟩ steps done ∧ advance (rule e m) done = none ∧
      whole blank output (done.tape (e out)) ∧
      VisitsAtMost (rule e m) ⟨start, load⟩ steps (cells + Fintype.card J) := by
  obtain ⟨load, done, hload, hempty, hrun, hhalt, hout, hcells⟩ := run
  let other := fun _ : J => Tape.loaded blank []
  refine ⟨extend e load other, config e other done, by simpa using hload, ?_,
    trace e _ _ hrun, by simp [advance_config, hhalt], by simpa [config] using hout,
    visits e _ _ _ _ _ hcells⟩
  intro j h
  by_cases hj : ∃ i, e i = j
  · obtain ⟨i, rfl⟩ := hj
    simpa using hempty i (fun he => h (congrArg e he))
  · exact extend_off e _ _ _ hj

end CommonTapes

end NearSquareRoot
end Computability
end OAI
