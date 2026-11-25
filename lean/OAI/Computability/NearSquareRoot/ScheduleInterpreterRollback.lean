import OAI.Computability.NearSquareRoot.ScheduleInterpreterFrontier
import OAI.Computability.NearSquareRoot.ScheduleInterpreterParallel

/-!
# Timed-out attempts and physical rollback

On timeout the clock dispatches the current finite control to `entry`.
The rollback rule settles a pending frontier update, then erases all tapes
concurrently. Immutable tracks can contain fence bits or read-only input.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Uniform.Rollback

open IntegerMultiplication TM Reset

variable {A F Q I : Type}

/-- Pending marker update, or independent eraser states for all heads. -/
abbrev Control (Q I : Type) := (Q × (I → Bool × Bool)) ⊕ (I → Phase)

/-- Select the rollback entry state by inspecting only the old finite control.
Every head and every symbol is shared with the interrupted attempt. -/
def entry (w : Config (Cell A F) (Frontier.Control Q I) I) : Config (Cell A F) (Control Q I) I :=
  ⟨match w.pc with
   | .inl _ => .inr (fun _ => .seekLeft)
   | .inr pending => .inl pending, w.tape⟩

def cleaning (x : Config (Cell A F) (I → Phase) I) : Config (Cell A F) (Control Q I) I :=
  ⟨.inr x.pc, x.tape⟩

def restoringRule [Fintype I] (m : Rule A Q I) (base : F → A) : Rule (Cell A F) (Control Q I) I
  | .inl pending, h =>
    (Frontier.rule m (.inr pending) h).map fun (_, op) => (.inr (fun _ => .seekLeft), op)
  | .inr q, h =>
    (Parallel.rule (fun _ => Reset.restoringRule base) q h).map fun (q', op) => (.inr q', op)

private theorem cleaning_step [Fintype I] (m : Rule A Q I) (base : F → A)
    (x : Config (Cell A F) (I → Phase) I) :
    advance (restoringRule m base) (cleaning x) =
      (advance (Parallel.rule (fun _ => Reset.restoringRule base)) x).map cleaning := by
  unfold advance
  cases h : Parallel.rule (fun _ => @Reset.restoringRule A F base) x.pc
      (fun i => (x.tape i).view 0) <;> simp [cleaning, restoringRule, h]

private theorem cleaning_trace [Fintype I] (m : Rule A Q I) (base : F → A)
    {x y : Config (Cell A F) (I → Phase) I} {k : ℕ}
    (h : Trace (advance (Parallel.rule (fun _ => Reset.restoringRule base))) x k y) :
    Trace (advance (restoringRule m base)) (cleaning x) k (cleaning y) := by
  induction h with
  | nil => exact .nil _
  | cons hs _ ih => exact .cons (by simp [cleaning_step, hs]) ih

private theorem settle_step [Fintype I] (m : Rule A Q I) (base : F → A)
    (fixed : I → ℤ → F) (origin lo hi : I → ℤ)
    (w : Config (Cell A F) (Frontier.Control Q I) I) (y : Config A Q I)
    (h : advance (Frontier.rule m) w = some (Frontier.config fixed origin lo hi y)) :
    advance (restoringRule m base) (entry w) = some (entry (Frontier.config fixed origin lo hi y)) := by
  obtain ⟨q, tp⟩ := w
  cases q with
  | inl q =>
    unfold advance at h
    cases hm : m q (fun i => ((tp i).view 0).val) with
    | none => simp [Frontier.rule, hm] at h
    | some z => simp [Frontier.rule, Frontier.config, hm] at h
  | inr pending =>
    change advance (restoringRule m base) ⟨.inl pending, tp⟩ = _
    unfold advance at h ⊢
    simp only [Frontier.rule, Option.map_some, Frontier.config,
      Option.some.injEq, Config.mk.injEq] at h
    simp [restoringRule, Frontier.rule, entry, Frontier.config, h.2]

/-- After rollback all volatile symbols equal the baseline read from the fixed track, with each head at its
own origin and both frontier markers there. -/
def restored (base : F → A) (fixed : I → ℤ → F) (origin : I → ℤ) :
    Config (Cell A F) (Control Q I) I :=
  ⟨.inr (fun _ => .done), fun i =>
    Reset.atHead (origin i) (Reset.marked (origin i) (origin i) (origin i)
      (fun p => base (fixed i p)) (fixed i))⟩

/-- A settled frontier can be erased in three times the largest visited
interval size, independently of the number of tapes. -/
theorem from_settled_restore [Fintype I] (m : Rule A Q I) (base : F → A)
    (fixed : I → ℤ → F) (origin lo hi : I → ℤ) (y : Config A Q I)
    (bounds : ∀ i, lo i ≤ origin i ∧ origin i ≤ hi i ∧
      lo i ≤ (y.tape i).pos ∧ (y.tape i).pos ≤ hi i)
    (outside : ∀ i p, p < lo i ∨ hi i < p → (y.tape i).absolute p = base (fixed i p))
    (B : ℕ) (width : ∀ i, hi i - lo i ≤ B) :
    ∃ u ≤ 3*(B+1), Trace (advance (restoringRule m base)) (entry (Frontier.config fixed origin lo hi y))
      u (restored base fixed origin) ∧ advance (restoringRule m base) (restored base fixed origin) = none := by
  let x i := Reset.config .seekLeft (y.tape i).pos
    (Reset.marked (lo i) (hi i) (origin i) (y.tape i).absolute (fixed i))
  let z i := Reset.config .done (origin i)
    (Reset.marked (origin i) (origin i) (origin i) (fun p => base (fixed i p)) (fixed i))
  obtain ⟨u, hu, ht, halt⟩ := Parallel.trace (fun _ => Reset.restoringRule base) x z (3*(B+1)) (by
    intro i
    obtain ⟨ho₁, ho₂, hp₁, hp₂⟩ := bounds i
    obtain ⟨h, _, hb⟩ := Reset.cleanup_restore base (lo i) (hi i) (origin i) (y.tape i).pos
      (y.tape i).absolute (fixed i) hp₁ hp₂ ho₁ ho₂
    have heq : (fun p => if lo i ≤ p ∧ p ≤ hi i then base (fixed i p) else (y.tape i).absolute p) =
        fun p => base (fixed i p) := by
      funext p
      split
      · rfl
      · exact outside i p (by omega)
    rw [heq] at h
    exact ⟨_, by have := width i; omega, h⟩) (fun _ => rfl)
  have hstart : entry (Frontier.config fixed origin lo hi y) = cleaning (Parallel.pack x) := by
    unfold entry Frontier.config cleaning Parallel.pack
    congr 1
    funext i
    exact Frontier.tape_eq_reset _ _ _ _ _
  rw [hstart]
  exact ⟨u, hu, cleaning_trace m base ht, by
    change advance (restoringRule m base) (cleaning (Parallel.pack z)) = none
    simp [cleaning_step, halt]⟩

private theorem length_le_halt {D : Type} {step : D → Option D}
    {x y : D} {n : ℕ} (h : Trace step x n y) (hh : step y = none)
    {z : D} {k : ℕ} (pref : Trace step x k z) : k ≤ n := by
  induction h generalizing k with
  | nil =>
    cases pref with
    | nil => exact le_rfl
    | cons hs => rw [hh] at hs; cases hs
  | cons hs _ ih =>
    cases pref with
    | nil => exact Nat.zero_le _
    | cons hs' ht =>
      rw [hs] at hs'
      cases hs'
      exact Nat.add_le_add_left (ih hh ht) _

private theorem project_cleaning [Fintype I] (m : Rule A Q I) (base : F → A)
    (x : Config (Cell A F) (I → Phase) I)
    {k : ℕ} {w : Config (Cell A F) (Control Q I) I}
    (h : Trace (advance (restoringRule m base)) (cleaning x) k w) :
    ∃ y, w = cleaning y ∧ Trace (advance (Parallel.rule (fun _ => Reset.restoringRule base))) x k y := by
  generalize he : cleaning x = s at h
  induction h generalizing x with
  | nil => exact ⟨x, he.symm, .nil _⟩
  | cons hs _ ih =>
    subst_vars
    rw [cleaning_step] at hs
    cases hm : advance (Parallel.rule (fun _ => @Reset.restoringRule A F base)) x with
    | none => simp [hm] at hs
    | some y =>
      obtain ⟨z, hzw, hz⟩ := ih _ (by simpa [hm] using hs)
      exact ⟨z, hzw, .cons hm hz⟩

/-- The parallel rollback from completed marks stays inside the individually
observed intervals on every tape, even after some of the heads have finished. -/
theorem from_settled_prefix_restore [Fintype I] (m : Rule A Q I) (base : F → A)
    (fixed : I → ℤ → F) (origin lo hi : I → ℤ) (y : Config A Q I)
    (bounds : ∀ i, lo i ≤ origin i ∧ origin i ≤ hi i ∧
      lo i ≤ (y.tape i).pos ∧ (y.tape i).pos ≤ hi i)
    {k : ℕ} {z : Config (Cell A F) (Control Q I) I}
    (h : Trace (advance (restoringRule m base)) (entry (Frontier.config fixed origin lo hi y)) k z) :
    ∀ i, lo i ≤ (z.tape i).pos ∧ (z.tape i).pos ≤ hi i := by
  let x i := Reset.config .seekLeft (y.tape i).pos
    (Reset.marked (lo i) (hi i) (origin i) (y.tape i).absolute (fixed i))
  have hs : entry (Frontier.config fixed origin lo hi y) = cleaning (Parallel.pack x) := by
    unfold entry Frontier.config cleaning Parallel.pack
    congr 1
    funext i
    exact Frontier.tape_eq_reset _ _ _ _ _
  rw [hs] at h
  obtain ⟨z', rfl, hpar⟩ := project_cleaning m base (Parallel.pack x) h
  obtain ⟨xs, rfl, hx⟩ := Parallel.project_prefix _ x hpar
  intro i
  obtain ⟨j, _, ht⟩ := hx i
  obtain ⟨ho₁, ho₂, hp₁, hp₂⟩ := bounds i
  have hh := Reset.cleanup_restore base (lo i) (hi i) (origin i) (y.tape i).pos
    (y.tape i).absolute (fixed i) hp₁ hp₂ ho₁ ho₂
  exact Reset.cleanup_restore_prefix base _ _ _ _ _ _ hp₁ hp₂ ho₁ ho₂ (length_le_halt hh.1 hh.2.1 ht) ht

/-- A timeout may occur after either half of a simulated transition. The
finite-control dispatch to `entry` first completes a pending marker installation
(if any) and then clears all scratch, including writes of the interrupted step.
The bound includes all physical steps of the interrupted trace and rollback. -/
theorem timeout_restore [Fintype I] (m : Rule A Q I) (base : F → A)
    (fixed : I → ℤ → F) (origin : I → ℤ) (x : Config A Q I)
    (head : ∀ i, (x.tape i).pos = origin i)
    (scratch : ∀ i p, (x.tape i).absolute p = base (fixed i p))
    {t : ℕ} {w : Config (Cell A F) (Frontier.Control Q I) I}
    (physical : Trace (advance (Frontier.rule m)) (Frontier.config fixed origin origin origin x)
      t w) :
    ∃ (k : ℕ) (y : Config A Q I) (u : ℕ), Trace (advance m) x k y ∧
      t ≤ 2*k ∧ 2*k ≤ t+1 ∧
      Trace (advance (restoringRule m base)) (entry w) u (restored base fixed origin) ∧
      advance (restoringRule m base) (restored base fixed origin) = none ∧
      t+u ≤ 2*k + 3*(k+1) := by
  obtain ⟨k, y, l, r, run, bounds, frame, phase⟩ :=
    Frontier.settle_timeout_frame m fixed origin origin origin x (by simp [head]) physical
  obtain ⟨d, hd, reset, hh⟩ := from_settled_restore m base fixed origin l r y
    (fun i => ⟨(bounds i).1, (bounds i).2.1, (bounds i).2.2.1, (bounds i).2.2.2.1⟩)
    (fun i p hp => (frame i p hp).trans (scratch i p)) k (fun i => by
      simpa using (bounds i).2.2.2.2)
  rcases phase with ⟨ht, rfl⟩ | ⟨ht, next⟩
  · exact ⟨k, y, d, run, by omega, by omega, reset, hh, by omega⟩
  · exact ⟨k, y, 1+d, run, by omega, by omega,
      .cons (settle_step m base fixed origin l r w y next) reset, hh, by omega⟩

private theorem settle_positions (m : Rule A Q I)
    (fixed : I → ℤ → F) (origin lo hi : I → ℤ)
    (w : Config (Cell A F) (Frontier.Control Q I) I) (y : Config A Q I)
    (h : advance (Frontier.rule m) w = some (Frontier.config fixed origin lo hi y)) :
    ∀ i, (w.tape i).pos = (y.tape i).pos := by
  obtain ⟨q, tp⟩ := w
  cases q with
  | inl q =>
    unfold advance at h
    cases hm : m q (fun i => ((tp i).view 0).val) with
    | none => simp [Frontier.rule, hm] at h
    | some z => simp [Frontier.rule, Frontier.config, hm] at h
  | inr pending =>
    simp only [advance, Frontier.rule, Option.map_some, Frontier.config,
      Option.some.injEq, Config.mk.injEq] at h
    intro i
    simpa [Tape.apply, Move.shift, Frontier.tape] using
      congrArg (fun f : I → Tape (Cell A F) => (f i).pos) h.2

/-- Every head in every rollback prefix stays inside the fences on the
source interpreter. This applies at a timeout after either physical phase,
and the bound is independent of the attempt's duration. -/
theorem timeout_prefix_restore [Fintype I] (m : Rule A Q I) (base : F → A)
    (fixed : I → ℤ → F) (origin L R : I → ℤ) (x : Config A Q I)
    (head : ∀ i, (x.tape i).pos = origin i)
    (fits : ∀ {j z}, Trace (advance m) x j z → ∀ i, L i ≤ (z.tape i).pos ∧ (z.tape i).pos ≤ R i)
    {t : ℕ} {w : Config (Cell A F) (Frontier.Control Q I) I}
    (physical : Trace (advance (Frontier.rule m)) (Frontier.config fixed origin origin origin x) t w)
    {j : ℕ} {c : Config (Cell A F) (Control Q I) I}
    (initialTrace : Trace (advance (restoringRule m base)) (entry w) j c) :
    ∀ i, L i ≤ (c.tape i).pos ∧ (c.tape i).pos ≤ R i := by
  obtain ⟨k, y, l, r, _, bounds, _, cover, phase⟩ :=
    Frontier.settle_timeout_cover m fixed origin origin origin x (by simp [head]) physical
  have outer := cover L R (by simpa [head] using fits (.nil x)) fits
  have inner := fun i => And.intro (bounds i).1 (And.intro (bounds i).2.1
    (And.intro (bounds i).2.2.1 (bounds i).2.2.2.1))
  have extend {z : Config (Cell A F) (Control Q I) I}
      (h : ∀ i, l i ≤ (z.tape i).pos ∧ (z.tape i).pos ≤ r i) :
      ∀ i, L i ≤ (z.tape i).pos ∧ (z.tape i).pos ≤ R i :=
    fun i => ⟨(outer i).1.trans (h i).1, (h i).2.trans (outer i).2⟩
  rcases phase with ⟨_, rfl⟩ | ⟨_, hs⟩
  · exact extend (from_settled_prefix_restore m base fixed origin l r y inner initialTrace)
  · generalize he : entry w = start at initialTrace
    cases initialTrace with
    | nil =>
      subst_vars
      apply extend
      intro i
      change l i ≤ (w.tape i).pos ∧ (w.tape i).pos ≤ r i
      rw [settle_positions m fixed origin l r w y hs i]
      exact ⟨(bounds i).2.2.1, (bounds i).2.2.2.1⟩
    | cons step tail =>
      subst_vars
      rw [settle_step m base fixed origin l r w y hs] at step
      cases step
      exact extend (from_settled_prefix_restore m base fixed origin l r y inner tail)

/-- Erase ordinary scratch to a single blank symbol. -/
abbrev rule [Fintype I] (m : Rule A Q I) (blank : A) : Rule (Cell A F) (Control Q I) I :=
  restoringRule m (fun _ => blank)

abbrev fresh (blank : A) (fixed : I → ℤ → F) (origin : I → ℤ) :
    Config (Cell A F) (Control Q I) I := restored (fun _ => blank) fixed origin

theorem from_settled [Fintype I] (m : Rule A Q I) (blank : A)
    (fixed : I → ℤ → F) (origin lo hi : I → ℤ) (y : Config A Q I)
    (bounds : ∀ i, lo i ≤ origin i ∧ origin i ≤ hi i ∧
      lo i ≤ (y.tape i).pos ∧ (y.tape i).pos ≤ hi i)
    (outside : ∀ i p, p < lo i ∨ hi i < p → (y.tape i).absolute p = blank)
    (B : ℕ) (width : ∀ i, hi i - lo i ≤ B) :
    ∃ u ≤ 3*(B+1), Trace (advance (rule m blank)) (entry (Frontier.config fixed origin lo hi y))
      u (fresh blank fixed origin) ∧ advance (rule m blank) (fresh blank fixed origin) = none :=
  from_settled_restore m (fun _ => blank) fixed origin lo hi y bounds outside B width

theorem from_settled_prefix [Fintype I] (m : Rule A Q I) (blank : A)
    (fixed : I → ℤ → F) (origin lo hi : I → ℤ) (y : Config A Q I)
    (bounds : ∀ i, lo i ≤ origin i ∧ origin i ≤ hi i ∧
      lo i ≤ (y.tape i).pos ∧ (y.tape i).pos ≤ hi i)
    {k : ℕ} {z : Config (Cell A F) (Control Q I) I}
    (h : Trace (advance (rule m blank)) (entry (Frontier.config fixed origin lo hi y)) k z) :
    ∀ i, lo i ≤ (z.tape i).pos ∧ (z.tape i).pos ≤ hi i :=
  from_settled_prefix_restore m (fun _ => blank) fixed origin lo hi y bounds h

theorem timeout [Fintype I] (m : Rule A Q I) (blank : A)
    (fixed : I → ℤ → F) (origin : I → ℤ) (x : Config A Q I)
    (head : ∀ i, (x.tape i).pos = origin i)
    (scratch : ∀ i p, (x.tape i).absolute p = blank)
    {t : ℕ} {w : Config (Cell A F) (Frontier.Control Q I) I}
    (physical : Trace (advance (Frontier.rule m)) (Frontier.config fixed origin origin origin x)
      t w) :
    ∃ (k : ℕ) (y : Config A Q I) (u : ℕ), Trace (advance m) x k y ∧
      t ≤ 2*k ∧ 2*k ≤ t+1 ∧
      Trace (advance (rule m blank)) (entry w) u (fresh blank fixed origin) ∧
      advance (rule m blank) (fresh blank fixed origin) = none ∧
      t+u ≤ 2*k + 3*(k+1) :=
  timeout_restore m (fun _ => blank) fixed origin x head scratch physical

theorem timeout_prefix [Fintype I] (m : Rule A Q I) (blank : A)
    (fixed : I → ℤ → F) (origin L R : I → ℤ) (x : Config A Q I)
    (head : ∀ i, (x.tape i).pos = origin i)
    (fits : ∀ {j z}, Trace (advance m) x j z → ∀ i, L i ≤ (z.tape i).pos ∧ (z.tape i).pos ≤ R i)
    {t : ℕ} {w : Config (Cell A F) (Frontier.Control Q I) I}
    (physical : Trace (advance (Frontier.rule m)) (Frontier.config fixed origin origin origin x) t w)
    {j : ℕ} {c : Config (Cell A F) (Control Q I) I}
    (initialTrace : Trace (advance (rule m blank)) (entry w) j c) :
    ∀ i, L i ≤ (c.tape i).pos ∧ (c.tape i).pos ≤ R i :=
  timeout_prefix_restore m (fun _ => blank) fixed origin L R x head fits physical initialTrace

end Uniform.Rollback

end NearSquareRoot
end Computability
end OAI
