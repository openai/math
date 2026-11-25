import OAI.Computability.IntegerMultiplication.TMModel
import Mathlib.Data.Fintype.Pi

/-!
# Space fences on simulated multitape steps

A fence attaches two read-only bits to each symbol. At an endpoint an outward move
of any head causes the whole attempted transition to abort. The aborted state is
distinguishable from an ordinary halt. The test is performed by finite control
on the symbols under the physical heads and costs one transition.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Uniform.Fence

open IntegerMultiplication TM

variable {A Q I : Type}

/-- Finite marker tracks read by the guard, in left-end, right-end order. -/
abbrev Symbol (A : Type) := A × Bool × Bool

def bits (lo hi p : ℤ) : Bool × Bool := (decide (p = lo), decide (p = hi))

def markedTape (lo hi : ℤ) (x : Tape A) : Tape (Symbol A) :=
  ⟨x.pos, fun k => (x.view k, bits lo hi (x.pos + k))⟩

/-- The flag in the larger state is set precisely on an aborted transition. -/
def marked (lo hi : I → ℤ) (aborted : Bool) (x : Config A Q I) :
    Config (Symbol A) (Bool × Q) I :=
  ⟨(aborted, x.pc), fun i => markedTape (lo i) (hi i) (x.tape i)⟩

def within (lo hi : I → ℤ) (x : Config A Q I) : Prop :=
  ∀ i, lo i ≤ (x.tape i).pos ∧ (x.tape i).pos ≤ hi i

instance [Fintype I] (lo hi : I → ℤ) (x : Config A Q I) : Decidable (within lo hi x) :=
  inferInstanceAs (Decidable (∀ i, lo i ≤ (x.tape i).pos ∧ (x.tape i).pos ≤ hi i))

def permits (b : Bool × Bool) : Move → Bool
  | .left => !b.1
  | .stay => true
  | .right => !b.2

private theorem permits_iff {lo hi p : ℤ} (hl : lo ≤ p) (hr : p ≤ hi) (d : Move) :
    permits (bits lo hi p) d = true ↔ lo ≤ p + d.shift ∧ p + d.shift ≤ hi := by
  cases d <;> simp [permits, bits, Move.shift] <;> omega

/-- A legal step copies the two endpoint bits before moving. An illegal one
only raises the flag, leaving every symbol and head unchanged. -/
def guard [Fintype I] (m : Rule A Q I) : Rule (Symbol A) (Bool × Q) I :=
  fun (aborted, q) heads => if aborted then none else do
    let (q', ops) ← m q (fun i => (heads i).1)
    if ∀ i, permits (heads i).2 (ops i).2 = true then
      some ((false, q'), fun i => (((ops i).1, (heads i).2), (ops i).2))
    else
      some ((true, q), fun i => (heads i, Move.stay))

private theorem markedTape_apply (lo hi : ℤ) (x : Tape A) (o : A × Move) :
    (markedTape lo hi x).apply ((o.1, bits lo hi x.pos), o.2) =
      markedTape lo hi (x.apply o) := by
  unfold markedTape Tape.apply
  congr 1
  funext k
  by_cases h : k + o.2.shift = 0
  · have hp : x.pos + o.2.shift + k = x.pos := by omega
    simp [h, hp]
  · have hp : x.pos + o.2.shift + k = x.pos + (k + o.2.shift) := by omega
    simp [h, hp]

private theorem stay_put {B : Type} (x : Tape B) :
    x.apply (x.view 0, Move.stay) = x := by
  cases x with
  | mk p f =>
    simp [Tape.apply, Move.shift]
    funext k
    split <;> simp_all

/-- Physical transition equation in absolute coordinates. The coordinate test
in the specification is implemented by the local two-bit guard. -/
theorem advance_marked [Fintype I] (m : Rule A Q I) (lo hi : I → ℤ)
    (x : Config A Q I) (hx : within lo hi x) :
    advance (guard m) (marked lo hi false x) =
      (advance m x).map (fun y =>
        if within lo hi y then marked lo hi false y else marked lo hi true x) := by
  cases ht : m x.pc (fun i => (x.tape i).view 0) with
  | none => simp [advance, guard, marked, markedTape, ht]
  | some qo =>
    rcases qo with ⟨q, o⟩
    let y : Config A Q I := ⟨q, fun i => (x.tape i).apply (o i)⟩
    have hcond :
        (∀ i, permits (bits (lo i) (hi i) (x.tape i).pos) (o i).2 = true) ↔
          within lo hi y :=
      forall_congr' fun i => permits_iff (hx i).1 (hx i).2 _
    change (guard m (false, x.pc) (fun i => ((x.tape i).view 0,
      bits (lo i) (hi i) ((x.tape i).pos + 0)))).map _ = _
    by_cases hy : within lo hi y
    · have hall := hcond.mpr hy
      dsimp only [y] at hy
      simp [guard, ht, advance, hall, hy]
      congr 2
      funext i
      exact markedTape_apply _ _ _ _
    · have hfail := mt hcond.mp hy
      dsimp only [y] at hy
      simp [guard, ht, advance, hfail, hy]
      congr 2
      funext i
      simpa [marked, markedTape] using stay_put (markedTape (lo i) (hi i) (x.tape i))

@[simp] theorem aborted_halts [Fintype I] (m : Rule A Q I) (lo hi : I → ℤ)
    (x : Config A Q I) : advance (guard m) (marked lo hi true x) = none := rfl

/-- If every prefix fits, the guard reproduces the original trace with exactly
the same number of physical transitions. -/
theorem trace_marked [Fintype I] (m : Rule A Q I) (lo hi : I → ℤ)
    {x y : Config A Q I} {n : ℕ} (h : Trace (advance m) x n y)
    (fits : ∀ {k c}, k ≤ n → Trace (advance m) x k c → within lo hi c) :
    Trace (advance (guard m)) (marked lo hi false x) n (marked lo hi false y) := by
  induction h with
  | nil => exact .nil _
  | @cons x u y n step _ ih =>
    have hx := fits (Nat.zero_le _) (.nil x)
    have hu := fits (by omega : 1 ≤ 1 + n) (Trace.single step)
    refine .cons ?_ (ih ?_)
    · simp [advance_marked m lo hi x hx, step, hu]
    · intro k c hk hkc
      exact fits (by omega) (.cons step hkc)

/-- Each reachable head, even of an unsuccessful timed-out attempt, remains
inside its tape's closed integer interval. -/
theorem trace_within [Fintype I] (m : Rule A Q I) (lo hi : I → ℤ)
    {x : Config A Q I} (hx : within lo hi x) {b : Bool} {n : ℕ}
    {w : Config (Symbol A) (Bool × Q) I}
    (h : Trace (advance (guard m)) (marked lo hi b x) n w) :
    ∃ (z : Config A Q I) (tag : Bool), within lo hi z ∧ w = marked lo hi tag z := by
  generalize heq : marked lo hi b x = initial at h
  induction h generalizing x b with
  | nil init => exact ⟨x, b, hx, heq.symm⟩
  | @cons init u w n step _ ih =>
    subst init
    cases b with
    | true => simp at step
    | false =>
      rw [advance_marked m lo hi x hx] at step
      cases hm : advance m x with
      | none => simp [hm] at step
      | some z =>
        by_cases hz : within lo hi z
        · exact ih hz (by simpa [hm, hz] using step)
        · exact ih hx (by simpa [hm, hz] using step)

/-- Successful guarded execution cannot contain an abort. Removing the two
marker tracks and the flag recovers the original physical execution. -/
theorem reflect_trace [Fintype I] (m : Rule A Q I) (lo hi : I → ℤ)
    {x : Config A Q I} (hx : within lo hi x) {b : Bool} {n : ℕ}
    {w : Config (Symbol A) (Bool × Q) I}
    (h : Trace (advance (guard m)) (marked lo hi b x) n w) (ok : w.pc.1 = false) :
    b = false ∧ ∃ z, within lo hi z ∧ w = marked lo hi false z ∧ Trace (advance m) x n z := by
  generalize heq : marked lo hi b x = initial at h
  induction h generalizing x b with
  | nil init =>
    subst init
    change b = false at ok
    subst b
    exact ⟨rfl, x, hx, rfl, .nil _⟩
  | @cons init u w n step _ ih =>
    subst init
    cases b with
    | true => simp at step
    | false =>
      rw [advance_marked m lo hi x hx] at step
      cases hm : advance m x with
      | none => simp [hm] at step
      | some z =>
        by_cases hz : within lo hi z
        · obtain ⟨_, t, ht, hw, hist⟩ := ih hz ok
            (by simpa [hm, hz] using step : marked lo hi false z = u)
          exact ⟨rfl, t, ht, hw, .cons hm hist⟩
        · obtain ⟨bad, _⟩ := ih hx ok
            (by simpa [hm, hz] using step : marked lo hi true x = u)
          contradiction

theorem reflect_halt [Fintype I] (m : Rule A Q I) (lo hi : I → ℤ)
    {x : Config A Q I} (hx : within lo hi x) {n : ℕ}
    {w : Config (Symbol A) (Bool × Q) I}
    (h : Trace (advance (guard m)) (marked lo hi false x) n w) (ok : w.pc.1 = false)
    (halt : advance (guard m) w = none) :
    ∃ z, w = marked lo hi false z ∧ Trace (advance m) x n z ∧ advance m z = none := by
  obtain ⟨_, z, hz, rfl, hist⟩ := reflect_trace m lo hi hx h ok
  exact ⟨z, rfl, hist, by simpa [advance_marked m lo hi z hz] using halt⟩

end Uniform.Fence

end NearSquareRoot
end Computability
end OAI
