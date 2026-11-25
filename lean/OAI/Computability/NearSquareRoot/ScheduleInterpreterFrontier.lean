import OAI.Computability.NearSquareRoot.ScheduleInterpreterReset
import Mathlib.Basic.Finite.Prod
import Mathlib.Basic.Finite.Sum
import Mathlib.Data.Fintype.Pi

/-!
# Recording visited tape intervals during execution

Each simulated transition takes two physical transitions. The first updates the
data track, clears each endpoint being crossed, and moves every head. The second
sets the carried endpoint bits at the new heads. Origin bits and the fixed track
are preserved at every address. No extra tape is scanned.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Frontier

open IntegerMultiplication TM Reset

variable {A F Q I : Type}

/-- At steady-state instruction boundaries the physical control is in the left
summand. The right summand remembers which endpoints to set at the new heads. -/
abbrev Control (Q I : Type) := Q ⊕ (Q × (I → Bool × Bool))

private def carry (d : Move) (c : Cell A F) : Bool × Bool :=
  match d with
  | .left => (c.leftEnd, false)
  | .stay => (false, false)
  | .right => (false, c.rightEnd)

private def depart (v : A) (d : Move) (c : Cell A F) : Cell A F :=
  match d with
  | .left => {c with val := v, leftEnd := false}
  | .stay => {c with val := v}
  | .right => {c with val := v, rightEnd := false}

private def arrive (b : Bool × Bool) (c : Cell A F) : Cell A F :=
  {c with leftEnd := c.leftEnd || b.1, rightEnd := c.rightEnd || b.2}

/-- A physical finite-control wrapper for any deterministic multitape rule. -/
def rule (m : Rule A Q I) : Rule (Cell A F) (Control Q I) I
  | .inl q, h => (m q fun i => (h i).val).map fun (q', ops) =>
    (.inr (q', fun i => carry (ops i).2 (h i)),
      fun i => (depart (ops i).1 (ops i).2 (h i), (ops i).2))
  | .inr (q, b), h => some (.inl q, fun i => (arrive (b i) (h i), .stay))

/-- Canonical representation of a data tape and its visited interval. -/
def tape (fixed : ℤ → F) (origin lo hi : ℤ) (t : Tape A) : Tape (Cell A F) :=
  ⟨t.pos, fun k => ⟨t.view k, fixed (t.pos + k), decide (t.pos + k = origin),
    decide (t.pos + k = lo), decide (t.pos + k = hi)⟩⟩

private theorem update_tape (fix : ℤ → F) (o l r : ℤ) (t : Tape A)
    (hl : l ≤ t.pos) (hr : t.pos ≤ r) (v : A) (d : Move) :
    let old := tape fix o l r t
    let moved := old.apply (depart v d (old.view 0), d)
    moved.apply (arrive (carry d (old.view 0)) (moved.view 0), .stay) =
      tape fix o (min l (t.pos + d.shift)) (max r (t.pos + d.shift)) (t.apply (v,d)) := by
  dsimp only
  unfold tape Tape.apply
  congr 1
  · simp [Move.shift]
  · funext k
    cases d <;> simp only [Move.shift, Int.add_zero]
    all_goals
      split_ifs <;> simp_all [depart, arrive, carry, min_def, max_def]
    all_goals grind

def config (fixed : I → ℤ → F) (origin lo hi : I → ℤ) (x : Config A Q I) :
    Config (Cell A F) (Control Q I) I :=
  ⟨.inl x.pc, fun i => tape (fixed i) (origin i) (lo i) (hi i) (x.tape i)⟩

def extendLeft (lo : I → ℤ) (y : Config A Q I) (i : I) := min (lo i) (y.tape i).pos

def extendRight (hi : I → ℤ) (y : Config A Q I) (i : I) := max (hi i) (y.tape i).pos

/-- Two transitions reproduce one simulated write and move on every tape,
and enlarge exactly the endpoints crossed by the simulated heads. -/
theorem simulate_step (m : Rule A Q I) (fixed : I → ℤ → F) (origin lo hi : I → ℤ)
    {x y : Config A Q I} (h : advance m x = some y)
    (hpos : ∀ i, lo i ≤ (x.tape i).pos ∧ (x.tape i).pos ≤ hi i) :
    Trace (advance (rule m)) (config fixed origin lo hi x) 2
      (config fixed origin (extendLeft lo y) (extendRight hi y) y) := by
  unfold advance at h
  cases hm : m x.pc (fun i => (x.tape i).view 0) with
  | none => simp [hm] at h
  | some z =>
    obtain ⟨q, ops⟩ := z
    simp [hm] at h
    subst y
    let old := (config fixed origin lo hi x).tape
    let mid : Config (Cell A F) (Control Q I) I :=
      ⟨.inr (q, fun i => carry (ops i).2 ((old i).view 0)),
       fun i => (old i).apply (depart (ops i).1 (ops i).2 ((old i).view 0), (ops i).2)⟩
    refine Trace.cons (y := mid) ?_ (Trace.single ?_)
    · simp [mid, old, advance, rule, config, tape, hm]
    · unfold advance
      simp only [mid, rule, Option.map_some]
      congr 2
      funext i
      exact update_tape (fixed i) (origin i) (lo i) (hi i) (x.tape i)
        (hpos i).1 (hpos i).2 (ops i).1 (ops i).2

@[simp] theorem halt_iff (m : Rule A Q I) (fixed : I → ℤ → F) (origin lo hi : I → ℤ)
    (x : Config A Q I) :
    advance (rule m) (config fixed origin lo hi x) = none ↔ advance m x = none := by
  simp [advance, rule, config, tape]

/-- In one transition of a one-dimensional tape machine the new head is
at most one cell beyond the current interval. -/
private theorem width_step (m : Rule A Q I) (lo hi : I → ℤ) {x y : Config A Q I}
    (step : advance m x = some y)
    (hpos : ∀ i, lo i ≤ (x.tape i).pos ∧ (x.tape i).pos ≤ hi i) (i : I) :
    extendRight hi y i - extendLeft lo y i ≤ hi i - lo i + 1 := by
  unfold advance at step
  cases hm : m x.pc (fun i => (x.tape i).view 0) with
  | none => simp [hm] at step
  | some z =>
    obtain ⟨q, ops⟩ := z
    simp [hm] at step
    subst y
    have h := hpos i
    simp only [extendRight, extendLeft, Tape.apply]
    cases (ops i).2 <;> simp [Move.shift, max_def, min_def] <;> grind

/-- Any whole simulated trace is reproduced in twice the number of physical
steps. Each final interval includes the initial one and has grown by at most
one cell per simulated step, independently on each tape. -/
theorem simulate_trace (m : Rule A Q I) (fixed : I → ℤ → F) (origin lo hi : I → ℤ)
    {x y : Config A Q I} {n : ℕ} (run : Trace (advance m) x n y)
    (hpos : ∀ i, lo i ≤ (x.tape i).pos ∧ (x.tape i).pos ≤ hi i) :
    ∃ lo' hi' : I → ℤ,
      Trace (advance (rule m)) (config fixed origin lo hi x) (2*n)
        (config fixed origin lo' hi' y) ∧
      ∀ i, lo' i ≤ lo i ∧ hi i ≤ hi' i ∧ lo' i ≤ (y.tape i).pos ∧
        (y.tape i).pos ≤ hi' i ∧ hi' i - lo' i ≤ hi i - lo i + n := by
  induction run generalizing lo hi with
  | nil x =>
    refine ⟨lo, hi, .nil _, ?_⟩
    intro i
    exact ⟨le_rfl, le_rfl, (hpos i).1, (hpos i).2, by simp⟩
  | @cons x u y n step _ ih =>
    let l := extendLeft lo u
    let r := extendRight hi u
    obtain ⟨lo', hi', rest, hr⟩ := ih l r (fun i => ⟨min_le_right _ _, le_max_right _ _⟩)
    refine ⟨lo', hi', ?_, ?_⟩
    · simpa [Nat.mul_add] using (simulate_step m fixed origin lo hi step hpos).trans rest
    · intro i
      obtain ⟨hl', hh', h₁, h₂, hw⟩ := hr i
      refine ⟨hl'.trans (min_le_left _ _), (le_max_left _ _).trans hh', h₁, h₂, ?_⟩
      have hstep : r i - l i ≤ _ := width_step m lo hi step hpos i
      omega

/-- The tape at an instruction boundary has precisely the marked absolute
contents required by the cleanup subroutine. -/
theorem tape_eq_reset (fixed : ℤ → F) (o l r : ℤ) (t : Tape A) :
    tape fixed o l r t = Reset.atHead t.pos (Reset.marked l r o t.absolute fixed) := by
  unfold tape Reset.atHead Reset.marked Tape.absolute
  congr 1
  funext k
  simp

private theorem propagate {X : Type*} {s : X → Option X} (P : ℕ → X → Prop)
    (next : ∀ {t u v}, P t u → s u = some v → P (t+1) v)
    {x y : X} {n : ℕ} (run : Trace s x n y) (k : ℕ) (hp : P k x) : P (k+n) y := by
  induction run generalizing k with
  | nil => simpa using hp
  | @cons x u y n h _ ih =>
    simpa [Nat.add_assoc] using ih (k+1) (next hp h)

private theorem finish_pair {X : Type*} {s : X → Option X} {x y z : X}
    (h : Trace s x 2 z) (step : s x = some y) : s y = some z := by
  have inv : ∀ {u v} {k : ℕ}, Trace s u k v → k ≠ 0 →
      ∃ u', s u = some u' ∧ Trace s u' (k-1) v := by
    rintro _ _ _ run hn
    cases run with
    | nil => contradiction
    | @cons _ u' _ n h ht => exact ⟨u', h, by simpa using ht⟩
  obtain ⟨u, hu, tail⟩ := inv h (by decide)
  have eu := Option.some.inj (hu.symm.trans step)
  subst u
  obtain ⟨w, hw, last⟩ := inv tail (by decide)
  have same : ∀ {u v : X} {k : ℕ}, Trace s u k v → k = 0 → u = v := by
    rintro _ _ _ run hn
    cases run with
    | nil => rfl
    | cons => omega
  simpa [same last rfl] using hw

private theorem frame_step (m : Rule A Q I) {x y : Config A Q I}
    (step : advance m x = some y) (i : I) (p : ℤ) (h : p ≠ (x.tape i).pos) :
    (y.tape i).absolute p = (x.tape i).absolute p := by
  unfold advance at step
  cases hm : m x.pc (fun i => (x.tape i).view 0) with
  | none => simp [hm] at step
  | some z =>
    obtain ⟨q, ops⟩ := z
    simp [hm] at step
    subst y
    simpa [h] using Tape.absolute_apply (ops i) (x.tape i) p

/-- Settling a timeout retains all cells outside the final interval on each
simulated tape. Final frontier marks stay in every interval covering the
initial markers and all reachable original head positions. -/
theorem settle_timeout_cover (m : Rule A Q I) (fixed : I → ℤ → F) (origin lo hi : I → ℤ)
    (x : Config A Q I) (hpos : ∀ i, lo i ≤ (x.tape i).pos ∧ (x.tape i).pos ≤ hi i)
    {t : ℕ} {w : Config (Cell A F) (Control Q I) I}
    (run : Trace (advance (rule m)) (config fixed origin lo hi x) t w) :
    ∃ k y lo' hi', Trace (advance m) x k y ∧
      (∀ i, lo' i ≤ lo i ∧ hi i ≤ hi' i ∧ lo' i ≤ (y.tape i).pos ∧
        (y.tape i).pos ≤ hi' i ∧ hi' i - lo' i ≤ hi i - lo i + k) ∧
      (∀ i p, p < lo' i ∨ hi' i < p → (y.tape i).absolute p = (x.tape i).absolute p) ∧
      (∀ L R : I → ℤ, (∀ i, L i ≤ lo i ∧ hi i ≤ R i) →
        (∀ {j z}, Trace (advance m) x j z → ∀ i, L i ≤ (z.tape i).pos ∧ (z.tape i).pos ≤ R i) →
        ∀ i, L i ≤ lo' i ∧ hi' i ≤ R i) ∧
      ((t = 2*k ∧ w = config fixed origin lo' hi' y) ∨
       (t+1 = 2*k ∧ advance (rule m) w = some (config fixed origin lo' hi' y))) := by
  let P (t : ℕ) (w : Config (Cell A F) (Control Q I) I) :=
    ∃ k y lo' hi', Trace (advance m) x k y ∧
      (∀ i, lo' i ≤ lo i ∧ hi i ≤ hi' i ∧ lo' i ≤ (y.tape i).pos ∧
        (y.tape i).pos ≤ hi' i ∧ hi' i - lo' i ≤ hi i - lo i + k) ∧
      (∀ i p, p < lo' i ∨ hi' i < p → (y.tape i).absolute p = (x.tape i).absolute p) ∧
      (∀ L R : I → ℤ, (∀ i, L i ≤ lo i ∧ hi i ≤ R i) →
        (∀ {j z}, Trace (advance m) x j z → ∀ i, L i ≤ (z.tape i).pos ∧ (z.tape i).pos ≤ R i) →
        ∀ i, L i ≤ lo' i ∧ hi' i ≤ R i) ∧
      ((t = 2*k ∧ w = config fixed origin lo' hi' y) ∨
       (t+1 = 2*k ∧ advance (rule m) w = some (config fixed origin lo' hi' y)))
  have init : P 0 (config fixed origin lo hi x) :=
    ⟨0, x, lo, hi, .nil _, fun i => ⟨le_rfl, le_rfl, (hpos i).1, (hpos i).2, by simp⟩,
      fun _ _ _ => rfl, fun _ _ h _ => h, .inl ⟨rfl, rfl⟩⟩
  suffices P (0+t) w by simpa [P] using this
  refine propagate P ?_ run 0 init
  intro t u w hp phys
  obtain ⟨k, y, l, r, subrun, bounds, frame, cover, hd | hd⟩ := hp
  · obtain ⟨ht, rfl⟩ := hd
    cases step : advance m y with
    | none =>
      rw [(halt_iff m fixed origin l r y).2 step] at phys
      contradiction
    | some z =>
      have head (i : I) := And.intro (bounds i).2.2.1 (bounds i).2.2.2.1
      refine ⟨k+1, z, extendLeft l z, extendRight r z, subrun.trans (.single step), ?_, ?_, ?_,
        .inr ⟨by omega, finish_pair (simulate_step m fixed origin l r step head) phys⟩⟩
      · intro i
        obtain ⟨hl, hr, _, _, hw⟩ := bounds i
        refine ⟨(min_le_left _ _).trans hl, hr.trans (le_max_left _ _),
          min_le_right _ _, le_max_right _ _, ?_⟩
        have := width_step m l r step head i
        omega
      · intro i p outside
        have prev : p < l i ∨ r i < p :=
          outside.imp (fun h => h.trans_le (min_le_left _ _)) (fun h => (le_max_left _ _).trans_lt h)
        have hx := head i
        exact (frame_step m step i p (by omega)).trans (frame i p prev)
      · intro L R init inside i
        have ih := cover L R init inside i
        have hz := inside (subrun.trans (.single step)) i
        exact ⟨le_min ih.1 hz.1, max_le ih.2 hz.2⟩
  · obtain ⟨ht, hnext⟩ := hd
    exact ⟨k, y, l, r, subrun, bounds, frame, cover, .inl ⟨ht, Option.some.inj (phys.symm.trans hnext)⟩⟩

/-- Settling a timeout retains all cells outside the final interval on each
simulated tape, including during the last write-and-move transition. -/
theorem settle_timeout_frame (m : Rule A Q I) (fixed : I → ℤ → F) (origin lo hi : I → ℤ)
    (x : Config A Q I) (hpos : ∀ i, lo i ≤ (x.tape i).pos ∧ (x.tape i).pos ≤ hi i)
    {t : ℕ} {w : Config (Cell A F) (Control Q I) I}
    (run : Trace (advance (rule m)) (config fixed origin lo hi x) t w) :
    ∃ k y lo' hi', Trace (advance m) x k y ∧
      (∀ i, lo' i ≤ lo i ∧ hi i ≤ hi' i ∧ lo' i ≤ (y.tape i).pos ∧
        (y.tape i).pos ≤ hi' i ∧ hi' i - lo' i ≤ hi i - lo i + k) ∧
      (∀ i p, p < lo' i ∨ hi' i < p → (y.tape i).absolute p = (x.tape i).absolute p) ∧
      ((t = 2*k ∧ w = config fixed origin lo' hi' y) ∨
       (t+1 = 2*k ∧ advance (rule m) w = some (config fixed origin lo' hi' y))) := by
  obtain ⟨k, y, l, r, subrun, bounds, frame, _, status⟩ :=
    settle_timeout_cover m fixed origin lo hi x hpos run
  exact ⟨k, y, l, r, subrun, bounds, frame, status⟩

/-- Timeout can interrupt either transition of the marking wrapper. At an
instruction boundary the marks are already usable by cleanup. If the data
write and move have taken place, precisely one stationary installation step
completes the marks. The resulting interval has grown by at most the number
of started simulated transitions. -/
theorem settle_timeout (m : Rule A Q I) (fixed : I → ℤ → F) (origin lo hi : I → ℤ)
    (x : Config A Q I) (hpos : ∀ i, lo i ≤ (x.tape i).pos ∧ (x.tape i).pos ≤ hi i)
    {t : ℕ} {w : Config (Cell A F) (Control Q I) I}
    (run : Trace (advance (rule m)) (config fixed origin lo hi x) t w) :
    ∃ k y lo' hi', Trace (advance m) x k y ∧
      (∀ i, lo' i ≤ lo i ∧ hi i ≤ hi' i ∧ lo' i ≤ (y.tape i).pos ∧
        (y.tape i).pos ≤ hi' i ∧ hi' i - lo' i ≤ hi i - lo i + k) ∧
      ((t = 2*k ∧ w = config fixed origin lo' hi' y) ∨
       (t+1 = 2*k ∧ advance (rule m) w = some (config fixed origin lo' hi' y))) := by
  obtain ⟨k, y, l, r, subrun, bounds, _, status⟩ :=
    settle_timeout_frame m fixed origin lo hi x hpos run
  exact ⟨k, y, l, r, subrun, bounds, status⟩

end Frontier

end NearSquareRoot
end Computability
end OAI
