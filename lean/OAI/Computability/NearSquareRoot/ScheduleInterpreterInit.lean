import OAI.Computability.NearSquareRoot.ScheduleInterpreter
import OAI.Computability.NearSquareRoot.ShortWordStack
import OAI.Computability.NearSquareRoot.VisitedCells
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Sum
import Mathlib.Tactic.DeriveFintype

/-!
# Installing the space fences

Two passes over the first input word place immutable boundary bits at the
two signed addresses `-n` and `n` on every initially blank work tape. The
input is read-only. All heads return to their initial positions. The five
control states and transition table are independent of the input length.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Uniform.FenceInit

open IntegerMultiplication TM

abbrev Cell (A : Type) := A × Bool × Bool

def plain {A : Type} (a : A) : Cell A := (a, false, false)

inductive Control
  | scan (right : Bool)
  | rewind (right : Bool)
  | done
  deriving DecidableEq, Fintype

private def direction (right : Bool) : Move := if right then .right else .left

/-- The two sweeps mark opposite ends on the same work tapes. -/
def setEnd {A : Type} (right : Bool) (c : Cell A) : Cell A :=
  if right then (c.1, c.2.1, true) else (c.1, true, c.2.2)

private def ops {A I : Type} (s : Option I → Cell A) (mi mw : Move)
    (f : Cell A → Cell A) : Option I → Cell A × Move
  | none => (s none, mi)
  | some i => (f (s (some i)), mw)

def rule {A I : Type} [DecidableEq A] (sep blank : A) : Rule (Cell A) Control (Option I)
  | .scan right, s =>
    if (s none).1 = sep then some (.rewind right, ops s .stay .stay (setEnd right))
    else some (.scan right, ops s .right (direction right) id)
  | .rewind right, s =>
    if (s none).1 = blank then
      some (if right then .scan false else .done, ops s .right (direction right) id)
    else some (.rewind right, ops s .left (direction (!right)) id)
  | .done, _ => none

private def tapeAt {S : Type} (f : ℤ → S) (p : ℤ) : Tape S :=
  ⟨p, fun j => f (p + j)⟩

@[simp] private theorem tapeAt_read {S : Type} (f : ℤ → S) (p : ℤ) :
    (tapeAt f p).view 0 = f p := by simp [tapeAt]

private theorem move_read {S : Type} (f : ℤ → S) (p : ℤ) (d : Move) :
    (tapeAt f p).apply (f p,d) = tapeAt f (p + d.shift) := by
  simp only [Tape.apply, tapeAt, Tape.mk.injEq, true_and]
  funext j
  split <;> rename_i h
  · congr 1
    omega
  · congr 1
    omega

private theorem write_stay {S : Type} (f : ℤ → S) (p : ℤ) (b : S) :
    (tapeAt f p).apply (b,.stay) = tapeAt (Function.update f p b) p := by
  simp only [Tape.apply, tapeAt, Move.shift, add_zero, Tape.mk.injEq, true_and]
  funext j
  by_cases h : j = 0
  · simp [h]
  · simp [h]

private def signed (right : Bool) (p : ℤ) := if right then p else -p

/-- Absolute contents are described by `input` and `work`. `p` is the
input head coordinate, and all scratch heads are at `p` or `-p`. -/
def layout {A I : Type} (input : ℤ → A) (work : ℤ → Cell A) (right : Bool)
    (p : ℤ) (q : Control) : Config (Cell A) Control (Option I) :=
  ⟨q, fun t => match t with
    | none => tapeAt (fun j => plain (input j)) p
    | some _ => tapeAt work (signed right p)⟩

variable {A I : Type} [DecidableEq A] (sep blank : A)
  (input : ℤ → A) (work : ℤ → Cell A)
local notation "cfg" => layout (I := I) input work
local notation "tick" => advance (rule (I := I) sep blank)

private theorem slide (right forward : Bool) (p : ℤ) (q q' : Control)
    (h : rule (I := I) sep blank q (fun i => ((cfg right p q).tape i).view 0) =
      some (q',ops (fun i => ((cfg right p q).tape i).view 0)
        (direction forward) (direction (right == forward)) id)) :
    tick (cfg right p q) =
      some (cfg right (p + (direction forward).shift) q') := by
  change (rule (I := I) sep blank q _).map _ = _
  rw [h]
  simp only [Option.map_some]
  congr 2
  funext t
  cases t with
  | none =>
    simpa [layout, ops] using move_read (fun j => plain (input j)) p (direction forward)
  | some i =>
    cases right <;> cases forward <;>
      simp [layout, ops, signed, direction, move_read, Move.shift, add_comm]

private theorem scan_step (right : Bool) (p : ℤ) (hp : input p ≠ sep) :
    tick (cfg right p (.scan right)) = some (cfg right (p+1) (.scan right)) := by
  apply slide (forward := true)
  simp [rule, layout, hp, plain, direction]

private theorem scan_trace (right : Bool) (n : ℕ) (h : ∀ j : ℕ, j < n → input j ≠ sep) :
    Trace tick (cfg right 0 (.scan right)) n (cfg right n (.scan right)) := by
  induction n with
  | zero => exact .nil _
  | succ n ih =>
    exact (ih (fun j hj => h j (by omega))).trans
      (.single (scan_step (I := I) sep blank input work right n (h n (by omega))))

private def marked (work : ℤ → Cell A) (right : Bool) (n : ℕ) : ℤ → Cell A :=
  Function.update work (signed right n) (setEnd right (work (signed right n)))

private theorem mark_step (right : Bool) (n : ℕ) (hn : input n = sep) :
    tick (cfg right n (.scan right)) =
      some (layout input (marked work right n) right n (.rewind right)) := by
  simp only [advance, rule, layout, tapeAt_read, plain, hn, ↓reduceIte, Option.map_some]
  congr 2
  funext t
  cases t with
  | none => simpa [ops, Move.shift, plain] using move_read (fun j => plain (input j)) (n : ℤ) .stay
  | some i => simp [ops, marked, write_stay]

private theorem rewind_step (right : Bool) (p : ℤ) (hp : input p ≠ blank) :
    tick (cfg right p (.rewind right)) = some (cfg right (p-1) (.rewind right)) := by
  apply slide (forward := false)
  simp [rule, layout, hp, plain, direction]

private theorem rewind_trace (right : Bool) (n : ℕ) (h : ∀ j : ℕ, j ≤ n → input j ≠ blank) :
    Trace tick (cfg right n (.rewind right)) (n+1) (cfg right (-1) (.rewind right)) := by
  induction n with
  | zero =>
    simpa using Trace.single (rewind_step (I := I) sep blank input work right 0 (h 0 (by omega)))
  | succ n ih =>
    have hs := rewind_step (I := I) sep blank input work right (n+1) (h (n+1) (by omega))
    have ht := ih (fun j hj => h j (by omega))
    exact (show n + 1 + 1 = 1 + (n+1) by omega) ▸
      (by apply Trace.cons _ ht; simpa using hs)

private theorem restart_step (right : Bool) (hb : input (-1) = blank) :
    tick (cfg right (-1) (.rewind right)) =
      some (cfg false 0 (if right then .scan false else .done)) := by
  have hs := slide (I := I) sep blank input work right true (-1) (.rewind right)
    (if right then .scan false else .done) (by simp [rule, layout, hb, plain, direction])
  simpa [direction, Move.shift, layout, signed] using hs

private theorem sweep (right : Bool) (n : ℕ)
    (hs : ∀ j : ℕ, j < n → input j ≠ sep) (he : input n = sep)
    (hb : ∀ j : ℕ, j ≤ n → input j ≠ blank) (hl : input (-1) = blank) :
    Trace tick (cfg right 0 (.scan right)) (2*n+3)
      (layout input (marked work right n) false 0 (if right then .scan false else .done)) := by
  have t := (scan_trace (I := I) sep blank input work right n hs).trans
    ((Trace.single (mark_step (I := I) sep blank input work right n he)).trans
      ((rewind_trace (I := I) sep blank input (marked work right n) right n hb).trans
        (Trace.single (restart_step (I := I) sep blank input (marked work right n) right hl))))
  convert t using 1
  omega

/-- The boundary track of each blank work tape after both sweeps. -/
def fenced (blank : A) (n : ℕ) (j : ℤ) : Cell A :=
  (blank, decide (j = -(n : ℤ)), decide (j = (n : ℤ)))

/-- From unmarked, blank scratch tapes and an input with first delimiter at
`n`, the physical initializer takes exactly `4*n+6` transitions, leaves the
input unchanged and puts each head back at zero. This includes both sweeps
and their return trips. -/
theorem initialize_fences (n : ℕ)
    (hs : ∀ j : ℕ, j < n → input j ≠ sep) (he : input n = sep)
    (hb : ∀ j : ℕ, j ≤ n → input j ≠ blank) (hl : input (-1) = blank) :
    Trace tick (layout (I := I) input (fun _ => plain blank) true 0 (.scan true))
      (4*n+6) (layout input (fenced blank n) false 0 .done) := by
  have hM : marked (marked (fun _ => plain blank) true n) false n = fenced blank n := by
    funext j
    by_cases hr : j = (n : ℤ) <;> by_cases hl' : j = -(n : ℤ) <;>
      simp_all [fenced, marked, setEnd, plain, signed, Function.update_apply]
  have t := (sweep (I := I) sep blank input (fun _ => plain blank) true n hs he hb hl).trans
    (sweep (I := I) sep blank input (marked (fun _ => plain blank) true n) false n hs he hb hl)
  rw [hM] at t
  simp only [Bool.false_eq_true, ↓reduceIte] at t
  convert t using 1
  omega

/-- A delimiter-separated input on its own tape, with the same initial
condition on each scratch tape. -/
def withInput (blank : A) (s : List A) (scratch : Tape (Cell A)) (q : Control) :
    Config (Cell A) Control (Option I) :=
  ⟨q, fun t => match t with
    | none => Tape.loaded (plain blank) (s.map plain)
    | some _ => scratch⟩

omit [DecidableEq A] in
private theorem layout_loaded (blank : A) (s : List A) (w : ℤ → Cell A)
    (right : Bool) (q : Control) :
    layout (I := I) (Tape.loaded blank s).view w right 0 q =
      withInput blank s ⟨0,w⟩ q := by
  unfold layout withInput
  congr 1
  funext t
  cases t with
  | some i => simp [signed, tapeAt]
  | none =>
    simp only [tapeAt, Tape.loaded, zero_add, Tape.mk.injEq, true_and]
    funext j
    cases j <;> simp [List.getElem?_map, Option.getD_map]

omit [DecidableEq A] in
private theorem loaded_empty (blank : A) : Tape.loaded (plain blank) [] =
    ⟨0,fun _ => plain blank⟩ := by
  simp only [Tape.loaded, Tape.mk.injEq, true_and]
  funext j
  cases j <;> simp

/-- A list-level specification on the P192 loaded tape interface. The tail
following the delimiter can be any list. -/
theorem initialize_delimited (first tail : List A)
    (hs : sep ∉ first) (hb : blank ∉ first) (hsb : sep ≠ blank) :
    let s := first ++ sep :: tail
    Trace tick
      (withInput (I := I) blank s (Tape.loaded (plain blank) []) (.scan true)) (4*first.length+6)
      (withInput blank s ⟨0,fenced blank first.length⟩ .done) := by
  dsimp only
  let source := (Tape.loaded blank (first ++ sep :: tail)).view
  have hread (j : ℕ) (hj : j < first.length) : source j = first[j] := by
    simp [source, Tape.loaded, List.getElem?_append_left hj, List.getElem?_eq_getElem hj]
  have he : source first.length = sep := by
    simp [source, Tape.loaded]
  have hnonblank (j : ℕ) (hj : j ≤ first.length) : source j ≠ blank := by
    rcases eq_or_lt_of_le hj with rfl | h
    · rwa [he]
    · exact fun e => hb ((hread j h).symm.trans e ▸ List.getElem_mem h)
  have h := initialize_fences (I := I) sep blank source first.length
    (fun j hj e => hs ((hread j hj).symm.trans e ▸ List.getElem_mem hj)) he hnonblank rfl
  unfold source at h
  simpa only [layout_loaded, loaded_empty] using h

omit [DecidableEq A] in
/-- The initialized scratch tape is precisely the guard's encoding of a
blank physical tape with the same head and the two specified endpoints. -/
theorem ready_for_guard (blank : A) (n : ℕ) :
    (⟨0, fenced blank n⟩ : Tape (Cell A)) =
      Fence.markedTape (-(n : ℤ)) n (Tape.loaded blank []) := by
  let w := Tape.loaded blank []
  have hw : w = (⟨0, fun _ => blank⟩ : Tape A) := by
    simp only [w, Tape.loaded, Tape.mk.injEq, true_and]
    funext j
    cases j <;> simp
  change _ = Fence.markedTape _ _ w
  rw [hw]
  simp [Fence.markedTape, Fence.bits]
  rfl

/-- All scratch and input cells touched during the preparation use an
absolute linear allowance on a fixed finite collection of tapes. -/
theorem initialize_visited [Fintype I] (first tail : List A) (hn : 0 < first.length) :
    VisitsAtMost (rule (I := I) sep blank)
      (withInput blank (first ++ sep :: tail) (Tape.loaded (plain blank) []) (.scan true))
      (4*first.length+6) ((Fintype.card (Option I) * 21) * first.length) := by
  apply visitsAtMost_of_linear_fence 10 first.length hn
  intro t ht c run i
  have h := head_excursion run i
  cases i <;> simp only [withInput, Tape.loaded, zero_sub, zero_add] at h <;> omega

end Uniform.FenceInit

end NearSquareRoot
end Computability
end OAI
