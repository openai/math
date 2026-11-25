import OAI.Computability.IntegerMultiplication.Toom.Evaluate
import OAI.Computability.IntegerMultiplication.Carry.Shrink
import OAI.Computability.IntegerMultiplication.Code.Padding
import OAI.Computability.IntegerMultiplication.Code.Repeat
import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Tactic

/-!
# Computing a dyadic chunk width with one stack program

A live record consists of three unary lists: the remaining exponent, the
current width, and the current number of chunks. Doubling the chunk count
uses list append. Halving the width uses the two-state stream transducer
`Toom.piece 2`. The exponent is input data throughout.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Uniform.Dyadic
open IntegerMultiplication IntegerMultiplication.Code

abbrev State := Tally × Tally × Tally

/-- One round, applied when the remaining exponent is nonempty. -/
def step (x : State) : State := (x.1.tail, Toom.piece 2 x.2.1, x.2.2 ++ x.2.2)

private theorem easyTail : Easy (fun l : Tally => l.tail) := by
  have eq : (fun l : Tally => l.tail) =
      (fun l : Tally => List.casesOn l ([] : Tally) (fun _ xs => xs)) := by
    funext l; cases l <;> rfl
  rw [eq]
  exact Easy.listCase [] Easy.snd

theorem easy_step : Easy step := by
  apply Easy.pair (Easy.fst.compose easyTail)
  exact (Toom.easy_piece (K := 2) Easy.snd.fstCompose).pair
    (easy_append Easy.snd.sndCompose Easy.snd.sndCompose)

theorem half_width (x : Tally) : (Toom.piece 2 x).length = x.length ⌈/⌉ 2 := by
  have h := Toom.piece_bounds (K := 2) x
  rw [Nat.ceilDiv_eq_add_pred_div]
  omega

theorem dyadic_ceil_succ (n d : ℕ) : (n ⌈/⌉ (2 ^ d)) ⌈/⌉ 2 = n ⌈/⌉ (2 ^ (d+1)) := by
  have hd : 0 < 2 ^ d := by positivity
  have hd' : 0 < 2 ^ (d+1) := by positivity
  apply le_antisymm
  · apply (ceilDiv_le_iff_le_mul (by decide : 0 < (2 : ℕ))).2
    apply (ceilDiv_le_iff_le_mul hd).2
    rw [← Nat.mul_assoc, ← pow_succ]
    exact (ceilDiv_le_iff_le_mul hd').1 le_rfl
  · apply (ceilDiv_le_iff_le_mul hd').2
    rw [pow_succ, Nat.mul_assoc]
    apply (ceilDiv_le_iff_le_mul hd).1
    exact (ceilDiv_le_iff_le_mul (by decide : 0 < (2 : ℕ))).1 le_rfl

/-- The decoder state after `d` of `k` rounds at input length `n`. -/
def stage (n k d : ℕ) : State :=
  (tally (k - d), tally (n ⌈/⌉ (2 ^ d)), tally (2 ^ d))

theorem step_stage (n : ℕ) {k d : ℕ} (h : d < k) :
    step (stage n k d) = stage n k (d+1) := by
  unfold step stage
  have hk : k-d = (k-(d+1))+1 := by omega
  rw [hk, tally_succ, List.tail_cons]
  congr 2
  · rw [← recover_tally (Toom.piece 2 _), half_width, tally_length, dyadic_ceil_succ]
  · rw [← recover_tally (tally _ ++ tally _), List.length_append, tally_length, pow_succ]
    congr 1
    omega

theorem iterate_stage (n k d : ℕ) (hd : d ≤ k) : step^[d] (stage n k 0) = stage n k d := by
  induction d with
  | zero => rfl
  | succ d ih => rw [Function.iterate_succ_apply', ih (by omega), step_stage n (by omega)]

theorem stage_size_bound {n k : ℕ} (h : 2 ^ k ≤ n) {d : ℕ} (hd : d ≤ k) :
    size (stage n k d) ≤ 6 * n + 5 := by
  have hr : 2 ^ d ≤ n := (Nat.pow_le_pow_right (by decide) hd).trans h
  have hw : n ⌈/⌉ 2 ^ d ≤ n := (ceilDiv_le_iff_le_mul (by positivity)).2
    (Nat.le_mul_of_pos_left _ (by positivity))
  have hk : k ≤ n := (Nat.le_of_lt (Nat.lt_two_pow_self)).trans h
  simp only [stage, size_prod, size_tally, tally_length]
  omega

private def running (x : State) : Bool := !x.1.isEmpty

private theorem easyRunning : Easy running := by
  apply Easy.compose (f := Prod.fst) (g := fun l : Tally => !l.isEmpty) Easy.fst
  have h : (fun l : Tally => !l.isEmpty) =
      (fun l : Tally => List.casesOn l false (fun _ _ => true)) := by
    funext l; cases l <;> rfl
  change Easy (fun l : Tally => !l.isEmpty)
  rw [h]
  exact Easy.listCase false (Easy.const true)

private def signal (x : State) : Bool × State :=
  (running x, bif running x then step x else x)

private theorem easySignal : Easy signal := by
  apply Easy.pair easyRunning
  exact (easyRunning.pair Easy.identity).compose (Easy.identity.ifst easy_step)

/-- The ghost stage tracks acceptance and the position in the unary counter. -/
private structure Index where
  n : ℕ
  k : ℕ
  d : ℕ
  fits : 2 ^ k ≤ n
  within : d ≤ k

private def current (i : Index) := stage i.n i.k i.d
private def finish (i : Index) := stage i.n i.k i.k
private def next (i : Index) : Option Index :=
  if h : i.d < i.k then some { i with d := i.d+1, within := h } else none

private theorem running_stage (i : Index) : running (current i) = decide (i.d < i.k) := by
  unfold running current stage
  by_cases h : i.d < i.k
  · have he : i.k-i.d = (i.k-i.d-1)+1 := by omega
    change (! (tally (i.k-i.d)).isEmpty) = decide (i.d < i.k)
    rw [he, tally_succ, decide_eq_true h]
    rfl
  · simp [Nat.sub_eq_zero_of_le (by omega : i.k ≤ i.d), h, tally]

/-- The potential pays for halving, doubling, and the repeated linear scans of the
remaining unary exponent. At termination the count `2^k` still has to be read. -/
private def credit (i : Index) :=
  let rem := i.k - i.d
  4 * (i.n ⌈/⌉ 2 ^ i.d) + 2 * (2 ^ i.k - 2 ^ i.d) +
    2 * rem ^ 2 + 10 * rem + 2 * 2 ^ i.k + 10

private theorem credit_step (i : Index) :
    size (current i) + 1 + (next i).elim 0 credit ≤ credit i := by
  simp only [current, stage, size_prod, size_tally, tally_length]
  unfold next
  split
  · next hd =>
    simp only [Option.elim_some, credit]
    have he : i.k-i.d = (i.k-(i.d+1))+1 := by omega
    have hwidth := half_width (tally (i.n ⌈/⌉ 2 ^ i.d))
    rw [tally_length, dyadic_ceil_succ] at hwidth
    have hw := (Toom.piece_bounds (K := 2) (tally (i.n ⌈/⌉ 2 ^ i.d))).2
    rw [tally_length, hwidth] at hw
    have hp : 2 ^ (i.d+1) ≤ 2 ^ i.k := Nat.pow_le_pow_right (by decide) hd
    rw [pow_succ] at hp
    rw [he]
    simp only [pow_succ (2 : ℕ) i.d, Nat.mul_two] at *
    ring_nf at *
    omega
  · next hd =>
    have he : i.d=i.k := by have := i.within; omega
    simp [he, credit]
    omega

private theorem setup_task :
    Task credit (fun i => send (current i)) (fun i => send (finish i)) := by
  apply Task.iterate (a := fun i => size (current i)) next
  · apply (easySignal.on current).conform (fun _ => rfl) (fun _ => rfl)
    intro i
    by_cases h : i.d < i.k
    · simp only [next, dite_eq_left h, signal, running_stage, decide_eq_true h, Bool.cond_true]
      change Tree.fork (.atom true) (send (step (stage i.n i.k i.d))) = _
      rw [step_stage _ h]
      rfl
    · have eq : i.d=i.k := by have := i.within; omega
      simp only [next, dite_eq_right h, signal, running_stage, decide_eq_false h, Bool.cond_false]
      change Tree.fork (.atom false) (send (stage i.n i.k i.d)) = _
      rw [eq]
      rfl
  · intro i j h
    unfold next at h
    split at h
    · cases h; rfl
    · contradiction
  · exact credit_step

private theorem sq_bound (k : ℕ) : k ^ 2 ≤ 2 * 2 ^ k := by
  induction k with
  | zero => decide
  | succ k ih =>
    by_cases h : k < 3
    · interval_cases k <;> decide
    · rw [pow_succ (2 : ℕ)]
      nlinarith

/-- One fixed stack program transforms the initial three tallies into the
terminal tallies. On every accepted split its entire run, including all
intermediate passes, has a common linear time bound. -/
theorem compute_width :
    Task (fun i : {p : ℕ × ℕ // 2 ^ p.2 ≤ p.1} => i.val.1)
      (fun i => send (tally i.val.2, tally i.val.1, tally 1))
      (fun i => send (tally 0, tally (i.val.1 ⌈/⌉ 2 ^ i.val.2), tally (2 ^ i.val.2))) := by
  let start (i : {p : ℕ × ℕ // 2 ^ p.2 ≤ p.1}) : Index :=
    ⟨i.val.1,i.val.2,0,i.property,Nat.zero_le _⟩
  refine ((setup_task.on start).bound 32 ?_).conform (fun _ => rfl) ?_ ?_
  · intro i
    have hk : i.val.2 ≤ i.val.1 := (Nat.le_of_lt (Nat.lt_two_pow_self)).trans i.property
    have hs := sq_bound i.val.2
    have hr := i.property
    simp [credit, start]
    omega
  · intro i
    simp only [current, start, stage, Nat.sub_zero, pow_zero, ceilDiv_one]
  · intro i
    simp [finish, start, stage]

private theorem lt_born_length (k n : ℕ) : k < (Carry.born n).length ↔ 2 ^ k ≤ n := by
  induction k generalizing n with
  | zero =>
    cases n with
    | zero => simp
    | succ n => simp [Carry.birth (Nat.zero_lt_succ n)]
  | succ k ih =>
    cases n with
    | zero => simp
    | succ n =>
      rw [Carry.birth (Nat.zero_lt_succ n), List.length_cons, Nat.succ_lt_succ_iff,
        ih, pow_succ]
      exact Nat.le_div_iff_mul_le (by decide)

/-- Check the split before allocating any of its chunks. Counting the
length tally to minimal binary is the linear-time P192 routine. -/
theorem easy_guard : Easy (fun p : Tally × Tally => decide (2 ^ p.1.length ≤ p.2.length)) := by
  have h := (Easy.fst.pair (Easy.snd.compose Carry.easy_chart)).compose
    (Iter.small_easy (X := Unit) (Y := Bool))
  simpa only [Iter.small, lt_born_length] using h

/-- The actual result of a checked split, as two unary lists. -/
def checked (p : Tally × Tally) : Option (Tally × Tally) :=
  if 2 ^ p.1.length ≤ p.2.length then
    some (tally (p.2.length ⌈/⌉ (2 ^ p.1.length)), tally (2 ^ p.1.length))
  else none

/-- One fixed command accepts valid splits and rejects oversize splits before
allocation. Its total running time is linear in the unary input size. -/
theorem easy_checked : Easy checked := by
  let P := Tally × Tally
  let ok (p : P) := decide (2 ^ p.1.length ≤ p.2.length)
  let prep (p : P) : State := (p.1,p.2,tally 1)
  have hp : Easy prep := Easy.fst.pair (Easy.snd.pair (Easy.const _))
  have guard : Task (fun p : P => size p)
      (fun p => Tree.fork (.atom (ok p)) (send p)) (fun p => send (checked p)) := by
    apply Task.control ok
    · let C := (Option (Tally × Tally))
      refine ((Easy.const (none : C)).on (fun x : {p : P // ok p = false} => x.val)).conform
        (fun _ => rfl) (fun _ => rfl) ?_
      intro x
      have hx := x.property
      change decide _ = false at hx
      simp [checked, of_decide_eq_false hx]
    · let G := {p : P // ok p = true}
      let index (x : G) : {q : ℕ × ℕ // 2 ^ q.2 ≤ q.1} :=
        ⟨(x.val.2.length,x.val.1.length), of_decide_eq_true x.property⟩
      let output (x : G) : State := stage x.val.2.length x.val.1.length x.val.1.length
      have sim := (compute_width.on index).conform (fun _ => rfl)
        (p' := fun x => send (prep x.val)) (fun x => by simp [prep, index, recover_tally])
        (q' := fun x => send (output x)) (fun x => by simp [output, stage, index])
      have pack : Easy (fun s : State => some s.2) := easy_some Easy.snd
      have prog := ((hp.on (fun x : G => x.val)).compose sim).compose (pack.on output)
      refine (prog.bound 10 ?_).conform (fun _ => rfl) (fun _ => rfl) ?_
      · intro x
        have H := stage_size_bound (of_decide_eq_true x.property) (le_refl x.val.1.length)
        change size x.val + x.val.2.length + size (stage _ _ _) + 1 ≤ 10 * (size x.val + 1)
        rw [size_prod, size_tally, size_tally]
        omega
      · intro x
        have hx : 2 ^ x.val.1.length ≤ x.val.2.length := of_decide_eq_true x.property
        simp [checked, hx, output, stage]
  exact (Code.Task.compose (easy_guard.pair Easy.identity) guard).bound 2 (by intro x; omega)

end Uniform.Dyadic

end NearSquareRoot
end Computability
end OAI
