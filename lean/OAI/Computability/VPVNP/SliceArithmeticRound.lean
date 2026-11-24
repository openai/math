import OAI.Computability.VPVNP.SliceArithmeticLoop
import OAI.Computability.VPVNP.SliceArithmeticWork
import OAI.Computability.VPVNP.SliceArithmeticStreamRow

/-!
# The uniform coefficient loop of one Horner round

The loop consumes the three low-degree-first streams of limbs. The result is
pushed in reverse bit order so that one ordinary stack reversal prepares the
next accumulator.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace SliceArithmeticRound

open VPVNP.SliceArithmetic VPVNP.RAMTape

variable {p w : ℕ} [NeZero p]

/-- The three prime-field limbs consumed at one coefficient position of a Horner round. -/
structure Item (p : ℕ) where
  /-- Old accumulator limb saved as the shifted predecessor at the next coefficient position. -/
  old : Fin p
  /-- Coefficient of the defining monic polynomial below its leading term, used in reduction at
  this position. -/
  coeff : Fin p
  /-- Coefficient of the multiplier at the current degree. -/
  factor : Fin p

/-- The previous accumulator limb and the registers last written by a row.
The output list stores the new limbs from high to low. -/
structure Acc (p : ℕ) where
  /-- Preceding old accumulator coefficient, supplying the shift term for the next row. -/
  previous : Fin p
  /-- Most recently loaded defining-polynomial coefficient in the row registers. -/
  coeff : Fin p
  /-- Most recently loaded multiplier coefficient in the row registers. -/
  factor : Fin p
  /-- Prime-field coefficient computed by the most recent Horner row. -/
  result : Fin p
  /-- Temporary residue holding the Horner digit times the current multiplier coefficient. -/
  scratch : Fin p
  /-- Coefficients emitted by the processed rows, stored in reverse degree order. -/
  output : List (Fin p)

/-- Compute the shifted predecessor plus the reduction and digit products, prepend the result,
and save the old limb for the next row. -/
def next (digit reduction : Fin p) (s : Acc p) (x : Item p) : Acc p :=
  let scratch := digit * x.factor
  let result := s.previous + reduction * x.coeff + scratch
  ⟨x.old, x.coeff, x.factor, result, scratch, result :: s.output⟩

omit [NeZero p] in
private theorem fold_output (digit reduction : Fin p) (xs : List (Item p)) (s : Acc p) :
    (xs.foldl (next digit reduction) s).output =
      (Stream.run digit reduction xs.length
        ⟨xs.map Item.coeff, xs.map Item.factor, xs.map Item.old, s.output, s.previous, 0⟩).output := by
  suffices ∀ (k : ℕ), (xs.foldl (next digit reduction) s).output =
      (Stream.run digit reduction xs.length
        ⟨xs.map Item.coeff, xs.map Item.factor, xs.map Item.old, s.output, s.previous, k⟩).output from this 0
  intro k
  induction xs generalizing s k with
  | nil => rfl
  | cons x xs ih => exact ih (next digit reduction s x) (k + 4)

/-- The vector of streamed row results is the companion step of Horner's rule. -/
theorem fold_vector_output {e : ℕ} (c b v : Vector p e) (digit : Fin p)
    (s : Acc p) (hp : s.previous = 0) :
    let items := List.ofFn (fun i => Item.mk (v i) (c i) (b i))
    (items.foldl (next digit (-(List.ofFn v).getLastD 0)) s).output =
      (List.ofFn (add (companion c v) (scale digit b))).reverse ++ s.output := by
  intro xs
  rw [fold_output]
  simp only [xs, List.length_ofFn, List.map_ofFn, Function.comp_def, hp]
  obtain ⟨h, _⟩ := Stream.scan_output digit (-(List.ofFn v).getLastD 0) 0 c b v s.output 0
  rw [h]
  congr 3
  funext i
  cases e with
  | zero => exact i.elim0
  | succ k =>
    have hlast : (List.ofFn v).getLastD 0 = v (Fin.last k) := by rw [List.ofFn_succ']; simp
    rw [hlast]
    rfl

omit [NeZero p] in
theorem fold_result_of_nonempty (digit reduction : Fin p) (xs : List (Item p)) (s : Acc p)
    (hx : xs ≠ []) :
    let z := xs.foldl (next digit reduction) s
    z.output.head? = some z.result := by
  induction xs generalizing s with
  | nil => exact False.elim (hx rfl)
  | cons a xs ih =>
    cases xs with
    | nil => rfl
    | cons b bs => exact ih (next digit reduction s a) (List.cons_ne_nil _ _)

omit [NeZero p] in
/-- Pack low-endian words consecutively, retaining the full working width. -/
def packed (w : ℕ) (xs : List (Fin p)) : List Bool :=
  xs.flatMap fun a => BurstRAM.wordBits (Word.limb w a)

omit [NeZero p] in
@[simp] theorem packed_length (w : ℕ) (xs : List (Fin p)) : (packed w xs).length = xs.length * w := by
  induction xs with
  | nil => simp [packed]
  | cons a xs ih =>
    rw [packed, List.flatMap_cons, List.length_append, BurstRAM.length_wordBits]
    change w + (packed w xs).length = _
    rw [ih, List.length_cons, Nat.succ_mul, Nat.add_comm]

open SliceArithmeticStreamRow

/-- Register order of the Horner-row kernel. -/
def registers (w : ℕ) (digit reduction : Fin p) (s : Acc p) : Fin 8 → BurstRAM.Word w :=
  ![Fin.ofNat _ p, Word.limb w s.previous, Word.limb w reduction, Word.limb w s.coeff,
    Word.limb w digit, Word.limb w s.factor, Word.limb w s.result, Word.limb w s.scratch]

variable {X : Type} [DecidableEq X]

/-- The remaining stream inputs, the accumulated output, and the row markers.
Other caller ports and suffixes of the input streams are preserved. -/
def streams (w : ℕ) (marker : X) (base : Stacks (StreamPort X)) (xs : List (Item p))
    (s : Acc p) : Stacks (StreamPort X)
  | .old => packed w (xs.map Item.old) ++ base .old
  | .coeff => packed w (xs.map Item.coeff) ++ base .coeff
  | .factor => packed w (xs.map Item.factor) ++ base .factor
  | .out => (packed w s.output.reverse).reverse ++ base .out
  | .scratch => []
  | .outer j => if j = marker then List.replicate xs.length true else base (.outer j)

/-- One finite control for all moduli, word widths and extension degrees. -/
def scan (marker : X) : FiniteRoutine (Port X) :=
  FiniteRoutine.repeatMarked (.inr (.outer marker)) body

/-- A complete scan on the represented coefficient stream, including
arithmetic, register loads, output stores and loop tests. -/
theorem scan_runs (hw : Word.workingWidth p ≤ w) (marker : X)
    (base : Stacks (StreamPort X)) (digit reduction : Fin p) (xs : List (Item p)) (s : Acc p) :
    let frame := fun ys a => state (registers w digit reduction a) (streams w marker base ys a)
    ∃ ticks ≤ xs.length * (800 * (w + 1) ^ 2 + 22 * w + 10) + 1,
      (scan marker).Runs ticks (frame xs s) (frame [] (xs.foldl (next digit reduction) s)) := by
  intro frame
  apply FiniteRoutine.repeatMarked_runs (.inr (.outer marker)) body frame (next digit reduction)
    (800 * (w + 1) ^ 2 + 22 * w + 9) ?_ ?_ xs s
  · intro ys acc
    simp [frame, state, streams]
  intro x ys a
  let r := registers w digit reduction a
  let u := Function.update (streams w marker base (x :: ys) a) (.outer marker)
    (List.replicate ys.length true)
  let tails := streams w marker base ys a
  have readOld : u .old = BurstRAM.wordBits (Word.limb w x.old) ++ tails .old := by
    simp [u, tails, streams, packed]
  have readCoeff : u .coeff = BurstRAM.wordBits (Word.limb w x.coeff) ++ tails .coeff := by
    simp [u, tails, streams, packed]
  have readFactor : u .factor = BurstRAM.wordBits (Word.limb w x.factor) ++ tails .factor := by
    simp [u, tails, streams, packed]
  obtain ⟨k, hk, hr⟩ := body_runs hw r u a.previous reduction x.coeff digit x.factor x.old
    (tails .old) (tails .coeff) (tails .factor)
    (Nat.mod_eq_of_lt (Word.modulus_lt hw)) (Word.limb_val hw a.previous)
    (Word.limb_val hw reduction) (Word.limb_val hw digit)
    readOld readCoeff readFactor (by simp [u, streams])
  have hreg : nextRegisters r a.previous reduction x.coeff digit x.factor x.old =
      registers w digit reduction (next digit reduction a x) := by
    funext i
    fin_cases i <;> simp [nextRegisters, SliceArithmeticRow.rowRegisters, next, r, registers, Function.update]
  have hstreams : nextStreams u (tails .old) (tails .coeff) (tails .factor)
      (BurstRAM.wordBits (Word.limb w (a.previous + reduction * x.coeff + digit * x.factor))) =
      streams w marker base ys (next digit reduction a x) := by
    funext i
    cases i with
    | outer j => by_cases hj : j = marker <;> simp [nextStreams, streams, u, hj]
    | old | coeff | factor | scratch | out =>
      simp [nextStreams, tails, streams, next, u, packed, List.flatMap_append]
  rw [hreg, hstreams] at hr
  exact ⟨k, hk, by simpa only [frame, updateStream] using hr⟩

/-- The checked bit-stack execution for one digit reads each of the three input
vectors and writes the complete next accumulator in globally reversed bit order.
Register 6 contains the last output limb for the following reduction. -/
theorem horner_scan_runs {e : ℕ} (he : 0 < e) (hw : Word.workingWidth p ≤ w) (marker : X)
    (base : Stacks (StreamPort X)) (c b v : Vector p e) (digit : Fin p)
    (s : Acc p) (hprev : s.previous = 0) (hout : s.output = []) :
    let reduction := -(List.ofFn v).getLastD 0
    let xs := List.ofFn (fun i => Item.mk (v i) (c i) (b i))
    let y := add (companion c v) (scale digit b)
    ∃ a : Acc p, a.output = (List.ofFn y).reverse ∧ a.result = (List.ofFn y).getLastD 0 ∧
    ∃ ticks ≤ e * (800 * (w + 1) ^ 2 + 22 * w + 10) + 1,
      (scan marker).Runs ticks
        (state (registers w digit reduction s) (streams w marker base xs s))
        (state (registers w digit reduction a) (streams w marker base [] a)) := by
  intro reduction xs y
  let a := xs.foldl (next digit reduction) s
  have hx : xs ≠ [] := by
    intro hz
    have h := congrArg List.length hz
    simp [xs] at h
    omega
  have houtput : a.output = (List.ofFn y).reverse := by
    simpa only [hout, List.append_nil] using fold_vector_output c b v digit s hprev
  have hresult := fold_result_of_nonempty digit reduction xs s hx
  change a.output.head? = some a.result at hresult
  rw [houtput, List.head?_reverse] at hresult
  refine ⟨a, houtput, ?_, ?_⟩
  · simp [hresult]
  · simpa only [xs, List.length_ofFn] using scan_runs hw marker base digit reduction xs s

end SliceArithmeticRound

end VPVNP
end Computability
end OAI
