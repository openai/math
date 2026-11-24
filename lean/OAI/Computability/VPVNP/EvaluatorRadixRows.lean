import OAI.Computability.VPVNP.EvaluatorRadixSpace
import OAI.Computability.VPVNP.RAMTapeSuccessorFields

/-!
# Packed radix-digit rows for all label exponents

The machine reads one fixed-width binary exponent per row, in descending
label order. Each field is most-significant-bit-first. It prepends the radix
digits of each exponent to the output. Thus the finished table is ordered by
increasing label, with the most significant digit first in each row.

A unary width counter is spent during extraction to build the radix round
counter. The quotient produced by the division has the original width, so
clearing its bits restores the width counter for the next exponent.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace EvaluatorRadixRows

open RAMTape TapeWord
open EvaluatorRadixDivision (encodedDigits radixRoutine radixTicks reverseOnto reverseOnto_runs)

/-- The packed exponent input, unary row and width counters and the radix-conversion register
bank. -/
inductive Port where
  | input | width | rowCount | radix (k : EvaluatorRadixDivision.Port)
  deriving DecidableEq, Fintype

private abbrev staged : Port := .radix (.word .input)
private abbrev feedPort : Port := .radix (.word .feed)
private abbrev roundPort : Port := .radix .rounds

private def frame (rows width rounds : ℕ) (raw stage feed d acc : List Bool) : Stacks Port
  | .input => raw
  | .width => List.replicate width true
  | .rowCount => List.replicate rows true
  | .radix k => EvaluatorRadixDivision.bank rounds ⟨stage,feed,d,[],[],[],[],[]⟩ acc k

/-- The ready state between rows has no pending quotient or rounds. -/
def ready (rows width : ℕ) (raw d acc : List Bool) : Stacks Port :=
  frame rows width 0 raw [] [] d acc

private def stageBit (b : Bool) :=
  (Routine.push staged b).followedBy (Routine.push roundPort true)

private def readBit :=
  Routine.popCase Port.input (Routine.halt false) (stageBit false) (stageBit true)

private def extract :=
  Routine.popLoop Port.width (fun _ => true) (Routine.halt false) readBit

private def restoreWidth :=
  Routine.popLoop feedPort (fun _ => true) (Routine.push .width true) (Routine.push .width true)

local macro "by_ports" : tactic => `(tactic|
  (funext j; cases j with
    | input | width | rowCount => first | rfl | exact (List.replicate_succ ..).symm
    | radix k => cases k with
      | rounds | digits => first | rfl | exact (List.replicate_succ ..).symm
      | word i => cases i <;> rfl))

private theorem readBit_runs (rows width n : ℕ) (b : Bool) (raw stage d acc : List Bool) :
    readBit.Runs 3 (frame rows width n (b :: raw) stage [] d acc)
      (frame rows width (n+1) raw (b :: stage) [] d acc) := by
  let a := frame rows width n raw stage [] d acc
  let u := frame rows width n raw (b :: stage) [] d acc
  let v := frame rows width (n+1) raw (b :: stage) [] d acc
  have h₁ : Function.update a staged (b :: a staged) = u := by by_ports
  have h₂ : Function.update u roundPort (true :: u roundPort) = v := by by_ports
  have p := (Routine.runs_push staged b a).followedBy (h₁.symm ▸ Routine.runs_push roundPort true u)
  rw [h₁, h₂] at p
  have hin : Function.update (frame rows width n (b :: raw) stage [] d acc) Port.input raw = a := by by_ports
  cases b with
  | false => exact Routine.runs_popCase_false _ _ _ _ rfl (by rw [hin]; exact p)
  | true => exact Routine.runs_popCase_true _ _ _ _ rfl (by rw [hin]; exact p)

private theorem extract_runs (rows n : ℕ) (xs suffix stage d acc : List Bool) :
    extract.Runs (4*xs.length+1) (frame rows xs.length n (xs ++ suffix) stage [] d acc)
      (frame rows 0 (n+xs.length) suffix (xs.reverse ++ stage) [] d acc) := by
  induction xs generalizing n stage with
  | nil =>
    exact Routine.Runs.popLoop_empty .width (fun _ => true) (Routine.halt false) readBit
      (s := frame rows 0 n suffix stage [] d acc) rfl
  | cons b xs ih =>
    let s := frame rows (xs.length+1) n (b :: (xs ++ suffix)) stage [] d acc
    let a := frame rows xs.length n (b :: (xs ++ suffix)) stage [] d acc
    let u := frame rows xs.length (n+1) (xs ++ suffix) (b :: stage) [] d acc
    have ha : Function.update s .width (List.replicate xs.length true) = a := by by_ports
    have h := Routine.Runs.popLoop_true_continue Port.width (fun _ => true) (Routine.halt false) readBit
      (s := s) (mid := u) (show s .width = true :: List.replicate xs.length true from List.replicate_succ ..)
      rfl (by rw [ha]; exact readBit_runs rows xs.length n b (xs ++ suffix) stage d acc) (ih (n+1) (b::stage))
    rw [show 4*(b::xs).length+1 = 1+3+(4*xs.length+1) by simp only [List.length_cons]; omega]
    simpa only [s, extract, List.length_cons, List.cons_append, List.reverse_cons, List.append_assoc,
      List.singleton_append, List.nil_append, Nat.add_left_comm, Nat.add_comm, Nat.add_assoc] using h

private theorem restoreWidth_runs (rows width : ℕ) (raw feed d acc : List Bool) :
    restoreWidth.Runs (2*feed.length+1) (frame rows width 0 raw [] feed d acc)
      (ready rows (width + feed.length) raw d acc) := by
  induction feed generalizing width with
  | nil =>
    exact Routine.Runs.popLoop_empty feedPort (fun _ => true) (Routine.push .width true)
      (Routine.push .width true) rfl
  | cons b xs ih =>
    let s := frame rows width 0 raw [] (b::xs) d acc
    let a := frame rows width 0 raw [] xs d acc
    let u := frame rows (width+1) 0 raw [] xs d acc
    have ha : Function.update s feedPort xs = a := by by_ports
    have hu : Function.update a .width (true :: a .width) = u := by by_ports
    have h := Routine.Runs.popLoop_continue feedPort (fun _ => true) (Routine.push .width true)
      (Routine.push .width true) (s := s) (mid := u) (show s feedPort = b :: xs from rfl) rfl
      (by rw [ha]; cases b <;> exact hu ▸ Routine.runs_push Port.width true a) (ih (width+1))
    rw [show 2*(b::xs).length+1 = 1+1+(2*xs.length+1) by simp only [List.length_cons]; omega]
    simpa only [s, restoreWidth, List.length_cons, Nat.add_left_comm, Nat.add_comm, Nat.add_assoc] using h

private def rowRoutine : FiniteRoutine Port :=
  (((FiniteRoutine.ofRoutine extract).followedBy (reverseOnto staged feedPort)).followedBy
    (radixRoutine.onPorts Port.radix)).followedBy (FiniteRoutine.ofRoutine restoreWidth)

/-- Instruction count for extracting one z-bit exponent and converting its z requested radix
digits using a w-bit divisor. -/
def rowTicks (z w : ℕ) := 8*z + 3 + radixTicks z z w

private theorem rowRoutine_runs (rows : ℕ) (x suffix d acc : List Bool) (hq : 2 ≤ value d) :
    rowRoutine.Runs (rowTicks x.length d.length) (ready rows x.length (x.reverse ++ suffix) d acc)
      (ready rows x.length suffix d (encodedDigits d.length (value d) x.length (value x) ++ acc)) := by
  let a := frame rows 0 x.length suffix x [] d acc
  let b := frame rows 0 x.length suffix [] x.reverse d acc
  let q := PrimedCounter.digits x.length 0
  let acc' := encodedDigits d.length (value d) x.length (value x) ++ acc
  let u := frame rows 0 0 suffix [] q.reverse d acc'
  have h₁ : (FiniteRoutine.ofRoutine extract).Runs (4*x.length+1)
      (ready rows x.length (x.reverse ++ suffix) d acc) a := by
    simpa only [FiniteRoutine.ofRoutine, FiniteRoutine.Runs, ready, a, List.reverse_reverse, List.length_reverse, List.append_nil, Nat.zero_add] using
      extract_runs rows 0 x.reverse suffix [] d acc
  have h₂ := reverseOnto_runs (src := staged) (dst := feedPort) (by decide) a b rfl
    (show x.reverse = x.reverse ++ [] by simp) (by
      intro k hk hk'; cases k with
      | input | width | rowCount => rfl
      | radix k => cases k with
        | rounds | digits => rfl
        | word i => cases i <;> first | rfl | exact (hk rfl).elim | exact (hk' rfl).elim)
  have h₃ : (radixRoutine.onPorts Port.radix).Runs (radixTicks x.length x.length d.length) b u := by
    apply FiniteRoutine.runs_onPorts_framed radixRoutine (fun _ _ => Port.radix.inj)
      (EvaluatorRadixDivision.full_radixRoutine_runs x d acc hq)
    · intro k; rfl
    · intro k; rfl
    · intro k hk
      cases k with
      | radix i => exact (hk i rfl).elim
      | input | width | rowCount => rfl
  have h₄ : (FiniteRoutine.ofRoutine restoreWidth).Runs (2*x.length+1) u
      (ready rows x.length suffix d acc') := by
    simpa only [FiniteRoutine.ofRoutine, FiniteRoutine.Runs, u, q, PrimedCounter.digits, List.length_reverse, BurstRAM.length_wordBits, Nat.zero_add] using
      restoreWidth_runs rows 0 suffix q.reverse d acc'
  have hcost : rowTicks x.length d.length =
      (4*x.length+1)+(2*x.length+1)+radixTicks x.length x.length d.length+(2*x.length+1) := by
    unfold rowTicks; omega
  rw [hcost]
  exact ((h₁.followedBy h₂).followedBy h₃).followedBy h₄

/-- The loop consumes one unary mark per binary exponent field. -/
def radixRows : FiniteRoutine Port :=
  .ofRoutine (Routine.popLoop .rowCount (fun _ => true) (Routine.halt false) rowRoutine.body)

/-- Instruction count for converting the specified number of exponent rows, including the
row-counter updates and final exit. -/
def rowsTicks (rows z w : ℕ) := rows * (rowTicks z w + 1) + 1

/-- Source rows are supplied by descending label and highest binary bit first. -/
def packedInput {z : ℕ} (rows : List (BurstRAM.Word z)) : List Bool :=
  rows.reverse.flatMap fun x => (BurstRAM.wordBits x).reverse

/-- Destination rows are ordered by ascending label, then descending radix
place. Within each digit the bits are little-endian. -/
def packedTable {z : ℕ} (w Q : ℕ) (rows : List (BurstRAM.Word z)) : List Bool :=
  rows.flatMap fun x => encodedDigits w Q z x.val

private theorem loop_runs {z : ℕ} (xs : List (BurstRAM.Word z)) (suffix d acc : List Bool) (hq : 2 ≤ value d) :
    radixRows.Runs (rowsTicks xs.length z d.length)
      (ready xs.length z ((xs.flatMap fun x => (BurstRAM.wordBits x).reverse) ++ suffix) d acc)
      (ready 0 z suffix d (packedTable d.length (value d) xs.reverse ++ acc)) := by
  induction xs generalizing acc with
  | nil =>
    simpa [rowsTicks, packedTable, radixRows, FiniteRoutine.Runs, FiniteRoutine.ofRoutine] using
      (Routine.Runs.popLoop_empty Port.rowCount (fun _ => true) (Routine.halt false) rowRoutine.body
        (s := ready 0 z suffix d acc) rfl)
  | cons x xs ih =>
    let tail := (xs.flatMap fun y => (BurstRAM.wordBits y).reverse) ++ suffix
    let s := ready (xs.length+1) z ((BurstRAM.wordBits x).reverse ++ tail) d acc
    let a := ready xs.length z ((BurstRAM.wordBits x).reverse ++ tail) d acc
    let next := encodedDigits d.length (value d) z x.val ++ acc
    let u := ready xs.length z tail d next
    have ha : Function.update s Port.rowCount (List.replicate xs.length true) = a := by by_ports
    have hb : rowRoutine.Runs (rowTicks z d.length) a u := by
      simpa only [a, u, next, BurstRAM.length_wordBits, value_wordBits] using
        rowRoutine_runs xs.length (BurstRAM.wordBits x) tail d acc hq
    have h := Routine.Runs.popLoop_true_continue Port.rowCount (fun _ => true) (Routine.halt false) rowRoutine.body
      (s := s) (mid := u)
      (show s .rowCount = true :: List.replicate xs.length true from List.replicate_succ ..)
      rfl (by rw [ha]; exact hb) (ih next)
    have ht : rowsTicks (x::xs).length z d.length = 1+rowTicks z d.length+rowsTicks xs.length z d.length := by
      simp only [rowsTicks, List.length_cons, Nat.succ_mul]
      omega
    rw [ht]
    simpa only [s, next, tail, radixRows, FiniteRoutine.ofRoutine, FiniteRoutine.Runs,
      List.length_cons, List.flatMap_cons, List.reverse_cons, packedTable, List.flatMap_append, List.flatMap_nil,
      List.append_nil, List.append_assoc] using h

/-- All rows of the exponent table are converted by the same finite code.
The input suffix, the original divisor and the width counter are preserved.
All intermediate stacks are empty on return. -/
theorem radixRows_runs {z : ℕ} (rows : List (BurstRAM.Word z)) (suffix d acc : List Bool) (hq : 2 ≤ value d) :
    radixRows.Runs (rowsTicks rows.length z d.length) (ready rows.length z (packedInput rows ++ suffix) d acc)
      (ready 0 z suffix d (packedTable d.length (value d) rows ++ acc)) := by
  simpa only [packedInput, List.length_reverse, List.reverse_reverse] using loop_runs rows.reverse suffix d acc hq

@[simp] theorem packedTable_length {z : ℕ} (w Q : ℕ) (rows : List (BurstRAM.Word z)) :
    (packedTable w Q rows).length = rows.length * (z*w) := by
  induction rows with
  | nil => simp [packedTable]
  | cons x xs ih =>
    simp only [packedTable, List.flatMap_cons, List.length_append, EvaluatorRadixDivision.encodedDigits_length,
      List.length_cons, Nat.succ_mul]
    rw [← packedTable, ih, Nat.add_comm]

private theorem drop_field {A : Type*} (f : A → List Bool) (w : ℕ) (hw : ∀ a, (f a).length = w)
    (xs : List A) (tail : List Bool) (i : ℕ) (hi : i < xs.length) :
    ((xs.flatMap f ++ tail).drop (i*w)) =
      f xs[i] ++ ((xs.drop (i+1)).flatMap f ++ tail) := by
  induction xs generalizing i with
  | nil => simp at hi
  | cons a xs ih =>
    cases i with
    | zero => simp
    | succ i =>
      simp only [List.flatMap_cons, List.append_assoc, Nat.succ_mul, List.getElem_cons_succ]
      rw [show i*w+w = (f a).length + i*w by rw [hw, Nat.add_comm], List.drop_length_add_append]
      exact ih i (by simpa using hi)

private theorem encodedDigits_cell (w Q z e : ℕ) (suffix : List Bool) (j : ℕ) (hj : j < z) :
    (((encodedDigits w Q z e ++ suffix).drop (j*w)).take w) =
      PrimedCounter.digits w (e / Q ^ (z-1-j) % Q) := by
  let fields := EvaluatorRadixDivision.radixDigits Q z e
  have hlen : fields.length = z := by simp [fields, EvaluatorRadixDivision.radixDigits_eq]
  have hi : j < fields.length := hlen.symm ▸ hj
  have hbits (n : ℕ) : (PrimedCounter.digits w n).length = w := by simp [PrimedCounter.digits]
  have hval : fields[j] = e / Q ^ (z-1-j) % Q := by
    simp [fields, EvaluatorRadixDivision.radixDigits_eq, List.getElem_reverse]
  change (((fields.flatMap (PrimedCounter.digits w) ++ suffix).drop (j*w)).take w) = _
  rw [drop_field _ w hbits fields suffix j hi, List.take_append_of_le_length (hbits fields[j]).ge,
    List.take_of_length_le (hbits fields[j]).le, hval]

/-- Lookup at row `i`, column `j` returns the encoded digit for power
`z - 1 - j`. The suffix can carry any data already on the table stack. -/
theorem packedTable_cell {z : ℕ} (w Q : ℕ) (rows : List (BurstRAM.Word z)) (suffix : List Bool)
    (i j : ℕ) (hi : i < rows.length) (hj : j < z) :
    (((packedTable w Q rows ++ suffix).drop ((i*z+j)*w)).take w) =
      PrimedCounter.digits w (rows[i].val / Q ^ (z-1-j) % Q) := by
  let f (a : BurstRAM.Word z) := encodedDigits w Q z a.val
  have hlen (a : BurstRAM.Word z) : (f a).length = z*w := EvaluatorRadixDivision.encodedDigits_length ..
  have h := drop_field f (z*w) hlen rows suffix i hi
  change (((rows.flatMap f ++ suffix).drop ((i*z+j)*w)).take w) = _
  rw [Nat.add_mul, Nat.mul_assoc, ← List.drop_drop, h]
  exact encodedDigits_cell w Q z rows[i].val _ j hj

@[simp] theorem packedInput_length {z : ℕ} (rows : List (BurstRAM.Word z)) :
    (packedInput rows).length = rows.length*z := by
  simp [packedInput, List.length_flatMap]

/-- Reversing the RAM's ascending, little-endian binary word stream puts
both the rows and their bits into the input order of the conversion loop. -/
theorem packedInput_eq_reverse {z : ℕ} (rows : List (BurstRAM.Word z)) :
    packedInput rows = (rows.flatMap BurstRAM.wordBits).reverse := by
  induction rows with
  | nil => rfl
  | cons x xs ih =>
    simpa only [packedInput, List.reverse_cons, List.flatMap_append, List.flatMap_cons,
      List.flatMap_nil, List.append_nil, List.reverse_append] using
      congrArg (· ++ (BurstRAM.wordBits x).reverse) ih

/-- Entry point when the RAM's binary exponents are already on a separate
stack in increasing label order. The saved-candidate stack of the division
kernel is available to receive this stream before the first divide. -/
def nativeRows : FiniteRoutine Port :=
  (reverseOnto (.radix (.word .original)) .input).followedBy radixRows

theorem nativeRows_runs {z : ℕ} (rows : List (BurstRAM.Word z)) (suffix d acc : List Bool) (hq : 2 ≤ value d) :
    nativeRows.Runs (2*(rows.length*z)+1+rowsTicks rows.length z d.length)
      (Function.update (ready rows.length z suffix d acc) (.radix (.word .original))
        (rows.flatMap BurstRAM.wordBits))
      (ready 0 z suffix d (packedTable d.length (value d) rows ++ acc)) := by
  let src : Port := .radix (.word .original)
  let s := Function.update (ready rows.length z suffix d acc) src (rows.flatMap BurstRAM.wordBits)
  let u := ready rows.length z (packedInput rows ++ suffix) d acc
  have h₁ := reverseOnto_runs (src := src) (dst := Port.input) (by decide) s u rfl
    (show packedInput rows ++ suffix = (rows.flatMap BurstRAM.wordBits).reverse ++ suffix by
      rw [packedInput_eq_reverse]) (by
      intro k hk hk'
      cases k with
      | input => exact (hk' rfl).elim
      | rowCount | width => rfl
      | radix p => cases p with
        | rounds | digits => rfl
        | word j => cases j <;> first | rfl | exact (hk rfl).elim)
  have ht : (s src).length = rows.length*z := by
    simpa only [s, Function.update_self, packedInput_eq_reverse, List.length_reverse] using packedInput_length rows
  rw [ht] at h₁
  exact h₁.followedBy (radixRows_runs rows suffix d acc hq)

/-- Conversion directly from the serialized exponent array on a cut, using
the same word-array equivalence as the RAM transcript. -/
theorem native_array_runs {k z : ℕ} (e : Fin k → BurstRAM.Word z) (suffix d acc : List Bool)
    (hq : 2 ≤ value d) :
    nativeRows.Runs (2*(k*z)+1+rowsTicks k z d.length)
      (Function.update (ready k z suffix d acc) (.radix (.word .original))
        (List.ofFn (RAMSerialization.arrayBits k z e)))
      (ready 0 z suffix d (packedTable d.length (value d) (List.ofFn e) ++ acc)) := by
  have he := SuccessorFields.raw_eq_flatten_words (RAMSerialization.arrayBits k z e)
  simp only [Equiv.symm_apply_apply] at he
  simpa only [List.length_ofFn, he, List.flatMap_def, List.map_ofFn, Function.comp_def] using
    nativeRows_runs (List.ofFn e) suffix d acc hq

/-- Peak total bit storage during the whole table conversion is polynomial in
the number of labels and the two binary widths. The input suffix and any
previously accumulated digits are included in the bound. -/
theorem radixRows_space {z : ℕ} (rows : List (BurstRAM.Word z)) (suffix d acc : List Bool) (hq : 2 ≤ value d)
    {n : ℕ} {q : Option radixRows.State} {u : Stacks Port}
    (run : StackRuns radixRows.body.standalone n (some radixRows.body.entry)
      (ready rows.length z (packedInput rows ++ suffix) d acc) q u) :
    ∑ k, (u k).length ≤ 13 * (rows.length + z + rows.length*z + suffix.length + d.length + acc.length +
      rowsTicks rows.length z d.length) := by
  have hn := EvaluatorRadixDivision.ticks_le_at_return (radixRows_runs rows suffix d acc hq) (by rfl) run
  have bound (k : Port) :
      (u k).length ≤ rows.length + z + rows.length*z + suffix.length + d.length + acc.length +
        rowsTicks rows.length z d.length := by
    have h := EvaluatorRadixDivision.run_length run k
    have hi : (ready rows.length z (packedInput rows ++ suffix) d acc k).length ≤
        rows.length + z + rows.length*z + suffix.length + d.length + acc.length := by
      cases k with
      | input | width | rowCount => simp +arith [ready, frame]
      | radix p => cases p with
        | rounds | digits => simp [ready, frame, EvaluatorRadixDivision.bank]
        | word j => cases j <;> simp +arith [ready, frame, EvaluatorRadixDivision.bank, DivisionStack.Data.stacks]
    omega
  calc
    ∑ k, (u k).length ≤ ∑ _ : Port, (rows.length + z + rows.length*z + suffix.length + d.length + acc.length +
        rowsTicks rows.length z d.length) := Finset.sum_le_sum (fun k _ => bound k)
    _ = _ := by simp [show Fintype.card Port = 13 by decide]

end EvaluatorRadixRows

end VPVNP
end Computability
end OAI
