import OAI.Computability.VPVNP.SliceArithmeticPowerPorts
import OAI.Computability.VPVNP.StructuredStackLoop

/-!
# Binary powering on a bit stack

For every exponent bit the machine squares its current packed accumulator.
A set bit triggers a second multiplication by the preserved packed base.
Both uses of the multiplier enter and return with its entire workspace clean.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace SliceArithmetic.InverseCall

open RAMTape BurstRAM
open SliceArithmeticRound (packed)

private def queryPort : Port := .inl (.inr .query)
private def accPort : Port := .inl (.inr .acc)

/-- Copy the selected source to the consumed operand and run the reusable multiplier. -/
private def multiplyFrom (src : Port) : FiniteRoutine Port :=
  (SuccessorFields.prependCopy src queryPort (.inr .scratch)).followedBy
    (MultiplyCall.machine.onPorts Sum.inl)

private def bitBody (b : Bool) : FiniteRoutine Port :=
  if b then (multiplyFrom accPort).followedBy (multiplyFrom (.inr .base)) else multiplyFrom accPort

/-- Consume the exponent in high-bit-first order, squaring at every bit and multiplying by the
base for each set bit. -/
def powerMachine : FiniteRoutine Port := FiniteRoutine.ofRoutine <|
  Routine.popLoop (.inr .bits) (fun _ => true) (bitBody false).body (bitBody true).body

/-- Step bound for processing one exponent bit, allowing both a square and a multiplication by
the base. -/
def bitCap (e w : ℕ) : ℕ := 2 * (5*(e*w)+2+MultiplyCall.callCap e w)

variable {p e w : ℕ} [Fact p.Prime]

private def phase (c x v : Vector p e) (b : Bool) : Vector p e :=
  if b then mul c (mul c v v) x else mul c v v

private theorem commutative_mul (c x y : Vector p e) : mul c x y = mul c y x := by
  apply value_injective (modulus_monic c) (modulus_natDegree c)
  rw [value_mul, value_mul, mul_comm]

private theorem multiplyFrom_runs (he : 0 < e) (hw : Word.workingWidth p ≤ w)
    (fromBase : Bool) (c x v : Vector p e) (advice bits : List Bool) :
    let src := if fromBase then .inr Extra.base else accPort
    let a := if fromBase then x else v
    let cb := packed w (List.ofFn c)
    let xb := packed w (List.ofFn x)
    ∃ t ≤ 5*(e*w)+2+MultiplyCall.callCap e w, (multiplyFrom src).Runs t
      (frame p e w cb xb advice bits (packed w (List.ofFn v)) [])
      (frame p e w cb xb advice bits (packed w (List.ofFn (mul c a v))) []) := by
  intro src a cb xb
  let vb := packed w (List.ofFn v)
  let ab := packed w (List.ofFn a)
  let yb := packed w (List.ofFn (mul c a v))
  let input := frame p e w cb xb advice bits vb []
  let output := frame p e w cb xb advice bits yb []
  let middle := Function.update input queryPort ab
  have hsrc : src ≠ queryPort ∧ src ≠ (.inr .scratch : Port) := by cases fromBase <;> decide
  have copy := SuccessorFields.prependCopy_runs src queryPort (.inr .scratch) hsrc.1 hsrc.2
    (by decide) input rfl
  have ha : input src = ab := by cases fromBase <;> rfl
  rw [ha, show input queryPort = [] from rfl, List.append_nil, show ab.length = e*w by simp [ab]] at copy
  obtain ⟨m, hm, hmul⟩ := MultiplyCall.machine_runs he hw c a v
  have installed : (MultiplyCall.machine.onPorts Sum.inl).Runs m middle output := by
    apply MultiplyCall.machine.runs_onPorts_framed Sum.inl_injective hmul
    · rintro (k | k)
      · rfl
      · cases k <;> rfl
    · intro k; rfl
    · rintro (k | k) h
      · exact (h k rfl).elim
      · rfl
  exact ⟨_, by omega, copy.followedBy installed⟩

private theorem bitBody_runs (he : 0 < e) (hw : Word.workingWidth p ≤ w)
    (c x v : Vector p e) (b : Bool) (advice bits : List Bool) :
    let cb := packed w (List.ofFn c)
    let xb := packed w (List.ofFn x)
    ∃ t ≤ bitCap e w, (bitBody b).Runs t
      (frame p e w cb xb advice bits (packed w (List.ofFn v)) [])
      (frame p e w cb xb advice bits (packed w (List.ofFn (phase c x v b))) []) := by
  intro cb xb
  obtain ⟨t, ht, square⟩ := multiplyFrom_runs he hw false c x v advice bits
  cases b with
  | false => exact ⟨t, by unfold bitCap; omega, square⟩
  | true =>
    obtain ⟨u, hu, byBase⟩ := multiplyFrom_runs he hw true c x (mul c v v) advice bits
    simp only [↓reduceIte] at byBase
    rw [commutative_mul c x (mul c v v)] at byBase
    exact ⟨_, by unfold bitCap; omega, square.followedBy byBase⟩

/-- The finite powering control consumes every bit of its input stack. -/
theorem powerMachine_runs (he : 0 < e) (hw : Word.workingWidth p ≤ w)
    (c x v : Vector p e) (advice bits : List Bool) :
    let cb := packed w (List.ofFn c)
    let xb := packed w (List.ofFn x)
    ∃ t ≤ bits.length * (bitCap e w + 1) + 1, powerMachine.Runs t
      (frame p e w cb xb advice bits (packed w (List.ofFn v)) [])
      (frame p e w cb xb advice [] (packed w (List.ofFn (bits.foldl (phase c x) v))) []) := by
  intro cb xb
  induction bits generalizing v with
  | nil =>
    exact ⟨1, by simp, Routine.Runs.popLoop_empty (.inr Extra.bits : Port) (fun _ => true)
      (bitBody false).body (bitBody true).body (s := frame p e w cb xb advice [] (packed w (List.ofFn v)) []) rfl⟩
  | cons b bs ih =>
    obtain ⟨t, ht, head⟩ := bitBody_runs he hw c x v b advice bs
    obtain ⟨u, hu, tail⟩ := ih (phase c x v b)
    let bank := fun bits (a : Vector p e) => frame p e w cb xb advice bits (packed w (List.ofFn a)) []
    have hupdate : Function.update (bank (b::bs) v) (.inr .bits) bs = bank bs v := by
      funext k
      rcases k with i | i
      · rfl
      · cases i <;> rfl
    change (Routine.popLoop (.inr Extra.bits : Port) (fun _ => true) (bitBody false).body
      (bitBody true).body).Runs u (bank bs (phase c x v b)) (bank [] _) at tail
    have run := Routine.Runs.popLoop_continue (.inr Extra.bits : Port) (fun _ => true)
      (bitBody false).body (bitBody true).body (s := bank (b::bs) v) (mid := bank bs (phase c x v b))
      (b := b) (tail := bs) rfl rfl (by rw [hupdate]; cases b <;> exact head) tail
    exact ⟨_, by rw [List.length_cons, Nat.succ_mul]; omega, run⟩

private theorem fold_phase_eq (c x : Vector p e) (bits : List Bool) (v : Vector p e) :
    bits.foldl (phase c x) v =
      (bits.flatMap fun b => if b then [PowerStep.square, .multiplyBase] else [.square]).foldl
        (PowerStep.run c x) v := by
  induction bits generalizing v with
  | nil => rfl
  | cons b bits ih =>
    rw [List.flatMap_cons, List.foldl_append, List.foldl_cons, ih]
    cases b <;> rfl

/-- The canonical binary expansion computes the vector power. -/
theorem power_runs (he : 0 < e) (hw : Word.workingWidth p ≤ w)
    (c x : Vector p e) (advice : List Bool) (n : ℕ) :
    let cb := packed w (List.ofFn c)
    let xb := packed w (List.ofFn x)
    ∃ t ≤ n.size * (bitCap e w + 1) + 1, powerMachine.Runs t
      (frame p e w cb xb advice n.bits.reverse (packed w (List.ofFn (one p e))) [])
      (frame p e w cb xb advice [] (packed w (List.ofFn (pow c x n))) []) := by
  simpa only [fold_phase_eq, pow, powerSteps, List.length_reverse, Nat.size_eq_bits_len] using
    powerMachine_runs he hw c x (one p e) advice n.bits.reverse

/-- A most-significant-bit-first exponent may retain its leading zero bits. -/
theorem power_word_runs (he : 0 < e) (hw : Word.workingWidth p ≤ w)
    (c x : Vector p e) (advice bits : List Bool) :
    let cb := packed w (List.ofFn c)
    let xb := packed w (List.ofFn x)
    ∃ t ≤ bits.length * (bitCap e w + 1) + 1, powerMachine.Runs t
      (frame p e w cb xb advice bits (packed w (List.ofFn (one p e))) [])
      (frame p e w cb xb advice [] (packed w (List.ofFn (pow c x (TapeWord.value bits.reverse)))) []) := by
  let : NeZero e := ⟨Nat.ne_of_gt he⟩
  have hval : value (modulus c) (bits.foldl (phase c x) (one p e)) =
      value (modulus c) x ^ TapeWord.value bits.reverse := by
    induction bits using List.reverseRecOn with
    | nil => simp [TapeWord.value]
    | append_singleton bs b ih =>
      cases b <;> simp [phase, value_mul, ih, TapeWord.value, two_mul, pow_add]
      ring
  have hfold : bits.foldl (phase c x) (one p e) = pow c x (TapeWord.value bits.reverse) := by
    apply value_injective (modulus_monic c) (modulus_natDegree c)
    rw [hval, value_pow]
  simpa only [hfold] using powerMachine_runs he hw c x (one p e) advice bits

/-- A zero base and a zero initial accumulator stay zero, including the empty exponent. -/
theorem power_zero_runs (he : 0 < e) (hw : Word.workingWidth p ≤ w)
    (c : Vector p e) (advice bits : List Bool) :
    let cb := packed w (List.ofFn c)
    let zb := packed w (List.ofFn (zero p e))
    ∃ t ≤ bits.length * (bitCap e w + 1) + 1, powerMachine.Runs t
      (frame p e w cb zb advice bits zb []) (frame p e w cb zb advice [] zb []) := by
  have hmul : mul c (zero p e) (zero p e) = zero p e := by
    apply value_injective (modulus_monic c) (modulus_natDegree c)
    simp [value_mul]
  have hfold : bits.foldl (phase c (zero p e)) (zero p e) = zero p e := by
    induction bits with
    | nil => rfl
    | cons b bs ih =>
      cases b <;> simpa only [List.foldl_cons, phase, Bool.false_eq_true, ↓reduceIte, hmul] using ih
  simpa only [hfold] using powerMachine_runs he hw c (zero p e) (zero p e) advice bits

end SliceArithmetic.InverseCall

end VPVNP
end Computability
end OAI
