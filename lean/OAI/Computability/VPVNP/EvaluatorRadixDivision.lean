import OAI.Computability.VPVNP.PrimedCounterBits
import OAI.Computability.VPVNP.RAMTapeDivision
import OAI.Computability.VPVNP.RAMTapeRoutinePorts
import OAI.Computability.VPVNP.StructuredStackLoop

/-!
# Binary-to-radix conversion for the streamed evaluator

The input exponent is a most-significant-bit-first binary stack. A fixed
restoring division table handles a divisor of any positive value, independently
of the dividend width. One division round returns the quotient in the original
input format and prepends a divisor-width little-endian remainder to the digit
stack. The loop count is supplied on a unary stack. Hence the output starts
with the most significant requested digit, including leading zero digits.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace EvaluatorRadixDivision

open RAMTape TapeWord

/-- The restoring-division registers, the unary count of remaining divisions and the stack of
accumulated radix digits. -/
inductive Port where
  | word (k : DivisionStack.Port)
  | rounds
  | digits
  deriving DecidableEq, Fintype

/-- The control consumes the source in head order, pushing onto the destination. -/
def reverseOnto {K : Type} (src dst : K) : FiniteRoutine K :=
  .ofRoutine (Routine.popLoop src (fun _ => true) (Routine.push dst false) (Routine.push dst true))

theorem reverseOnto_runs {K : Type} [DecidableEq K] {src dst : K} (hne : src ≠ dst)
    (s u : Stacks K) (hs : u src = []) (hd : u dst = (s src).reverse ++ s dst)
    (hframe : ∀ k, k ≠ src → k ≠ dst → u k = s k) :
    (reverseOnto src dst).Runs (2 * (s src).length + 1) s u := by
  generalize hx : s src = xs at *
  induction xs generalizing s with
  | nil =>
    have hu : u = s := by
      funext k
      by_cases h : k = src
      · subst k; exact hs.trans hx.symm
      by_cases h' : k = dst
      · subst k; simpa using hd
      exact hframe k h h'
    rw [hu]
    exact Routine.Runs.popLoop_empty src (fun _ => true) (Routine.push dst false) (Routine.push dst true) hx
  | cons b xs ih =>
    let a := Function.update s src xs
    let v := Function.update a dst (b :: s dst)
    have va : v src = xs := by simp [v, a, hne]
    have ad : a dst = s dst := Function.update_of_ne hne.symm ..
    have hpush : (Routine.push dst b).Runs 1 a v := by
      simpa only [v, ad] using Routine.runs_push dst b a
    have hrest : (reverseOnto src dst).Runs (2 * xs.length + 1) v u := by
      apply ih v
      all_goals first
        | exact va
        | simpa [v, List.reverse_cons, List.append_assoc] using hd
        | exact fun k hk hk' => by simpa [v, a, hk, hk'] using hframe k hk hk'

    have run := Routine.Runs.popLoop_continue src (fun _ => true) (Routine.push dst false)
      (Routine.push dst true) hx rfl (by cases b <;> exact hpush) hrest
    rw [show 2 * (b :: xs).length + 1 = 1 + 1 + (2 * xs.length + 1) by
      simp only [List.length_cons]; omega]
    exact run

/-- The machine's integer inputs and scratch are precisely the division word
ports. The counter and the growing digit string belong to the caller's loop. -/
def bank (rounds : ℕ) (w : DivisionStack.Data) (acc : List Bool) : Stacks Port
  | .word k => w.stacks k
  | .rounds => List.replicate rounds true
  | .digits => acc

/-- The bank at a division-round boundary, containing the reversed dividend, divisor,
remaining-round tally and accumulated digits. -/
def ready (rounds : ℕ) (x d acc : List Bool) : Stacks Port :=
  bank rounds ⟨[], x.reverse, d, [], [], [], [], []⟩ acc

private def divRoutine : FiniteRoutine Port :=
  .ofStackCode DivisionStack.code Port.word .reverseInput (· == .done)

/-- One radix-conversion round. Divide the dividend, install the quotient for the next round
and prepend the remainder bits to the digit stack. -/
def digitRoutine : FiniteRoutine Port :=
  let input := reverseOnto (.word .feed) (.word .input)
  let quot := reverseOnto (.word .quotient) (.word .feed)
  let save := reverseOnto (.word .remainder) (.word .original)
  let emit := reverseOnto (.word .original) .digits
  (((input.followedBy divRoutine).followedBy quot).followedBy save).followedBy emit

/-- Positive-divisor division accepts arbitrary, possibly unequal widths. -/
theorem divide_spec (x d : List Bool) (h : 0 < value d) :
    let t := divideWords x d
    t.1.length = x.length ∧ t.2.length = d.length ∧
    value t.1 = value x / value d ∧ value t.2 = value x % value d := by
  have hd := (anyBit_iff d).mpr h
  obtain ⟨h₁, h₂, hlt, he⟩ := dividePass_spec d x h
  simp only [divideWords, hd, ↓reduceIte]
  refine ⟨h₁, h₂, ?_, ?_⟩
  · rw [← he, Nat.mul_add_div h, Nat.div_eq_of_lt hlt, Nat.add_zero]
  · rw [← he, Nat.mul_add_mod, Nat.mod_eq_of_lt hlt]

/-- One complete divide-and-emit pass, measured in elementary bit instructions. -/
def digitTicks (z w : ℕ) := z * (10*w+10) + 9*w + 8

private theorem framed_divide (rounds : ℕ) (x d acc : List Bool) :
    let out := divideWords x d
    divRoutine.Runs (DivisionStack.ticks x d) (bank rounds ⟨x,[],d,[],[],[],[],[]⟩ acc)
      (bank rounds ⟨[],[],d,out.2,out.1,[],[],[]⟩ acc) := by
  have hh (q : DivisionStack.State) (h : (q == DivisionStack.State.done) = true) :
      (DivisionStack.code q).returns = true := by
    have : q = DivisionStack.State.done := by simpa using h
    subst q; rfl
  apply FiniteRoutine.runs_ofStackCode_framed (normal := (· == DivisionStack.State.done))
    (ports := Port.word) (fun _ _ => Port.word.inj) (by decide) (by decide) hh (DivisionStack.divideRun x d)
  · intro k; rfl
  · intro k; rfl
  · intro k hk
    cases k with
    | word j => exact (hk j rfl).elim
    | rounds | digits => rfl

local macro "frame_cases" : tactic =>
  `(tactic| (intro k hk hk'; cases k with
    | word j => cases j <;> first | rfl | exact (hk rfl).elim | exact (hk' rfl).elim
    | rounds | digits => first | rfl | exact (hk rfl).elim | exact (hk' rfl).elim))

theorem digitRoutine_runs (rounds : ℕ) (x d acc : List Bool) (hd : 0 < value d) :
    let out := divideWords x d
    digitRoutine.Runs (digitTicks x.length d.length) (ready rounds x d acc)
      (ready rounds out.1 d (out.2 ++ acc)) := by
  let out := divideWords x d
  let a := bank rounds ⟨x,[],d,[],[],[],[],[]⟩ acc
  let b := bank rounds ⟨[],[],d,out.2,out.1,[],[],[]⟩ acc
  let c := bank rounds ⟨[],out.1.reverse,d,out.2,[],[],[],[]⟩ acc
  let e := bank rounds ⟨[],out.1.reverse,d,[],[],[],out.2.reverse,[]⟩ acc
  have h₁ := reverseOnto_runs (src := Port.word .feed) (dst := .word .input) (by decide)
    (ready rounds x d acc) a rfl
    (show x = x.reverse.reverse ++ [] by simp) (by frame_cases)
  have h₂ : divRoutine.Runs (DivisionStack.ticks x d) a b := framed_divide rounds x d acc
  have h₃ := reverseOnto_runs (src := Port.word .quotient) (dst := .word .feed) (by decide)
    b c rfl (show out.1.reverse = out.1.reverse ++ [] by simp) (by frame_cases)
  have h₄ := reverseOnto_runs (src := Port.word .remainder) (dst := .word .original) (by decide)
    c e rfl (show out.2.reverse = out.2.reverse ++ [] by simp) (by frame_cases)
  have h₅ := reverseOnto_runs (src := Port.word .original) (dst := .digits) (by decide)
    e (ready rounds out.1 d (out.2 ++ acc)) rfl
    (show out.2 ++ acc = out.2.reverse.reverse ++ acc by simp) (by frame_cases)
  obtain ⟨hq, hr, _, _⟩ := divide_spec x d hd
  have ht := (((h₁.followedBy h₂).followedBy h₃).followedBy h₄).followedBy h₅
  have hc : digitTicks x.length d.length =
      2 * x.reverse.length + 1 + DivisionStack.ticks x d + (2*out.1.length+1) +
      (2*out.2.length+1) + (2*out.2.reverse.length+1) := by
    simp only [digitTicks, DivisionStack.ticks, (anyBit_iff d).mpr hd, ↓reduceIte, out,
      List.length_reverse, hq, hr]
    ring
  dsimp only
  rw [hc]
  exact ht

/-- A fixed number of base-`Q` digits, ordered from the most to the least
significant, as in the Frobenius evaluator. -/
def radixDigits (Q : ℕ) : ℕ → ℕ → List ℕ
  | 0, _ => []
  | k + 1, e => radixDigits Q k (e / Q) ++ [e % Q]

/-- The digit in place `j` is the residue of the quotient by `Q ^ j`. The
stack exposes the highest place first. -/
theorem radixDigits_eq (Q rounds e : ℕ) :
    radixDigits Q rounds e =
      (List.range rounds).reverse.map (fun j => e / Q^j % Q) := by
  induction rounds generalizing e with
  | zero => rfl
  | succ k ih =>
    simp [radixDigits, ih, List.range_succ_eq_map, List.map_reverse, List.map_map,
      Function.comp_def, Nat.div_div_eq_div_mul, pow_succ']

/-- Fixed-width little-endian encoding of each digit, concatenated without
separators. A reader knows the field width from the divisor. -/
def encodedDigits (w Q rounds e : ℕ) :=
  (radixDigits Q rounds e).flatMap (PrimedCounter.digits w)

@[simp] theorem encodedDigits_length (w Q rounds e : ℕ) :
    (encodedDigits w Q rounds e).length = rounds * w := by
  induction rounds generalizing e with
  | zero => simp [encodedDigits, radixDigits]
  | succ k ih =>
    simp only [encodedDigits, radixDigits, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
      List.append_nil, List.length_append, PrimedCounter.digits, BurstRAM.length_wordBits]
    rw [← encodedDigits, ih, Nat.succ_mul]

theorem digit_lt {Q : ℕ} (hq : 0 < Q) (rounds e : ℕ) {a : ℕ} (ha : a ∈ radixDigits Q rounds e) :
    a < Q := by
  induction rounds generalizing e with
  | zero => simp [radixDigits] at ha
  | succ k ih =>
    simp only [radixDigits, List.mem_append, List.mem_singleton] at ha
    exact ha.elim (ih _) (fun he => he ▸ Nat.mod_lt _ hq)

private theorem bits_value (x : List Bool) :
    PrimedCounter.digits x.length (value x) = x := by
  apply eq_of_length_value
  · simp [PrimedCounter.digits]
  · simp only [PrimedCounter.digits, value_wordBits, Fin.ofNat, Nat.mod_eq_of_lt (value_lt x)]

/-- Positive counter marks launch a divide-and-emit pass. Empty input to
the loop returns immediately. -/
def radixRoutine : FiniteRoutine Port :=
  .ofRoutine (Routine.popLoop .rounds (fun _ => true) (Routine.halt false) digitRoutine.body)

/-- Instruction count for the specified number of restoring-division rounds on a z-bit dividend
with a w-bit divisor. -/
def radixTicks (rounds z w : ℕ) := rounds * (digitTicks z w + 1) + 1

private theorem pop_round (rounds : ℕ) (x d acc : List Bool) :
    Function.update (ready (rounds + 1) x d acc) Port.rounds (List.replicate rounds true) =
      ready rounds x d acc := by
  funext k
  cases k <;> rfl

/-- Exact normal return of the fixed finite routine. It preserves the divisor,
retains the high quotient after the requested rounds, and emits exactly one
fixed-width binary block per round. -/
theorem radixRoutine_runs (rounds : ℕ) (x d acc : List Bool) (hd : 0 < value d) :
    radixRoutine.Runs (radixTicks rounds x.length d.length) (ready rounds x d acc)
      (ready 0 (PrimedCounter.digits x.length (value x / value d ^ rounds)) d
        (encodedDigits d.length (value d) rounds (value x) ++ acc)) := by
  induction rounds generalizing x acc with
  | zero =>
    simp only [pow_zero, Nat.div_one, bits_value]
    simpa [radixRoutine, FiniteRoutine.Runs, FiniteRoutine.ofRoutine, radixTicks, encodedDigits, radixDigits] using
      (Routine.Runs.popLoop_empty Port.rounds (fun _ => true) (Routine.halt false) digitRoutine.body
        (s := ready 0 x d acc) rfl)
  | succ k ih =>
    let t := divideWords x d
    obtain ⟨hq, hr, hvq, hvr⟩ := divide_spec x d hd
    have hdigit : t.2 = PrimedCounter.digits d.length (value x % value d) := by
      simpa only [t, hr, hvr] using (bits_value t.2).symm
    have hb := digitRoutine_runs k x d acc hd
    have h := Routine.Runs.popLoop_true_continue Port.rounds (fun _ => true)
      (Routine.halt false) digitRoutine.body
      (s := ready (k+1) x d acc) (mid := ready k t.1 d (t.2 ++ acc))
      (show ready (k+1) x d acc .rounds = true :: List.replicate k true from List.replicate_succ ..)
      rfl (by rw [pop_round]; exact hb) (ih t.1 (t.2 ++ acc))
    have hcost : radixTicks (k+1) x.length d.length =
        1 + digitTicks x.length d.length + radixTicks k t.1.length d.length := by
      simp only [radixTicks, t, hq, Nat.succ_mul]
      omega
    rw [hcost]
    simpa only [radixRoutine, FiniteRoutine.Runs, FiniteRoutine.ofRoutine, encodedDigits, radixDigits,
      List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
      List.append_nil, List.append_assoc, hdigit, t, hq, hvq, Nat.div_div_eq_div_mul, pow_succ'] using h

/-- A full input bit width of base-`Q` rounds suffices whenever `Q ≥ 2`.
Every such run leaves a zero quotient and all the digits of the exponent. -/
theorem full_radixRoutine_runs (x d acc : List Bool) (hq : 2 ≤ value d) :
    radixRoutine.Runs (radixTicks x.length x.length d.length) (ready x.length x d acc)
      (ready 0 (PrimedCounter.digits x.length 0) d
        (encodedDigits d.length (value d) x.length (value x) ++ acc)) := by
  have hfit := (value_lt x).trans_le (Nat.pow_le_pow_left hq x.length)
  simpa only [Nat.div_eq_of_lt hfit] using radixRoutine_runs x.length x d acc (by omega)

end EvaluatorRadixDivision

end VPVNP
end Computability
end OAI
