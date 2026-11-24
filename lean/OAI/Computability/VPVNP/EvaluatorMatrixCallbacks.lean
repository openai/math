import OAI.Computability.VPVNP.EvaluatorWeightedStep
import OAI.Computability.VPVNP.EvaluatorBinaryMachine

/-!
# Mounting the coordinate query in the monomial scheduler

A query sees the unary label number on one port and the weighted-step payload
on all other ports. The Frobenius and label entry readers use the same numeric
row and column representation. The remaining digit scheduler counters are
framed around the callbacks, so their sizes do not enter the query clock.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace Evaluator.MatrixCallbacks

open RAMTape SliceArithmetic WeightedStep
open EvaluatorDigitFetch (bank)

variable {P : Type} [DecidableEq P]

/-- The query's label-index port together with the weighted-step ports for matrix indices,
field arithmetic and callback data. -/
abbrev ReadPort (P : Type) := Unit ⊕ WeightedStep.Port P
/-- The surrounding digit-fetch bank with a weighted matrix-step register bank mounted as its
work payload. -/
abbrev Host (P : Type) := EvaluatorDigitFetch.Port (WeightedStep.Port P)

/-- Only the label index of the outer schedule is shared with its entry reader. -/
def mount : ReadPort P → Host P
  | .inl _ => .addr .labelIndex
  | .inr k => .work k

omit [DecidableEq P] in
private theorem mount_injective : Function.Injective (mount (P := P)) := by
  intro a b h
  rcases a with (⟨⟩ | a) <;> rcases b with (⟨⟩ | b) <;> cases h <;> rfl

/-- The read ABI, with the label ordinal in unary. -/
def queryBank (label : List Bool) (s : Stacks (WeightedStep.Port P)) : Stacks (ReadPort P) :=
  Sum.elim (fun _ ↦ label) s

/-- Fixed outer callback for either the Frobenius or the label multiplication
query. The differing query controls are installed in the same ports. -/
def machine (read : FiniteRoutine (ReadPort P)) : FiniteRoutine (Host P) :=
  WeightedStep.callback EvaluatorDigitFetch.Port.work (read.onPorts mount)

variable {p e w v : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K]
    {c : Vector p e} (φ : AdjoinRoot (modulus c) ≃ₐ[ZMod p] K)
    (dim : BurstRAM.Word v) (extra : Stacks P)

local notation "wb" j => BurstRAM.wordBits (Fin.castLE dim.isLt.le j : BurstRAM.Word v)
local notation "base" => (fun i n q a ↦ WeightedStep.bank φ w dim i n q a extra)

private theorem query_frame (read : FiniteRoutine (ReadPort P)) (ambient : Stacks (Host P))
    {s s' : Stacks (WeightedStep.Port P)} {d : ℕ}
    (h : read.Runs d (queryBank (ambient (.addr .labelIndex)) s)
      (queryBank (ambient (.addr .labelIndex)) s')) :
    (read.onPorts mount).Runs d (installStacks EvaluatorDigitFetch.Port.work ambient s)
      (installStacks EvaluatorDigitFetch.Port.work ambient s') := by
  have hw : Function.Injective (EvaluatorDigitFetch.Port.work (P := WeightedStep.Port P)) :=
    fun _ _ h ↦ EvaluatorDigitFetch.Port.work.inj h
  have hlookup (b : Stacks (WeightedStep.Port P)) (k : ReadPort P) :
      installStacks EvaluatorDigitFetch.Port.work ambient b (mount k) =
        queryBank (ambient (.addr .labelIndex)) b k := by
    cases k with
    | inl => exact installStacks_outside _ _ (fun _ h ↦ by cases h)
    | inr => exact installStacks_at hw ..
  apply read.runs_onPorts_framed mount_injective h (hlookup _) (hlookup _)
  intro k hk
  have hn (a : WeightedStep.Port P) : EvaluatorDigitFetch.Port.work a ≠ k := hk (.inr a)
  rw [installStacks_outside _ _ hn, installStacks_outside _ _ hn]

/-- From an actual deterministic entry reader, the complete callback
satisfies the bounded-delay law of the digit scheduler, with its label counter
and other outer registers preserved. -/
theorem count_callback (he : 0 < e) (hw : Word.workingWidth p ≤ w)
    (read : FiniteRoutine (ReadPort P)) (ambient : Stacks (Host P))
    (matrix : Matrix (Fin dim.val) (Fin dim.val) K) (i : Fin dim.val) (a : K)
    (queryTicks : ℕ)
    (query : ∀ j : Fin dim.val, ∃ time ≤ queryTicks, read.Runs time
      (queryBank (ambient (.addr .labelIndex)) (base i (wb j) [] a))
      (queryBank (ambient (.addr .labelIndex)) (base i (wb j) (bits φ w (matrix i j)) a)))
    (fuel : ℕ) (hfuel : WeightedStep.ticks v e w queryTicks ≤ fuel) :
    ∃ delay : Fin dim.val → ℕ, (∀ j, delay j ≤ WeightedStep.ticks v e w queryTicks) ∧
      ∀ cont, (machine read).body.count cont fuel
        (installStacks EvaluatorDigitFetch.Port.work ambient (base i [] [] a)) =
        ∑ j, cont (fuel-delay j)
          (installStacks EvaluatorDigitFetch.Port.work ambient (base j [] [] (a*matrix i j))) := by
  apply WeightedStep.callback_count φ EvaluatorDigitFetch.Port.work
    (fun _ _ h ↦ EvaluatorDigitFetch.Port.work.inj h) ambient extra dim he hw (read.onPorts mount)
    matrix i a queryTicks _ fuel hfuel
  intro j
  obtain ⟨time, ht, hrun⟩ := query j
  exact ⟨time, ht, query_frame read ambient hrun⟩

/-- Identify the fixed ports from which the final routine reads. -/
def outputPort : Output.Port → WeightedStep.Port P
  | .index => .indices .current
  | .width => .width
  | .product => .arithmetic (.inr .acc)

omit [DecidableEq P] in
theorem outputPort_injective : Function.Injective (outputPort (P := P)) := by
  intro x y h
  cases x <;> cases y <;> cases h <;> rfl

omit [DecidableEq P] in
/-- On the compatible polynomial-basis advice, the real arithmetic bank meets
the terminal reader's exact low-limb and endpoint-index specifications. -/
theorem output_data [Fintype K] {d : ℕ} {c' : Vector p (d+1)}
    (φ' : AdjoinRoot (modulus c') ≃ₐ[ZMod p] K)
    (hc : ∀ x, SliceEvaluator.primeCoordinate p K (φ' (value (modulus c') x)) =
      ((x (0 : Fin (d+1))).val : ZMod p))
    (hw : Word.workingWidth p ≤ w) (i : Fin dim.val) (a : K) :
    ∃ tail, WeightedStep.bank φ' w dim i [] [] a extra ∘ outputPort =
      Output.bank (wb i) (List.replicate w true) (BurstRAM.wordBits
        (Word.limb w (⟨(SliceEvaluator.primeCoordinate p K a).val, ZMod.val_lt _⟩ : Fin p)) ++ tail) := by
  obtain ⟨low, tail, hl, hv⟩ := packed_primeCoordinate φ' hc hw a
  have he : low = Word.limb w (⟨(SliceEvaluator.primeCoordinate p K a).val, ZMod.val_lt _⟩ : Fin p) :=
    Fin.ext (by rw [Word.limb_val hw]; exact hv)
  refine ⟨tail, funext fun k ↦ ?_⟩
  cases k with
  | index | width => rfl
  | product => exact he ▸ hl

end Evaluator.MatrixCallbacks

end VPVNP
end Computability
end OAI
