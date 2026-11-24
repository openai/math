import OAI.Computability.VPVNP.EvaluatorCallbackMountSafety
import OAI.Computability.VPVNP.EvaluatorProgramInputBounds

/-! # Resource bounds for the native finite-algebra evaluator

The streaming coordinate routines supply independent time and peak bounds.
The arithmetic, digit loops and radix converter run with fixed control. The
bounds below apply to all their paths for every input exponent width.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace Evaluator.MatrixCallbacks

open RAMTape SliceArithmetic EvaluatorRoutineSafety EvaluatorChronologicalLoop
  EvaluatorProgramMonomial EvaluatorProgramRawInput
open EvaluatorDigitFetch (bank)
open EvaluatorMonomialSchedule (budget)

variable {P : Type} [DecidableEq P] {p e w v t Z : ℕ} [Fact p.Prime]
    {K : Type} [Field K] [Algebra (ZMod p) K] {c : Vector p e}
    (φ : AdjoinRoot (modulus c) ≃ₐ[ZMod p] K) (dim : BurstRAM.Word v) (extra : Stacks P)
    (es : Fin t → BurstRAM.Word Z) (d : List Bool) (extraSpace : ℕ) (hextra : ∀ k, (extra k).length ≤ extraSpace)

local notation "pay" => payload φ dim extra w
local notation "tableBits" => EvaluatorRadixRows.packedTable d.length (TapeWord.value d) (List.ofFn es)
local notation "space" => workspace v e w extraSpace
local notation "ticks" => WeightedStep.ticks v e w

include hextra in
/-- The reachable-path and stopping contract for the entire converter and
scheduler, from the two concrete streamed-entry contracts. -/
theorem native_from_readers (he : 0 < e) (hw : Word.workingWidth p ≤ w) (hq : 2 ≤ TapeWord.value d)
    (frobenius label : FiniteRoutine (ReadPort P)) (F L peak : ℕ)
    (MF : Matrix (Fin dim.val) (Fin dim.val) K) (ML : Fin t → Matrix (Fin dim.val) (Fin dim.val) K)
    (hf : ReadsEntryWithin φ dim extra frobenius w 0 F peak MF)
    (hl : ∀ i : Fin t, ReadsEntryWithin φ dim extra label w i.val L peak (ML i)) :
    Bounded (nativeMachine (machine frobenius) (machine label)).body
      (stackFits (nativeSpace t Z d.length (space peak))) (EvaluatorProgramInput.initial es d ∘ pay)
      (fun x ↦ EvaluatorProgramInput.extend Z d (bank tableBits t Z d.length 0 0 0 0 (pay x)))
      (EvaluatorProgramInput.convertTicks t Z d.length + budget t Z d.length (TapeWord.value d) (ticks F) (ticks L)) :=
  native_bounded es d pay (space peak) (payload_length φ dim extra extraSpace hextra peak)
    (machine frobenius) (machine label) (ticks F) (ticks L) hq
    (frobenius_bounded φ dim extra es d extraSpace hextra he hw frobenius F peak MF hf)
    (label_bounded φ dim extra es d extraSpace hextra he hw label L peak ML hl)

/-- A uniform bit bound for the actual advice fields over every possible
path endpoint. The bound is independent of the exponent array. -/
def adviceCap (fields t divisorBits payloadSpace : ℕ) := 4*t+4*divisorBits+4 + fields*(2*payloadSpace+1)

include hextra in
omit [DecidableEq P] in
theorem advice_le (ps : List (WeightedStep.Port P)) (s : Fin dim.val × K) :
    (advice ps t d (pay s)).length ≤ adviceCap ps.length t d.length (WeightedStep.bankSpace v e w extraSpace) := by
  have hlen := WeightedStep.bank_length (w := w) φ extra dim extraSpace hextra s.1 [] [] (by simp) (by simp) s.2
  rw [advice_length]
  unfold adviceCap
  apply Nat.add_le_add_left
  induction ps with
  | nil => simp
  | cons k ks ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    conv_rhs => rw [Nat.succ_mul]
    have hk := hlen k
    change (pay s k).length ≤ _ at hk
    omega

/-- The deterministic preparation and field multiplication add a polynomial
term to each matrix query's clock. -/
theorem localTicks_polynomial {v e w : ℕ → ℕ} (hv : PolynomiallyBounded v)
    (he : PolynomiallyBounded e) (hw : PolynomiallyBounded w) :
    PolynomiallyBounded fun n ↦ WeightedStep.localTicks (v n) (e n) (w n) := by
  have hmul := (((PolynomiallyBounded.const 2000).mul ((he.add (.const 1)).pow 2)).mul
    ((hw.add (.const 1)).pow 2)).of_le (fun n ↦ MultiplyCall.callCap_le (e n) (w n))
  exact (((((PolynomiallyBounded.const 10).mul hv).add (.const 5)).add hmul).add
    (((PolynomiallyBounded.const 5).mul hv).add (.const 3)))

theorem workspace_polynomial {v e w h peak : ℕ → ℕ} (hv : PolynomiallyBounded v)
    (he : PolynomiallyBounded e) (hw : PolynomiallyBounded w)
    (hh : PolynomiallyBounded h) (hp : PolynomiallyBounded peak) :
    PolynomiallyBounded fun n ↦ workspace (v n) (e n) (w n) (h n) (peak n) :=
  ((((((hv.add he).add hw).add (he.mul hw)).add hh).add (localTicks_polynomial hv he hw)).add hp)

theorem adviceCap_polynomial (fields : ℕ) {t ℓ footprint : ℕ → ℕ}
    (ht : PolynomiallyBounded t) (hd : PolynomiallyBounded ℓ) (hf : PolynomiallyBounded footprint) :
    PolynomiallyBounded fun n ↦ adviceCap fields (t n) (ℓ n) (footprint n) :=
  ((((PolynomiallyBounded.const 4).mul ht).add ((PolynomiallyBounded.const 4).mul hd)).add (.const 4)).add
    ((PolynomiallyBounded.const fields).mul (((PolynomiallyBounded.const 2).mul hf).add (.const 1)))

end Evaluator.MatrixCallbacks

end VPVNP
end Computability
end OAI
