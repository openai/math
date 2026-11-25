import OAI.Computability.NearSquareRoot.KernelPassMixError
import OAI.Computability.NearSquareRoot.KernelPassMixValue
import OAI.Computability.IntegerMultiplication.Toom.Evaluate

/-! # Fixed-coefficient mixing on encoded complex records

Each coefficient row has a fixed common binary denominator. Multiply the decoded signed
magnitudes by fixed integers, add with arbitrary-length signed accumulators, truncate once
by a binary shift, and then re-encode the width requested on the ruler. Cost is linear
in the combined lengths of the records, for the whole fixed coefficient matrix.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace KernelPassMix

open IntegerMultiplication IntegerMultiplication.Code KernelPass

def natScale (n : ℕ) (s : Grid.S) : Grid.S := (s.1, Bits.scale n s.2)

private theorem natScale_easy (n : ℕ) : Easy (natScale n) :=
  Easy.fst.pair (Bits.easy_scale n Easy.snd)

private theorem whole_natScale (n : ℕ) (s : Grid.S) :
    Grid.whole (natScale n s) = n * Grid.whole s := by
  simp only [Grid.whole, natScale, Bits.scale_exact, Nat.cast_mul]
  ring

/-- Signed scaling by a template numerator, with the magnitude multiplication compiled
using the P192 fixed-integer word program. -/
def signedScale : ℤ → Grid.S → Grid.S
  | .ofNat n => natScale n
  | .negSucc n => fun s => Grid.neg (natScale (n+1) s)

private theorem signedScale_easy (c : ℤ) : Easy (signedScale c) := by
  cases c with
  | ofNat n => exact natScale_easy n
  | negSucc n => exact (natScale_easy _).compose Grid.easy_neg

private theorem whole_signedScale (c : ℤ) (s : Grid.S) :
    Grid.whole (signedScale c s) = c * Grid.whole s := by
  cases c with
  | ofNat n => exact whole_natScale n s
  | negSucc n => simp only [signedScale, Grid.neg_r, whole_natScale, Int.negSucc_eq, neg_mul, Nat.cast_succ]

def scaleRecord (c : ℤ) (s : Grid.Coef) : Grid.Coef :=
  (signedScale c s.1, signedScale c s.2)

private theorem scaleRecord_easy (c : ℤ) : Easy (scaleRecord c) :=
  (Easy.fst.compose (signedScale_easy c)).pair (Easy.snd.compose (signedScale_easy c))

private theorem content_scaleRecord (c : ℤ) (x : Grid.Coef) :
    Grid.content (scaleRecord c x) = c • Grid.content x := by
  apply QuadraticAlgebra.ext <;> simp [Grid.content, scaleRecord, whole_signedScale]

private def zeroRecord : Grid.Coef := ((false, []), (false, []))

private theorem content_zeroRecord : Grid.content zeroRecord = 0 := by
  apply QuadraticAlgebra.ext <;> simp [Grid.content, zeroRecord, Grid.whole]

def sumRecords {i : ℕ} (v : Fin i → Grid.Coef) : Grid.Coef :=
  (List.ofFn v).foldr (fun a b => Grid.plusG (a,b)) zeroRecord

private theorem sumRecords_easy {X : Type*} [Codec X] {i : ℕ} (v : Fin i → X → Grid.Coef)
    (hv : ∀ j, Easy (v j)) : Easy (fun z => sumRecords (fun j => v j z)) := by
  induction i with
  | zero => simpa [sumRecords] using (Easy.const zeroRecord : Easy (fun _ : X => zeroRecord))
  | succ i ih =>
    simp only [sumRecords, List.ofFn_succ, List.foldr_cons]
    exact ((hv 0).pair (ih (fun j => v j.succ) (fun j => hv _))).compose Grid.facile_G

private theorem content_sumRecords {i : ℕ} (v : Fin i → Grid.Coef) :
    Grid.content (sumRecords v) = ∑ j, Grid.content (v j) := by
  induction i with
  | zero => simp [sumRecords, content_zeroRecord]
  | succ i ih =>
    rw [Fin.sum_univ_succ]
    change Grid.content ((List.ofFn v).foldr _ _) = _
    rw [List.ofFn_succ, List.foldr_cons, Grid.key_P, ← ih]
    rfl

/-- Accumulate a full row on the sign-and-magnitude representation. -/
def accumulateRow {i : ℕ} (r : Fin i → Coefficient) (xs : List Dusk.Pair) : Grid.Coef :=
  sumRecords (fun j => scaleRecord (numerator (denom r) (r j))
    (Grid.disp (Iter.pick ([], []) (xs, tally j.val))))

private theorem accumulateRow_easy {i : ℕ} (r : Fin i → Coefficient) :
    Easy (accumulateRow r) := by
  apply sumRecords_easy
  intro j
  exact (((Easy.identity.pair (Easy.const (tally j.val))).compose
    (Iter.facile (([], []) : Dusk.Pair))).compose Grid.disp_easy).compose (scaleRecord_easy _)

theorem content_accumulateRow {i w : ℕ} (r : Fin i → Coefficient) (v : Fin i → Dusk.Grain w) :
    Grid.content (accumulateRow r (List.ofFn (fun j => Dusk.mark (v j)))) =
      accum r (Grid.aspect ∘ v) := by
  unfold accumulateRow accum
  rw [content_sumRecords]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Iter.entry, content_scaleRecord, Grid.pullG]
  rfl

/-- The output width ruler counts magnitude bits including the sign-code redundancy. -/
def mixMarked {i o : ℕ} (c : Fin o → Fin i → Coefficient)
    (a : Tally × List Dusk.Pair) : List Dusk.Pair :=
  List.ofFn fun b => Grid.spell (Grid.fit (a.1,
    Grid.rest (tally (denom (c b)), accumulateRow (c b) a.2)))

theorem mixMarked_easy {i o : ℕ} (c : Fin o → Fin i → Coefficient) : Easy (mixMarked c) := by
  apply Toom.easy_ofFn
  intro b
  exact (Easy.fst.pair (((Easy.const (tally (denom (c b)))).pair
    (Easy.snd.compose (accumulateRow_easy (c b)))).compose Grid.rest_easy)).compose
      (Grid.fit_easy.compose Grid.spell_easy)

def rounded {i w : ℕ} (r : Fin i → Coefficient) (v : Fin i → Dusk.Grain w) : Dusk.Grain w :=
  Grid.wrapMap w (Grid.divA (denom r) (accum r (Grid.aspect ∘ v)))

theorem mixMarked_exact {i o w : ℕ} (c : Fin o → Fin i → Coefficient) (v : Fin i → Dusk.Grain w)
    (headroom : ∀ b, Grid.focus w (Grid.divA (denom (c b)) (accum (c b) (Grid.aspect ∘ v)))) :
    mixMarked c (tally (w+1), List.ofFn (fun j => Dusk.mark (v j))) =
      List.ofFn (fun b => Dusk.mark (rounded (c b) v)) := by
  apply congrArg List.ofFn
  funext b
  dsimp only [mixMarked, rounded]
  rw [spell_rounded, content_accumulateRow]
  rw [content_accumulateRow]
  exact headroom b

end KernelPassMix

end NearSquareRoot
end Computability
end OAI
