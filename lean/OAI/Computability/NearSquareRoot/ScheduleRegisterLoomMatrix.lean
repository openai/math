import OAI.Computability.NearSquareRoot.ScheduleRegisterLoomPayload
import OAI.Computability.NearSquareRoot.InterchangeROMTableArithmetic
import Mathlib.Data.List.FinRange

/-! # Four-register modular matrix instructions on packed interchange streams -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace LoomRegisters

open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Strip
open CommonRegisters Space InterchangeROMTable

/-- The ordinary input layout contains at least one actual column. Its first
stream supplies the record and payload delimiters. -/
def matrixPayloadCommand (p n m : ℕ) (coefficients : List (List ℕ)) : Cmd :=
  payloadCommand 0 (Series.natural m) (matrixTable p n coefficients)

theorem matrixPayload_within (p n m : ℕ) (coefficients : List (List ℕ)) :
    Within 4 (matrixPayloadCommand p n m coefficients) := payload_within ..

private theorem numeral_stripe {p n : ℕ} (x : Fin n → ZMod p) :
    stripe (Series.natural n) (fun k => numeral (x k).val) = numeralWord (residues x) := by
  simp only [numeralWord, residues, stripe_simple, Series.natural, Series.fixed]
  have eq : List.ofFn (fun i => (x i).val) = (List.finRange n).map (fun i => (x i).val) := by
    apply List.ext_getElem <;> simp
  rw [eq, Task.forest_map]

/-- At every payload address the same literal program multiplies the vector
of residue lanes by the supplied matrix over the actual residue ring. -/
theorem matrixPayload_bounded {p n m : ℕ} [NeZero p] (hn : 0 < n)
    (M : Matrix (Fin m) (Fin n) (ZMod p)) {A : Type} {P : A → Type}
    (rows : Series A) (payload : (a : A) → Series (P a)) (width : ℕ)
    (hw : ∀ a, (payload a).count ≤ width) (x : (a : A) → P a → Fin n → ZMod p)
    (env : Env) (r : Deck) (base : ℕ) (hr : DeckCap base r) :
    let coefficients := List.ofFn fun i => residues (M i)
    let D := payloadFactor n m (matrixTable p n coefficients) * (rows.count * (width + 1) + 1)
    BoundedFits env (matrixPayloadCommand p n m coefficients)
      (pile 0 (stripe (Series.natural n) fun k => stripe rows (fun a =>
        stripe (payload a) fun j => numeral (x a j k).val)) r)
      (pile 0 (stripe (Series.natural m) fun k => stripe rows (fun a =>
        stripe (payload a) fun j => numeral (M.mulVec (x a j) k).val)) r) D (base + D) D := by
  let k : Fin n := ⟨0, hn⟩
  have iz : (Series.natural n).explore.idxOf k = 0 := by
    simpa only [Series.natural, Series.fixed, List.idxOf_finRange] using (show k.val = 0 from rfl)
  have run := payload_bounded (Series.natural n) (Series.natural m) rows payload width hw k
    (fun a j z => numeral (x a j z).val) (fun a j z => numeral (M.mulVec (x a j) z).val)
    (matrixTable p n (List.ofFn fun i => residues (M i))) (fun a j => by
      simpa only [numeral_stripe] using matrixTable_correct M (x a j)) env r base hr
  simpa only [iz, Series.count_natural, matrixPayloadCommand] using run

/-- A matrix with no input columns outputs zeros. A shape-only physical lane
retains the otherwise absent record and payload delimiters. -/
theorem zeroMatrixPayload_bounded {p m : ℕ} (M : Matrix (Fin m) (Fin 0) (ZMod p))
    {A : Type} {P : A → Type} (rows : Series A) (payload : (a : A) → Series (P a)) (width : ℕ)
    (hw : ∀ a, (payload a).count ≤ width) (x : (a : A) → P a → Fin 0 → ZMod p)
    (env : Env) (r : Deck) (base : ℕ) (hr : DeckCap base r) :
    let tab := constantTable (Series.natural m) (fun _ => numeral 0)
    let D := payloadFactor 1 m tab * (rows.count * (width + 1) + 1)
    BoundedFits env (payloadCommand 0 (Series.natural m) tab)
      (pile 0 (stripe templateLane fun _ => stripe rows (fun a => stripe (payload a) fun _ => .atom false)) r)
      (pile 0 (stripe (Series.natural m) fun z => stripe rows (fun a =>
        stripe (payload a) fun j => numeral (M.mulVec (x a j) z).val)) r) D (base + D) D := by
  simpa only [Matrix.mulVec, dotProduct, Fintype.sum_empty, ZMod.val_zero, Series.count_natural] using
    constant_payload_bounded (Series.natural m) (fun _ => numeral 0) rows payload width hw env r base hr

end LoomRegisters

end NearSquareRoot
end Computability
end OAI
