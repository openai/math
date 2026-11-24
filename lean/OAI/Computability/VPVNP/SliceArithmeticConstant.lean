import OAI.Computability.VPVNP.SliceArithmeticEncoding
import OAI.Computability.VPVNP.RAMTapeWordOperands
import OAI.Computability.VPVNP.RAMTapeRoutinePorts

/-!
# Returning the field constants zero and one on bit stacks

The advised defining polynomial occupies exactly as many limbs as a scalar.
Its packed representation supplies the width template for a literal scan.
The scan restores the template and writes the selected constant in the
extension field's packed power-basis format.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace SliceArithmeticConstant

open SliceArithmetic SliceArithmeticRound RAMTape BurstRAM TapeWord

private def normal {A : Type} : Operand.State A → Bool
  | .done _ => true
  | _ => false

/-- Scan a packed width template to write the extension-field literal zero or one according to
`b`. -/
def machine (b : Bool) : FiniteRoutine ScanPort :=
  .ofStackCode (Operand.code (Operand.literalBit b.toNat)) id (.clear (Fin.last b.toNat)) normal

private theorem scan_runs (b : Bool) (template old : List Bool) :
    (machine b).Runs (old.length + 7 * template.length + 3) (scanStacks template [] [] old)
      (scanStacks template [] [] (wordBits (Fin.ofNat (2^template.length) b.toNat))) := by
  let W := template.length
  let x : BurstRAM.Word W := ⟨value template, value_lt template⟩
  have hx : wordBits x = template := eq_of_length_value (length_wordBits x) (value_wordBits x)
  obtain ⟨q, hr⟩ := Operand.literal_run b.toNat x old
  rw [hx] at hr
  apply FiniteRoutine.runs_ofStackCode_framed Function.injective_id rfl (exit := .done q) rfl ?_ hr
    (fun _ => rfl) (fun _ => rfl) (fun i hi => (hi i rfl).elim)
  intro i hi
  cases i <;> simp_all [normal, Operand.code]

variable {p e w : ℕ} [Fact p.Prime]

/-- Chosen coefficient vector of the returned field literal. -/
def literal (b : Bool) (p e : ℕ) [NeZero p] : Vector p e := if b then one p e else zero p e

private theorem packed_zero_value (w : ℕ) (e : ℕ) :
    TapeWord.value (packed w (List.ofFn (zero p e))) = 0 := by
  induction e with
  | zero => rfl
  | succ e ih =>
    rw [List.ofFn_succ, packed, List.flatMap_cons, value_append]
    change TapeWord.value (wordBits (Word.limb w (0 : Fin p))) +
      2 ^ _ * TapeWord.value (packed w (List.ofFn (zero p e))) = 0
    simp [ih, value_wordBits, Word.limb]

private theorem packed_literal_value (he : 0 < e) (hw : Word.workingWidth p ≤ w) (b : Bool) :
    TapeWord.value (packed w (List.ofFn (literal b p e))) = b.toNat := by
  cases b with
  | false => exact packed_zero_value _ _
  | true =>
    cases e with
    | zero => omega
    | succ e =>
      change TapeWord.value (packed w (List.ofFn (one p (e+1)))) = 1
      rw [List.ofFn_succ]
      have ht : (fun i : Fin e => one p (e + 1) i.succ) = zero p e := by funext i; simp [one, zero]
      rw [ht, packed, List.flatMap_cons, value_append]
      change TapeWord.value (wordBits (Word.limb w (1 : Fin p))) +
        2 ^ _ * TapeWord.value (packed w (List.ofFn (zero p e))) = 1
      rw [packed_zero_value, mul_zero, add_zero, value_wordBits, Word.limb_val hw]
      exact Nat.mod_eq_of_lt (Fact.out : p.Prime).one_lt

/-- Initialize or overwrite a scalar result on `.out`. The advised
polynomial on `.left` is preserved and both temporary stacks return empty. -/
theorem machine_runs (he : 0 < e) (hw : Word.workingWidth p ≤ w) (b : Bool)
    (c : Vector p e) (old : List Bool) :
    (machine b).Runs (old.length + 7 * (e*w) + 3)
      (scanStacks (packed w (List.ofFn c)) [] [] old)
      (scanStacks (packed w (List.ofFn c)) [] [] (packed w (List.ofFn (literal b p e)))) := by
  have h := scan_runs b (packed w (List.ofFn c)) old
  rw [packed_length, List.length_ofFn] at h
  have hW : 0 < e * w := Nat.mul_pos he (by unfold Word.workingWidth at hw; omega)
  have hfit : b.toNat < 2^(e*w) := (Bool.toNat_le b).trans_lt (one_lt_pow₀ (by decide) (by omega))
  have eq : wordBits (Fin.ofNat (2^(e*w)) b.toNat) = packed w (List.ofFn (literal b p e)) := by
    apply eq_of_length_value (by simp)
    rw [value_wordBits, Fin.val_ofNat, Nat.mod_eq_of_lt hfit, packed_literal_value he hw]
  rw [← eq]
  exact h

end SliceArithmeticConstant

end VPVNP
end Computability
end OAI
