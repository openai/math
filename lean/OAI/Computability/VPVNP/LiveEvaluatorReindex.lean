import OAI.Computability.VPVNP.EvaluatorProgramRawInput
import OAI.Computability.VPVNP.LiveEvaluatorInitializeSweep

/-!
# Exponent coordinates on the physical evaluator input

The middle cut sends dense production rows followed by dense gadget rows.
The advised permutation identifies the corresponding formal coordinate of
the evaluator. Each low-endian row bit appears once in the raw input,
as the payload of a reversed tagged field. All remaining bytes of the
initial tape are identical to the raw input with zero exponent rows.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace LiveEvaluatorReindex

open Evaluator.InputBank EvaluatorProgramRawInput RAMSerialization
open BurstRAM (Word)
variable {d t Z : ℕ}

/-- Lift the coordinate permutation, keeping every row's bit index fixed. -/
def bitOrder (perm : Fin d ≃ Fin t) (Z : ℕ) : Fin (d * Z) ≃ Fin (t * Z) :=
  finProdFinEquiv.symm.trans ((perm.prodCongr (Equiv.refl _)).trans finProdFinEquiv)

@[simp] theorem bitOrder_at (perm : Fin d ≃ Fin t) (i : Fin d) (j : Fin Z) :
    bitOrder perm Z (finProdFinEquiv (i, j)) = finProdFinEquiv (perm i, j) := by
  simp [bitOrder]

theorem bitOrder_read (perm : Fin d ≃ Fin t) (dense : Fin d → Word Z) (formal : Fin t → Word Z)
    (h : ∀ i, formal (perm i) = dense i) (q : Fin (d * Z)) :
    arrayBits t Z formal (bitOrder perm Z q) = arrayBits d Z dense q := by
  obtain ⟨⟨i, j⟩, rfl⟩ := finProdFinEquiv.surjective q
  simp [arrayBits_at, h]

/-- Address inside the tagged exponent field of the bit whose formal index
in the forward, low-endian array is `q`. -/
def payload {T : ℕ} (q : Fin T) : ℕ := 2 * (T - 1 - q.val) + 1

theorem payload_injective {T : ℕ} : Function.Injective (payload (T := T)) := by
  intro i j he
  apply Fin.ext
  unfold payload at he
  omega

private theorem field_at {T : ℕ} (f : Fin T → Bool) (q : Fin T) :
    (fieldBits (List.ofFn f))[payload q]? = some (f q) := by
  let i : Fin (List.ofFn f).length := ⟨T-1-q.val, by rw [List.length_ofFn]; omega⟩
  have he := fieldBits_payload (List.ofFn f) i
  simp only [List.getElem_reverse, List.length_ofFn, List.getElem_ofFn] at he
  have hi : T-1-i.val = q.val := by dsimp [i]; omega
  rw [List.getElem?_eq_getElem (by rw [length_fieldBits, List.length_ofFn]; unfold payload; omega)]
  apply congrArg some
  change (fieldBits (List.ofFn f))[2*i.val+1]'_ = f q
  exact he.trans (congrArg f (Fin.ext hi))

private theorem field_else {T : ℕ} (f g : Fin T → Bool) (j : ℕ)
    (hj : ∀ q : Fin T, j ≠ payload q) : (fieldBits (List.ofFn f))[j]? = (fieldBits (List.ofFn g))[j]? := by
  by_cases h : j < 2*T+1
  · have hget (b : Fin T → Bool) : j < (fieldBits (List.ofFn b)).length := by simpa [length_fieldBits] using h
    rw [List.getElem?_eq_getElem (hget f), List.getElem?_eq_getElem (hget g)]
    by_cases hend : j = 2*T
    · subst j
      have he (b : Fin T → Bool) := fieldBits_end (List.ofFn b)
      simp only [List.length_ofFn] at he
      rw [he, he]
    · have heven : j = 2*(j/2) := by
        by_contra hn
        let q : Fin T := ⟨T-1-(j/2), by omega⟩
        exact hj q (by dsimp [payload, q]; omega)
      have tag (b : Fin T → Bool) := fieldBits_tag (List.ofFn b)
        ⟨j/2, by rw [List.length_ofFn]; omega⟩
      rw [show (fieldBits (List.ofFn f))[j]'(hget f) = true from by simpa only [← heven] using tag f,
        show (fieldBits (List.ofFn g))[j]'(hget g) = true from by simpa only [← heven] using tag g]
  · simp [List.getElem?_eq_none (by simpa [length_fieldBits] using Nat.le_of_not_gt h :
        (fieldBits (List.ofFn f)).length ≤ j),
      List.getElem?_eq_none (by simpa [length_fieldBits] using Nat.le_of_not_gt h :
        (fieldBits (List.ofFn g)).length ≤ j)]

/-- Offset in the raw evaluator input, after the advised prefix and the
initial unary width field. -/
def rawSlot (adviceLength Z : ℕ) {T : ℕ} (q : Fin T) : ℕ :=
  adviceLength + (2 * Z + 1) + payload q

private def start (A : List Bool) (Z : ℕ) : List Bool := A ++ fieldBits (List.replicate Z true)

private def ending (Z : ℕ) : List Bool :=
  fieldBits (List.replicate Z true) ++ fieldBits (List.replicate Z true)

private theorem raw_parts (A : List Bool) (e : Fin t → Word Z) :
    A ++ runtime e = start A Z ++ (fieldBits (List.ofFn (arrayBits t Z e)) ++ ending Z) := by
  simp [start, ending, runtime, List.append_assoc]

@[simp] private theorem start_length (A : List Bool) : (start A Z).length = A.length + (2*Z+1) := by
  simp [start, length_fieldBits]

theorem raw_at (A : List Bool) (e : Fin t → Word Z) (q : Fin (t*Z)) :
    (A ++ runtime e)[rawSlot A.length Z q]? = some (arrayBits t Z e q) := by
  rw [raw_parts]
  rw [List.getElem?_append_right (by simp [rawSlot])]
  simp only [start_length, rawSlot, Nat.add_sub_cancel_left]
  rw [List.getElem?_append_left (by rw [length_fieldBits, List.length_ofFn]; unfold payload; omega),
    field_at]

theorem raw_else (A : List Bool) (e f : Fin t → Word Z) (j : ℕ)
    (hj : ∀ q : Fin (t*Z), j ≠ rawSlot A.length Z q) :
    (A ++ runtime e)[j]? = (A ++ runtime f)[j]? := by
  rw [raw_parts, raw_parts]
  by_cases h : j < (start A Z).length
  · rw [List.getElem?_append_left h, List.getElem?_append_left h]
  rw [List.getElem?_append_right (Nat.le_of_not_gt h), List.getElem?_append_right (Nat.le_of_not_gt h)]
  let k := j - (start A Z).length
  have hlen (x : Fin t → Word Z) : (fieldBits (List.ofFn (arrayBits t Z x))).length = 2*(t*Z)+1 := by
    rw [length_fieldBits, List.length_ofFn]
  by_cases hk : k < 2*(t*Z)+1
  · rw [List.getElem?_append_left (by rwa [hlen]), List.getElem?_append_left (by rwa [hlen])]
    apply field_else
    intro q he
    apply hj q
    rw [rawSlot, ← start_length, ← he]
    omega
  · rw [List.getElem?_append_right (by rw [hlen]; exact Nat.le_of_not_gt hk),
      List.getElem?_append_right (by rw [hlen]; exact Nat.le_of_not_gt hk), hlen, hlen]

/-- The word read from dense row `q / Z` supplies exactly the payload
of the formal-coordinate evaluator field. -/
theorem raw_dense_at (A : List Bool) (perm : Fin d ≃ Fin t) (dense : Fin d → Word Z)
    (formal : Fin t → Word Z) (h : ∀ i, formal (perm i) = dense i) (q : Fin (d*Z)) :
    (A ++ runtime formal)[rawSlot A.length Z (bitOrder perm Z q)]? = some (arrayBits d Z dense q) := by
  rw [raw_at, bitOrder_read perm dense formal h]

end LiveEvaluatorReindex

end VPVNP
end Computability
end OAI
