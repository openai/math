import OAI.Computability.VPVNP.AffinePinExponents
import OAI.Computability.VPVNP.MacaulayExponentPack
import OAI.Computability.VPVNP.SliceGeometryProjection

/-! # Recovering the pin coefficient from its physical bit pattern -/

namespace OAI
namespace Computability
namespace VPVNP

namespace AffinePin

open RAMTape BurstRAM
open Exponents (Kind classify)
open RadicalCertificate.MonomialIndex
open UniversalCountStack (digits)

namespace Blocks

/-- Contiguous equal-width rows, in order of their `Fin` index. -/
def table {t : ℕ} (rows : Fin t → List Bool) : List Bool := (List.ofFn rows).flatten

theorem length {t : ℕ} (rows : Fin t → List Bool) (stride : ℕ)
    (h : ∀ j, (rows j).length = stride) : (table rows).length = t*stride := by
  induction t with
  | zero => simp [table]
  | succ t ih =>
    rw [table, List.ofFn_succ, List.flatten_cons, List.length_append, h, Nat.succ_mul]
    rw [← table, ih _ (fun i => h i.succ), Nat.add_comm]

theorem cell {t : ℕ} (rows : Fin t → List Bool) (w : ℕ) (h : ∀ j, (rows j).length = w)
    (i : Fin t) : ((table rows).drop (i.val*w)).take w = rows i := by
  induction t with
  | zero => exact i.elim0
  | succ t ih =>
    refine Fin.cases ?_ (fun k => ?_) i
    · simp only [table, List.ofFn_succ, List.flatten_cons, Fin.val_zero, Nat.zero_mul, List.drop_zero]
      rw [List.take_append_of_le_length (h 0).ge, List.take_of_length_le (h 0).le]
    · simp only [table, List.ofFn_succ, List.flatten_cons, Fin.val_succ, Nat.succ_mul]
      rw [show k.val*w+w=(rows 0).length+k.val*w by rw [h, Nat.add_comm], List.drop_length_add_append]
      exact ih _ (fun j => h j.succ) k

theorem exponent_table {t : ℕ} (w : ℕ) (d : Fin t → ℕ) :
    ExponentPack.packed w (List.ofFn d) = table (fun j => digits w (d j)) := by
  simp [ExponentPack.packed, table, List.flatMap_def, Function.comp_def]

theorem packed_injective {t w : ℕ} {d d' : Fin t → ℕ}
    (h : ∀ i, d i < 2^w) (h' : ∀ i, d' i < 2^w)
    (he : ExponentPack.packed w (List.ofFn d) = ExponentPack.packed w (List.ofFn d')) : d = d' := by
  rw [exponent_table, exponent_table] at he
  funext i
  have e := congrArg (fun xs : List Bool => (xs.drop (i.val*w)).take w) he
  simp only [cell _ w (fun j => UniversalCountStack.length_digits _ _) i] at e
  have hv := congrArg TapeWord.value e
  simpa only [UniversalCountStack.value_digits, Nat.mod_eq_of_lt (h i), Nat.mod_eq_of_lt (h' i)] using hv

theorem zeros (t w : ℕ) : table (fun _ : Fin t => digits w 0) = List.replicate (t*w) false := by
  induction t with
  | zero => simp [table]
  | succ t ih =>
    rw [table, List.ofFn_succ, List.flatten_cons, ← table,
      ih, UniversalCountStack.digits_zero, ← List.replicate_add, Nat.succ_mul, Nat.add_comm]

theorem one (w : ℕ) (hw : 0 < w) : digits w 1 = true :: List.replicate (w-1) false := by
  apply TapeWord.eq_of_length_value
  · simp; omega
  · rw [UniversalCountStack.value_digits, Nat.mod_eq_of_lt (one_lt_pow₀ (by decide) hw.ne')]
    simp [TapeWord.value]

theorem singleton {t : ℕ} (i : Fin t) (w : ℕ) (hw : 0 < w) :
    table (fun j => digits w (if j=i then 1 else 0)) =
      List.replicate (i.val*w) false ++ true :: List.replicate (t*w-i.val*w-1) false := by
  induction t with
  | zero => exact i.elim0
  | succ t ih =>
    refine Fin.cases ?_ (fun k => ?_) i
    · simp only [table, List.ofFn_succ, List.flatten_cons, ite_true, Fin.succ_ne_zero, ite_false,
        Fin.val_zero, Nat.zero_mul, List.replicate_zero, List.nil_append, Nat.sub_zero]
      rw [one _ hw, List.cons_append, ← table, zeros, ← List.replicate_add, Nat.succ_mul]
      congr 2; omega
    · simp only [table, List.ofFn_succ, List.flatten_cons, Ne.symm (Fin.succ_ne_zero k), ite_false,
        Fin.succ_inj, Fin.val_succ, Nat.succ_mul, UniversalCountStack.digits_zero]
      rw [← table, ih k, ← List.append_assoc, ← List.replicate_add]
      rw [Nat.add_comm w (k.val*w), Nat.add_sub_add_right]

private theorem all_zero (xs : List Bool) :
    true ∉ xs ↔ xs = List.replicate xs.length false := by
  induction xs with
  | nil => simp
  | cons b xs ih =>
    cases b <;> simp [List.replicate_succ, ih]

theorem classify_constant (pre : List Bool) (b : Bool) (post : List Bool) :
    classify pre b post = .constant ↔
      pre ++ b::post = List.replicate pre.length false ++ false :: List.replicate post.length false := by
  have eq : pre ++ b::post = List.replicate pre.length false ++ false :: List.replicate post.length false ↔
      pre = List.replicate pre.length false ∧ b = false ∧ post = List.replicate post.length false := by
    constructor
    · intro h
      obtain ⟨h₁, h₂⟩ := List.append_inj h (by simp)
      exact ⟨h₁, List.cons.inj h₂⟩
    · rintro ⟨h₁, h₂, h₃⟩
      exact congrArg₂ List.append h₁ (congrArg₂ List.cons h₂ h₃)
  rw [eq, ← all_zero, ← all_zero]
  by_cases h : true ∈ pre <;> by_cases h' : true ∈ post <;> cases b <;>
    simp [classify, Exponents.tailKind, Exponents.selected, h, h']

theorem classify_unit (pre : List Bool) (b : Bool) (post : List Bool) :
    classify pre b post = .unit ↔
      pre ++ b::post = List.replicate pre.length false ++ true :: List.replicate post.length false := by
  have eq : pre ++ b::post = List.replicate pre.length false ++ true :: List.replicate post.length false ↔
      pre = List.replicate pre.length false ∧ b = true ∧ post = List.replicate post.length false := by
    constructor
    · intro h
      obtain ⟨h₁, h₂⟩ := List.append_inj h (by simp)
      exact ⟨h₁, List.cons.inj h₂⟩
    · rintro ⟨h₁, h₂, h₃⟩
      exact congrArg₂ List.append h₁ (congrArg₂ List.cons h₂ h₃)
  rw [eq, ← all_zero, ← all_zero]
  by_cases h : true ∈ pre <;> by_cases h' : true ∈ post <;> cases b <;>
    simp [classify, Exponents.tailKind, Exponents.selected, h, h']

/-- The two flags written by the scan select exactly the zero exponent and
the selected unit exponent, including when the selected variable is first or last. -/
theorem split_packed {t : ℕ} (w : ℕ) (hw : 0 < w) (i : Fin t) (d : Fin t →₀ ℕ)
    (hd : ∀ j, d j < 2^w) :
    ∃ pre b post,
      ExponentPack.packed w (List.ofFn (fun j => d j)) = pre ++ b::post ∧
      pre.length = i.val*w ∧ post.length = t*w-i.val*w-1 ∧
      (classify pre b post = .constant ↔ d = 0) ∧
      (classify pre b post = .unit ↔ d = Finsupp.single i 1) := by
  let xs := ExponentPack.packed w (List.ofFn (fun j => d j))
  let k := i.val*w
  have len : xs.length = t*w := (congrArg List.length (exponent_table w (fun j => d j))).trans
    (length _ w (fun _ => UniversalCountStack.length_digits ..))
  have hk : k < xs.length := len ▸ (Nat.mul_lt_mul_of_pos_right i.isLt hw)
  let pre := xs.take k
  let b := xs[k]
  let post := xs.drop (k+1)
  have hsplit : xs = pre ++ b::post := by
    rw [← List.take_append_drop k xs, List.drop_eq_getElem_cons hk]
  have hpre : pre.length = k := List.length_take.trans (min_eq_left hk.le)
  have hpost : post.length = t*w-k-1 := by simp [post, len]; omega
  have hz : List.replicate pre.length false ++ false :: List.replicate post.length false =
      ExponentPack.packed w (List.ofFn fun _ : Fin t => 0) := by
    rw [exponent_table, zeros, ← List.replicate_succ, ← List.replicate_add, hpre, hpost]
    have := hk; rw [len] at this
    congr 1; omega
  have hu : List.replicate pre.length false ++ true :: List.replicate post.length false =
      ExponentPack.packed w (List.ofFn fun j => (Finsupp.single i 1 : Fin t →₀ ℕ) j) := by
    rw [exponent_table, hpre, hpost, ← singleton i w hw]
    apply congrArg table
    funext j
    simp [Finsupp.single_apply, eq_comm]
  refine ⟨pre,b,post,hsplit,hpre,hpost,?_,?_⟩
  · rw [classify_constant, ← hsplit, hz]
    constructor
    · intro h
      exact DFunLike.ext' (packed_injective hd (fun _ => Nat.two_pow_pos _) h)
    · rintro rfl; rfl
  · rw [classify_unit, ← hsplit, hu]
    constructor
    · intro h
      refine DFunLike.ext' (packed_injective hd (fun j => ?_) h)
      rw [Finsupp.single_apply]
      split
      · exact one_lt_pow₀ (by decide) hw.ne'
      · exact Nat.two_pow_pos _
    · rintro rfl; rfl

end Blocks

/-- Coefficient of a coordinate equation in the padded presentation of the slice. -/
theorem coeff_pin {K ι : Type*} [Field K] {t : ℕ} (F : ι → MvPolynomial (Fin t) K)
    (pins : Finset (Fin t)) (a : Fin t → K) (i : Fin t) (d : Fin t →₀ ℕ) :
    (SliceGeometry.pinnedEquations F pins a (.inr i)).coeff d =
      if i ∈ pins then (if d=0 then -a i else if d=Finsupp.single i 1 then 1 else 0) else 0 := by
  classical
  by_cases h : i ∈ pins
  · simp only [SliceGeometry.pinnedEquations, Sum.elim_inr, h, ite_true, MvPolynomial.coeff_sub,
      MvPolynomial.coeff_X, MvPolynomial.coeff_C]
    by_cases hd : d=0
    · subst d
      simp
    · by_cases hs : d=Finsupp.single i 1 <;> simp [hd, hs, Ne.symm hd, eq_comm]
  · simp [SliceGeometry.pinnedEquations, h]
end AffinePin

end VPVNP
end Computability
end OAI
