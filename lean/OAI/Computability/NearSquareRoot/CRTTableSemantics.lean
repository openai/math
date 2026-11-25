import OAI.Computability.NearSquareRoot.CRTTableElimination
import OAI.Computability.IntegerMultiplication.Code.Padding
import Mathlib.Data.ZMod.Basic

/-! # Correctness of CRT table elimination

The residual of a control row is its decoded digit plus contributions from the
still-pending columns. The first residual is the pivot. Eliminating the column
subtracts the same pivot times each row's own coefficient, modulo that row's
modulus. Target rows initialized at zero then contain the negative offsets.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace CRTTable
open IntegerMultiplication.Code

/-- Dot product of an initial segment of recovered digits with a row of
mixed-radix coefficients. Missing coefficients are zero. -/
def rowDot : List Tally → List Tally → ℕ
  | [], _ => 0
  | x :: xs, cs => x.length * (cs.headD []).length + rowDot xs cs.tail

theorem rowDot_map {J : Type*} (u c : J → Tally) (js : List J) :
    rowDot (js.map u) (js.map c) = (js.map (fun j => (u j).length * (c j).length)).sum := by
  induction js with
  | nil => rfl
  | cons j js ih => simpa only [List.map_cons, rowDot, List.headD_cons, List.tail_cons,
      List.sum_cons, Nat.add_left_cancel_iff] using ih

theorem rowDot_append_right (xs cs suffix : List Tally) (h : xs.length ≤ cs.length) :
    rowDot xs (cs ++ suffix) = rowDot xs cs := by
  induction xs generalizing cs with
  | nil => rfl
  | cons x xs ih =>
    cases cs with
    | nil => simp at h
    | cons c cs =>
      simp only [List.cons_append, rowDot, List.headD_cons, List.tail_cons,
        Nat.add_left_cancel_iff]
      exact ih cs (Nat.le_of_succ_le_succ h)

/-- The unit diagonal of the triangular system is implicit. The stored
coefficients give the contribution from digits preceding the row. -/
def Encodes (prior : List Tally) : List Row → List Tally → Prop
  | [], [] => True
  | r :: rs, x :: xs =>
      r.2.1.length < r.1.length ∧ x.length < r.1.length ∧
      r.2.1.length ≡ x.length + rowDot prior r.2.2 [MOD r.1.length] ∧
      Encodes (prior ++ [x]) rs xs
  | _, _ => False

/-- Construct the triangular-system invariant from the individual row formulas,
using exactly the earlier digits in their original order. -/
theorem encodes_of_get (prior : List Tally) (rows : List Row) (digits : List Tally)
    (hlen : rows.length = digits.length)
    (h : ∀ (j : ℕ) (hr : j < rows.length) (hx : j < digits.length),
      let r := rows[j]
      let x := digits[j]
      r.2.1.length < r.1.length ∧ x.length < r.1.length ∧
      r.2.1.length ≡ x.length + rowDot (prior ++ digits.take j) r.2.2 [MOD r.1.length]) :
    Encodes prior rows digits := by
  induction rows generalizing prior digits with
  | nil =>
    cases digits with
    | nil => trivial
    | cons => simp at hlen
  | cons r rs ih =>
    cases digits with
    | nil => simp at hlen
    | cons x xs =>
      obtain ⟨hv, hx, he⟩ := h 0 (by simp) (by simp)
      refine ⟨hv, hx, ?_, ih (prior ++ [x]) xs (by simpa using hlen) ?_⟩
      · simpa using he
      · intro j hj h'
        have hh := h j.succ (Nat.succ_lt_succ hj) (Nat.succ_lt_succ h')
        dsimp only at hh ⊢
        simpa only [List.getElem_cons_succ, List.take_succ_cons, List.append_assoc,
          List.cons_append, List.nil_append] using hh

private theorem advance_cancel (u : Tally) (r : Row) (hm : 0 < r.1.length) :
    (advanceRow (u,r)).2.1.length + u.length * (r.2.2.headD []).length ≡
      r.2.1.length [MOD r.1.length] := by
  let a := r.1.length
  let v := r.2.1.length
  let t := u.length * (r.2.2.headD []).length
  change (residualStep (_,_,_,_)).length + t ≡ v [MOD a]
  simp only [residualStep, tally_length, Nat.mul_comm (r.2.2.headD []).length]
  change (v % a + a - t % a) % a + t ≡ v [MOD a]
  have hlt : t % a < a := Nat.mod_lt t hm
  calc
    _ ≡ (v % a + a - t % a) + t % a [MOD a] :=
      (Nat.mod_modEq _ _).add (Nat.mod_modEq _ _).symm
    _ = v % a + a := Nat.sub_add_cancel (by omega)
    _ ≡ v [MOD a] := by simp [Nat.ModEq]

private theorem consume_column (u : Tally) (prior : List Tally) {rs : List Row} {xs : List Tally}
    (h : Encodes (u :: prior) rs xs) :
    Encodes prior (rs.map (fun r => advanceRow (u,r))) xs := by
  induction rs generalizing prior xs with
  | nil => cases xs <;> exact h
  | cons r rs ih =>
    cases xs with
    | nil => exact False.elim h
    | cons x xs =>
      obtain ⟨hv, hx, he, htail⟩ := h
      have hm : 0 < r.1.length := by omega
      have hsub := (advance_cancel u r hm).trans he
      refine ⟨?_, hx, ?_, ih (prior ++ [x]) htail⟩
      · change (residualStep (_,_,_,_)).length < _
        simp only [residualStep, tally_length]
        exact Nat.mod_lt _ hm
      · apply Nat.ModEq.add_right_cancel' (u.length * (r.2.2.headD []).length)
        simpa only [rowDot, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc, advanceRow] using hsub

/-- Subtract one entire recovered prefix from a target row, in column order. -/
def reduceRow (xs : List Tally) (r : Row) : Row :=
  xs.foldl (fun s x => advanceRow (x,s)) r

/-- After all the controls have been consumed, only the updated target rows remain. -/
theorem residuals_encoded {controls targets : List Row} {xs : List Tally} (t : Tally)
    (ht : t.length = xs.length) (h : Encodes [] controls xs) :
    residuals (t, controls ++ targets) = targets.map (reduceRow xs) := by
  rw [residuals, ride_t, ht]
  clear ht t
  induction xs generalizing controls targets with
  | nil =>
    cases controls with
    | nil => simp [show reduceRow [] = id from rfl]
    | cons => exact False.elim h
  | cons x xs ih =>
    cases controls with
    | nil => exact False.elim h
    | cons r rs =>
      obtain ⟨hv, hx, he, htail⟩ := h
      have hp : r.2.1.length = x.length :=
        (show r.2.1.length ≡ x.length [MOD r.1.length] by simpa [rowDot] using he).eq_of_lt_of_lt hv hx
      have hx' : r.2.1 = x := (recover_tally r.2.1).symm.trans (hp ▸ recover_tally x)
      have hs := consume_column x [] htail
      rw [List.length_cons, Function.iterate_succ_apply]
      simp only [List.cons_append, eliminate, List.tail_cons, List.headD_cons, hx', List.map_append]
      rw [ih hs]
      simp only [List.map_map]
      rfl

@[simp] theorem reduceRow_modulus (xs : List Tally) (r : Row) : (reduceRow xs r).1 = r.1 := by
  induction xs generalizing r with
  | nil => rfl
  | cons u xs ih => exact ih (advanceRow (u,r))

theorem reduceRow_value_lt (xs : List Tally) (r : Row) (hv : r.2.1.length < r.1.length) :
    (reduceRow xs r).2.1.length < r.1.length := by
  induction xs generalizing r with
  | nil => exact hv
  | cons u xs ih =>
    apply ih (advanceRow (u,r))
    change (residualStep (_,_,_,_)).length < r.1.length
    simp only [residualStep, tally_length]
    exact Nat.mod_lt _ (by omega)

/-- Congruence for an arbitrary target row, including a nonzero initial value. -/
theorem reduceRow_cancel (xs : List Tally) (r : Row) (hm : 0 < r.1.length) :
    (reduceRow xs r).2.1.length + rowDot xs r.2.2 ≡ r.2.1.length [MOD r.1.length] := by
  induction xs generalizing r with
  | nil => exact (Nat.add_zero _).symm ▸ Nat.ModEq.refl _
  | cons u xs ih =>
    have h := (ih (advanceRow (u,r)) hm).add_right (u.length * (r.2.2.headD []).length)
    change (reduceRow xs (advanceRow (u,r))).2.1.length + rowDot (u :: xs) r.2.2 ≡ r.2.1.length [MOD r.1.length]
    rw [rowDot, Nat.add_comm (u.length * _), ← Nat.add_assoc]
    exact h.trans (advance_cancel u r hm)

/-- A target accumulator initialized at zero computes the additive inverse of
the rotation required by the CRT merge. -/
theorem reduceRow_negative (xs : List Tally) (a : Tally) (cs : List Tally) (ha : 0 < a.length) :
    (((reduceRow xs (a,[],cs)).2.1.length : ℕ) : ZMod a.length) =
      -((rowDot xs cs : ℕ) : ZMod a.length) := by
  have h := (ZMod.natCast_eq_natCast_iff _ _ _).mpr (reduceRow_cancel xs (a,[],cs) ha)
  exact eq_neg_of_add_eq_zero_left (by simpa only [Nat.cast_add, List.length_nil, Nat.cast_zero] using h)

end CRTTable

end NearSquareRoot
end Computability
end OAI
