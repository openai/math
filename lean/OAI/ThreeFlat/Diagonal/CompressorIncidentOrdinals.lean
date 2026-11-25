import OAI.ThreeFlat.Diagonal.CompressorIncidentKeys
import Mathlib.Data.ZMod.Defs

namespace OAI
/-! # The count and six native fields of the first occurrence of each nonzero incident key -/

namespace ThreeFlat.Diagonal.CompressorPacking.Native.ShrinkStage.Incidents

open Computability.VPVNP.BurstRAM Computability.VPVNP.BurstRAM.PrivateRAM RAM.PhysicalPinsExpr
open scoped Fin.CommRing

variable {w : ℕ} (data : Param → Word w) (m : Memory w) (vs : Fin 1 → Word w)
local notation "V" => Formula.value data m vs

private theorem eval_eq (a b x y : F) :
    V (.select .eq a b x y) = if V a = V b then V x else V y := by
  simp only [Formula.value,RAM.DescriptorExpr.Comparison.test,beq_iff_eq]

private theorem eval_lit (i : ℕ) : V (.lit i : F) = (i : Word w) := rfl

private theorem member_eval (a : F) (seen : List F) :
    V (Template.member a seen) = if V a ∈ seen.map V then 1 else 0 := by
  induction seen with
  | nil => simp [Template.member,Formula.value]
  | cons x xs ih =>
    change V (.select .eq a x (.lit 1) (Template.member a xs)) = _
    rw [eval_eq,eval_lit,ih]
    by_cases h : V a = V x <;> simp [h]

private def mark (k : F) (seen : List F) : F :=
  .select .eq k (.lit 0) (.lit 0)
    (.select .eq (Template.member k seen) (.lit 1) (.lit 0) (.lit 1))

private theorem one_nonzero (room : 1 < 2^w) : (1 : Word w) ≠ 0 := by
  intro eq
  have h := congrArg Fin.val eq
  change (1 : Word w).val = 0 at h
  rw [show (1 : Word w).val = 1 from Fin.val_cast_of_lt room] at h
  omega

private theorem mark_value (one : (1 : Word w) ≠ 0) (k : F) (seen : List F) :
    V (mark k seen) = if V k ≠ 0 ∧ V k ∉ seen.map V then 1 else 0 := by
  simp only [mark,eval_eq,eval_lit,Nat.cast_zero,Nat.cast_one,member_eval]
  by_cases a : V k=0 <;> by_cases b : V k ∈ seen.map V <;> simp [a,b,Ne.symm one]

private theorem occupied_cons (a : FirstHit) (xs : List FirstHit) :
    V (occupied (a::xs)) = V a.valid + V (occupied xs) := rfl

private theorem occupied_from (one : (1 : Word w) ≠ 0) (seen : List F) (xs : List Hit) :
    V (occupied (firsts seen xs)) = ((selected V (seen.map V) xs).length : Word w) := by
  induction xs generalizing seen with
  | nil => rfl
  | cons a xs ih =>
    change V (occupied (⟨mark a.key seen,a.fields⟩ :: firsts (a.key::seen) xs)) = _
    rw [occupied_cons,mark_value data m vs one,ih]
    by_cases keep : V a.key ≠ 0 ∧ V a.key ∉ seen.map V
    · simp [selected,keep,List.length_cons,Nat.cast_add,add_comm]
    · simp only [selected,ite_eq_right keep,List.map_cons,zero_add]

theorem occupied_firsts (room : 1 < 2^w) (xs : List Hit) :
    V (occupied (firsts [] xs)) = ((selected V [] xs).length : Word w) :=
  occupied_from data m vs (one_nonzero room) [] xs

/-- Fields beyond the dense first-occurrence prefix are zero. -/
def fieldValue (value : F → Word w) (xs : List Hit) (i : ℕ) (f : Fin 6) : Word w :=
  (xs[i]?.map (fun a => value (a.fields f))).getD 0

private theorem ordinal_cons (one : (1 : Word w) ≠ 0) (f : Fin 6) (n index : F)
    (a : FirstHit) (xs : List FirstHit) :
    V (ordinalField f n (a::xs) index) =
      if V a.valid = 1 ∧ V n = V index then V (a.fields f)
      else V (ordinalField f n xs (.op .add index a.valid)) := by
  simp only [ordinalField,eval_eq,eval_lit,Nat.cast_one,Nat.cast_zero]
  by_cases h : V a.valid=1 <;> by_cases e : V n=V index <;> simp [h,e,Ne.symm one]

private theorem ordinal_from (one : (1 : Word w) ≠ 0) (f : Fin 6) (n : F) (xs : List Hit)
    (seen : List F) (index : F) (lo : (V index).val ≤ (V n).val)
    (fit : (V index).val+xs.length < 2^w) :
    V (ordinalField f n (firsts seen xs) index) =
      fieldValue V (selected V (seen.map V) xs) ((V n).val-(V index).val) f := by
  induction xs generalizing seen index with
  | nil => simp [firsts,ordinalField,selected,fieldValue,Formula.value]
  | cons a xs ih =>
    simp only [List.length_cons] at fit
    let flag := mark a.key seen
    let next : F := .op .add index flag
    have stepV : V next = V index + V flag := rfl
    change V (ordinalField f n (⟨flag,a.fields⟩::firsts (a.key::seen) xs) index) = _
    rw [ordinal_cons data m vs one]
    change (if V flag = 1 ∧ V n = V index then V (a.fields f)
      else V (ordinalField f n (firsts (a.key::seen) xs) next)) = _
    have flagV := mark_value data m vs one a.key seen
    change V flag = _ at flagV
    by_cases keep : V a.key ≠ 0 ∧ V a.key ∉ seen.map V
    · rw [ite_eq_left keep] at flagV
      have advance : (V next).val = (V index).val+1 := by
        rw [stepV,flagV]
        exact Fin.val_add_one_of_lt' (by omega)
      by_cases here : V n=V index
      · simp [flagV,here,selected,keep,fieldValue]
      · have ne : (V n).val ≠ (V index).val := fun eq => here (Fin.ext eq)
        have t := ih (a.key::seen) next (by omega) (by omega)
        have sub : (V n).val-(V index).val = ((V n).val-(V next).val)+1 := by omega
        rw [ite_eq_right (by simp [here]),t,sub]
        simp [selected,keep,fieldValue]
    · rw [ite_eq_right keep] at flagV
      have same : V next = V index := by rw [stepV,flagV,add_zero]
      have t := ih (a.key::seen) next (by simpa only [same] using lo) (by rw [same]; omega)
      rw [ite_eq_right (by simp [flagV,Ne.symm one]),t,same]
      simp only [selected,ite_eq_right keep,List.map_cons]

private theorem eval_field_fold (row : Fin 6 → F) (f : F) (field : Fin 6) (room : 6 ≤ 2^w)
    (wanted : (V f).val = field.val) (js : List (Fin 6)) (present : field ∈ js) :
    V (js.foldr (fun j z => .select .eq f (.lit j.val) (row j) z) (.lit 0)) = V (row field) := by
  induction js with
  | nil => simp at present
  | cons j js ih =>
    have eq : V f = (j.val : Word w) ↔ field=j := by
      rw [Fin.ext_iff,Fin.val_cast_of_lt (j.isLt.trans_le room),wanted,Fin.ext_iff]
    change V (.select .eq f (.lit j.val) (row j) _) = _
    rw [eval_eq,eval_lit]
    by_cases h : field=j
    · rw [ite_eq_left (eq.mpr h),h]
    · rw [ite_eq_right (eq.not.mpr h)]
      exact ih ((List.mem_cons.mp present).resolve_left h)

theorem fieldAt_firsts (room : 6 ≤ 2^w) (xs : List Hit) (fit : xs.length < 2^w)
    (k f : F) (field : Fin 6) (wanted : (V f).val = field.val) :
    V (fieldAt (firsts [] xs) k f) = fieldValue V (selected V [] xs) (V k).val field := by
  unfold fieldAt
  rw [eval_field_fold data m vs _ f field room wanted _ (List.mem_finRange field)]
  have h := ordinal_from data m vs (one_nonzero (by omega)) field k xs [] (.lit 0)
    (show (V (.lit 0 : F)).val ≤ _ from Nat.zero_le _) (by simpa [Formula.value] using fit)
  simpa [Formula.value] using h

theorem fieldAt_firsts_of_lt (room : 6 ≤ 2^w) (xs : List Hit) (fit : xs.length < 2^w)
    (k f : F) (field : Fin 6) (wanted : (V f).val=field.val)
    (within : (V k).val < (selected V [] xs).length) :
    V (fieldAt (firsts [] xs) k f) = V (((selected V [] xs)[(V k).val]).fields field) := by
  rw [fieldAt_firsts data m vs room xs fit k f field wanted]
  simp [fieldValue,List.getElem?_eq_getElem within]

theorem fieldAt_firsts_of_le (room : 6 ≤ 2^w) (xs : List Hit) (fit : xs.length < 2^w)
    (k f : F) (field : Fin 6) (wanted : (V f).val=field.val)
    (past : (selected V [] xs).length ≤ (V k).val) :
    V (fieldAt (firsts [] xs) k f) = 0 := by
  rw [fieldAt_firsts data m vs room xs fit k f field wanted]
  simp [fieldValue,List.getElem?_eq_none past]

end ThreeFlat.Diagonal.CompressorPacking.Native.ShrinkStage.Incidents

end OAI
