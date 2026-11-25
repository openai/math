import OAI.ThreeFlat.RAM.MotifAdmission
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.List.FinRange

namespace OAI
/-! # Admission of a histogram with a run-time active prefix -/

namespace ThreeFlat.RAM.AdmissionPrefix

open Computability.VPVNP.BurstRAM PrivateRAM DescriptorExpr PhysicalPinsExpr
open scoped Classical BigOperators

def active (K d : ℕ) : List (Fin K) := (List.finRange K).take d
def pad (K d : ℕ) : List (Fin K) := (List.finRange K).drop d

def Valid (K d : ℕ) (counts : Fin K → ℕ) (copies : ℕ) : Prop :=
  d ≤ K ∧ MotifAdmission.Valid (active K d) (pad K d) counts copies

theorem mem_pad {K d : ℕ} (j : Fin K) : j ∈ pad K d ↔ d ≤ j.val := by
  rw [pad,List.mem_iff_getElem]
  constructor
  · rintro ⟨i,hi,eqj⟩
    have v := congrArg Fin.val eqj
    simp only [List.getElem_drop,List.getElem_finRange,Fin.val_cast] at v
    omega
  · intro hd
    refine ⟨j.val-d,?_,?_⟩
    · simp only [List.length_drop,List.length_finRange]
      have bound := j.isLt
      omega
    · apply Fin.ext
      simp only [List.getElem_drop,List.getElem_finRange,Fin.val_cast]
      omega

theorem valid_iff_sum (K d : ℕ) (counts : Fin K → ℕ) (copies : ℕ) :
    Valid K d counts copies ↔ d ≤ K ∧ (∑ j : Fin K, counts j) = copies ∧
      ∀ j : Fin K, d ≤ j.val → counts j = 0 := by
  have total : ((active K d).map counts).sum + ((pad K d).map counts).sum =
      ∑ j : Fin K, counts j := by
    rw [←List.sum_append,←List.map_append,active,pad,List.take_append_drop,
      ←List.ofFn_eq_map,List.sum_ofFn]
  have padding (hz : ∀ j : Fin K, d ≤ j.val → counts j = 0) : ((pad K d).map counts).sum = 0 := by
    apply List.sum_eq_zero
    intro a ha
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp ha
    exact hz j ((mem_pad j).mp hj)
  constructor
  · rintro ⟨hd,hs,hp⟩
    have hz : ∀ j : Fin K, d ≤ j.val → counts j = 0 := fun j hj => hp j ((mem_pad j).mpr hj)
    exact ⟨hd,by rw [←total,padding hz,Nat.add_zero,hs],hz⟩
  · rintro ⟨hd,hs,hz⟩
    rw [padding hz,Nat.add_zero,hs] at total
    exact ⟨hd,total,fun j hj => hz j ((mem_pad j).mp hj)⟩

variable {n : ℕ}

private def scan (K : ℕ) (width base copies : Fin n) : ℕ → ℕ → Formula n
  | 0, _ => .lit 0
  | t+1, first => .select .eq (.reg width) (.lit first)
    (MotifAdmission.formula (.reg base) (.reg copies) (active K first) (pad K first))
    (scan K width base copies t (first+1))

/-- The literal tests inspect candidate widths in ascending order. A matched
width therefore always fits in the current word, even at the address-space boundary. -/
def select (K : ℕ) (width base copies : Fin n) : Formula n :=
  scan K width base copies (K+1) 0

private theorem scan_value {W : ℕ} (K : ℕ) (width base copies : Fin n)
    (data : Param → Word W) (mem : Memory W) (vs : Fin n → Word W)
    (room : (vs base).val+K ≤ 2^W) (t first : ℕ) (before : first ≤ (vs width).val) :
    (scan K width base copies t first).value data mem vs =
      if (vs width).val < first+t ∧ MotifAdmission.Valid (active K (vs width).val)
          (pad K (vs width).val) (fun i => (mem ((vs base).val+i.val)).val) (vs copies).val
        then (1 : Word W) else 0 := by
  induction t generalizing first with
  | zero =>
    have outside : ¬(vs width).val < first+0 := by omega
    simp only [scan,Formula.value,outside,false_and,ite_false]; rfl
  | succ t ih =>
    have fit : first < 2^W := before.trans_lt (vs width).isLt
    have test : vs width = Fin.ofNat (2^W) first ↔ (vs width).val = first := by
      rw [Fin.ext_iff]
      change (vs width).val = first % (2^W) ↔ _
      rw [Nat.mod_eq_of_lt fit]
    simp only [scan,Formula.value,Comparison.test,beq_iff_eq,test]
    by_cases hit : (vs width).val=first
    · have inside : (vs width).val < first+(t+1) := by omega
      rw [ite_eq_left hit]
      simp only [inside,true_and]
      rw [hit]
      exact MotifAdmission.word_value data mem vs base copies (active K first) (pad K first) room
    · have next : first+1 ≤ (vs width).val := by omega
      rw [ite_eq_right hit,ih (first+1) next,show first+1+t=first+(t+1) by omega]

theorem word_value {W : ℕ} (K : ℕ) (width base copies : Fin n)
    (data : Param → Word W) (mem : Memory W) (vs : Fin n → Word W)
    (room : (vs base).val+K ≤ 2^W) :
    (select K width base copies).value data mem vs =
      if Valid K (vs width).val (fun i => (mem ((vs base).val+i.val)).val) (vs copies).val
      then (1 : Word W) else 0 := by
  rw [select,scan_value K width base copies data mem vs room (K+1) 0 (Nat.zero_le _)]
  simp only [Nat.zero_add,Nat.lt_succ_iff]
  by_cases h : Valid K (vs width).val (fun i => (mem ((vs base).val+i.val)).val) (vs copies).val
  · simp only [ite_eq_left h,ite_eq_left (show _ ∧ _ from h)]
  · simp only [ite_eq_right h,ite_eq_right (show ¬(_ ∧ _) from h)]

theorem compile_eval {W k : ℕ} (K : ℕ) (width base copies : Fin n) (p : Param → Fin k)
    (data : Fin k → Word W) (mem : Memory W) (vs : Fin n → Word W)
    (room : (vs base).val+K ≤ 2^W) :
    ((select K width base copies).compile p).eval data mem vs =
      if Valid K (vs width).val (fun i => (mem ((vs base).val+i.val)).val) (vs copies).val
      then (1 : Word W) else 0 := by
  rw [Formula.eval_compile]
  exact word_value K width base copies _ mem vs room

end ThreeFlat.RAM.AdmissionPrefix

end OAI
