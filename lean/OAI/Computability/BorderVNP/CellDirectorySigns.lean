import OAI.Computability.BorderVNP.CellSparseSemantics
import Mathlib.Data.List.GetD

/-! # Signs of true private factor observations -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace CellSparse

open scoped Classical

/-- Such a factor emits a positive observation on every passing row. -/
def Factor.SignFree : Factor → Prop
  | .sign .. => False
  | _ => True

/-- All tables physically stored in this packet have positive observations. -/
def Directory.SignFree (D : Directory) : Prop := ∀ fs ∈ D.boxes, ∀ f ∈ fs, f.SignFree

theorem Factor.observe_sign {f : Factor} (h : f.SignFree) (bank : ℕ → Bool) (off copy : ℕ)
    {o : Bool × Option ℕ} (ho : f.observe bank off copy = some o) : o.1 = false := by
  cases f with
  | sign => cases h
  | truth ws rs | unary ws rs =>
    simp only [observe] at ho
    split at ho
    · cases ho; rfl
    · cases ho
  | gadget ws rs =>
    simp only [observe] at ho
    cases he : rs[word bank (ws.map (off+·))]? <;> simp only [he,Option.map_none,Option.map_some] at ho
    all_goals cases ho <;> rfl

private theorem occurrence_factor {D : Directory} (h : D.SignFree) {o : Occurrence} (hm : o ∈ D.occurrences) :
    o.factor.SignFree := by
  obtain ⟨r,_,hr⟩ := List.mem_flatMap.mp hm
  cases r with
  | box id base copies stride =>
    change o ∈ (List.range copies).flatMap (fun i => (D.boxes.getD id []).map
      (fun f => (⟨f,base+i*stride,i⟩ : Occurrence))) at hr
    obtain ⟨_,_,hmapped⟩ := List.mem_flatMap.mp hr
    obtain ⟨f,hf,eqo⟩ := List.mem_map.mp hmapped
    subst o
    by_cases hi : id < D.boxes.length
    · rw [List.getD_eq_getElem D.boxes [] hi] at hf
      exact h _ (List.getElem_mem hi) _ hf
    · rw [List.getD_eq_default D.boxes [] (Nat.le_of_not_gt hi)] at hf
      cases hf
  | _ => cases hr

private theorem all_signs (xs : List Occurrence) (h : ∀ a ∈ xs, a.factor.SignFree) (bank : ℕ → Bool)
    {os : List (Bool × Option ℕ)}
    (hm : xs.mapM (fun a => a.factor.observe bank a.offset a.copy) = some os) :
    ∀ o ∈ os, o.1 = false := by
  induction xs generalizing os with
  | nil => simp at hm; subst os; simp
  | cons a xs ih =>
    cases ha : a.factor.observe bank a.offset a.copy with
    | none => simp [List.mapM_cons,ha] at hm
    | some b =>
      cases hs : xs.mapM (fun a => a.factor.observe bank a.offset a.copy) with
      | none => simp [List.mapM_cons,ha,hs] at hm
      | some bs =>
        simp [List.mapM_cons,ha,hs] at hm
        subst os
        intro o ho
        rcases List.mem_cons.mp ho with rfl | ht
        · exact Factor.observe_sign (h _ List.mem_cons_self) bank a.offset a.copy ha
        · exact ih (fun x hx => h _ (.tail _ hx)) hs o ht

theorem Directory.SignFree.signs {D : Directory} (h : D.SignFree) (bank : ℕ → Bool)
    {os : List (Bool × Option ℕ)} (hs : D.observations bank = some os) : ∀ o ∈ os, o.1=false :=
  all_signs D.occurrences (fun _ ha => occurrence_factor h ha) bank hs

private theorem xor_false (xs : List (Bool × Option ℕ)) (h : ∀ x ∈ xs, x.1 = false) :
    (xs.map Prod.fst).foldl Bool.xor false = false := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    rw [List.map_cons,List.foldl_cons,h a List.mem_cons_self]
    exact ih fun x hx => h x (.tail _ hx)

/-- The local signed sum contributes exactly one on each passing assignment;
this includes every selected zero-valued field coefficient. -/
theorem Directory.SignFree.weight_eq {D : Directory} (h : D.SignFree) (bank : ℕ → Bool) :
    D.weight bank = if ∃ os, D.observations bank = some os ∧ (∀ r ∈ D.records, r.Valid D.boxes bank) ∧
      countsValid bank D.reportedCounts os then 1 else 0 := by
  classical
  unfold Directory.weight
  cases hs : D.observations bank with
  | none => simp
  | some os => simp only [Option.some.injEq,exists_eq_left',xor_false os (h.signs bank hs),Bool.false_eq_true,ite_false]

end CellSparse

end BorderVNP
end Computability
end OAI
