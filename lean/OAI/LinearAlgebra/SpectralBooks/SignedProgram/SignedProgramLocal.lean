import OAI.LinearAlgebra.SpectralBooks.SignedProgram.SignedProgramCertificate
import Mathlib.Data.List.FinRange

/-! # Local checks for padded transition tables -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

namespace SignedProgram

open SignedMachine
open private blankMove blankRow from OAI.LinearAlgebra.SpectralBooks.SignedProgramPadding

@[simp] private theorem bounded_fin {n : ℕ} (x : Fin (n+1)) : bounded n x.val = x := by
  apply Fin.ext
  exact Nat.min_eq_right (Nat.le_of_lt_succ x.isLt)

private theorem activeList_at {n : ℕ} {α : Type*} (f : Fin n → α) (k : Fin (n+1)) (i : Fin n) :
    (activeList k f)[i.val]? = if i.val < k.val then some (f i) else none := by
  simp only [activeList,List.getElem?_ofFn]
  split <;> rfl

private def pad {α : Type*} {n : ℕ} (k : Fin (n+1)) (x : Fin n → α) (d : α) :
    Fin n → α := fun i ↦ if i.val < k.val then x i else d

private def Move.normal {n : ℕ} (m : Move n) (k : Fin (n+1)) : Move n :=
  {m with work := pad k m.work (.blank,.left)}

private theorem fromTransition_normal {n : ℕ} (m : Move n) (k : Fin (n+1)) :
    fromTransition n (m.transition k) = m.normal k := by
  cases m with
  | mk s a w =>
    simp only [fromTransition,Move.normal,Move.transition,bounded_fin]
    congr 1
    funext i
    simp only [List.getD_eq_getElem?_getD, activeList_at,pad]
    split <;> rfl

private def Row.normal {n : ℕ} (r : Row n) (k : Fin (n+1)) : Row n :=
  {r with
   reads := pad k r.reads .blank
   out := if r.kind = 0 then r.out else .zero
   next := fun b ↦
      if r.kind = 0 ∨ (r.kind = 1 ∧ b = true) then blankMove n else (r.next b).normal k}

private theorem fromRule_normal {n : ℕ} (r : Row n) (k : Fin (n+1)) :
    fromRule n (r.rule k) = r.normal k := by
  have hread : (fun i : Fin n ↦ (activeList k r.reads).getD i.val .blank) = pad k r.reads .blank := by
    funext i
    simp only [List.getD_eq_getElem?_getD,activeList_at,pad]
    split <;> rfl
  cases r with
  | mk s inp rd kind o tr =>
    dsimp only at hread
    fin_cases kind <;>
      simp only [Row.rule, Row.action, fromRule, Row.normal, bounded_fin, hread]
    all_goals
      simp [blankRow, -List.getD_eq_getElem?_getD]
    all_goals
      funext b
      cases b <;> simp [fromTransition_normal]

/-- Each row either is the all-default padding row or has default values only
in its unused fields, according to its action tag and the tape count. -/
def Table.LocalPadding {n : ℕ} (t : Table n) : Prop :=
  ∀ i, t.row i = if i.val < t.rows.val then (t.row i).normal t.tapes else blankRow n

theorem localPadding_iff {n : ℕ} (t : Table n) : t.LocalPadding ↔ t.Canonical := by
  have hrow (i : Fin n) : (fromProgram n t.program).row i =
      if i.val < t.rows.val then (t.row i).normal t.tapes else blankRow n := by
    rw [fromProgram, Table.program]
    simp only [activeList_at]
    split <;> simp [fromRule_normal]
  constructor
  · intro hl
    have he : t.row = (fromProgram n t.program).row := funext fun i ↦ (hl i).trans (hrow i).symm
    cases t with
    | mk k m rs =>
      change Table.mk k m rs = Table.mk _ _ _
      congr 1
      · exact (bounded_fin _).symm
      · simp [Table.program,activeList]
  · intro hc i
    exact (congrArg (fun u : Table n ↦ u.row i) hc).trans (hrow i)

/-- Pairwise inequality of the active keys; padding tapes play no part. -/
def Table.Distinct {n : ℕ} (t : Table n) : Prop :=
  ∀ i j : Fin n, i.val < t.rows.val → j.val < t.rows.val →
    (t.row i).state = (t.row j).state → (t.row i).input = (t.row j).input →
    (∀ k : Fin n, k.val < t.tapes.val → (t.row i).reads k = (t.row j).reads k) → i = j

private theorem read_eq {α : Type*} {n : ℕ} (k : Fin (n+1)) (f g : Fin n → α) :
    activeList k f = activeList k g ↔ ∀ j : Fin n, j.val < k.val → f j = g j := by
  rw [activeList,activeList,List.ofFn_inj,funext_iff]
  exact ⟨fun h j hj ↦ h ⟨j.val,hj⟩,fun h j ↦ h _ j.isLt⟩

theorem distinct_iff {n : ℕ} (t : Table n) : t.Distinct ↔ ProgramCode.WellFormed t.program := by
  have hkey : (t.program.table.map (fun r ↦ (r.state,r.inputSymbol,r.workSymbols))).Nodup ↔ t.Distinct := by
    simp only [Table.program,activeList,List.map_ofFn, List.nodup_ofFn, Function.Injective, Function.comp_apply,
      Row.rule, Prod.mk.injEq, Fin.val_inj]
    constructor
    · intro h i j hi hj he ha hw
      have e := h (a₁ := ⟨i.val,hi⟩) (a₂ := ⟨j.val,hj⟩)
        ⟨he,ha,(read_eq _ _ _).mpr hw⟩
      exact Fin.ext (congrArg (Fin.val (n := t.rows.val)) e)
    · intro hd i j h
      have e := hd _ _ i.isLt j.isLt h.1 h.2.1 ((read_eq _ _ _).mp h.2.2)
      exact Fin.ext (congrArg (Fin.val (n := n)) e)
  refine ⟨fun hd ↦ ⟨hkey.mpr hd,?_⟩, fun hg ↦ hkey.mp hg.1⟩
  intro r hr
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hr
  constructor
  · exact List.length_ofFn
  · simp only [Row.rule, Row.action]
    split
    · trivial
    · split
      · exact List.length_ofFn
      · exact ⟨List.length_ofFn,List.length_ofFn⟩

end SignedProgram

end SpectralBooks
end LinearAlgebra
end OAI
