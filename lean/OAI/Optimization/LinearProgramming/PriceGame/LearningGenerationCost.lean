import OAI.Computability.QuantumFactoring.BitStackGCD
import OAI.Computability.QuantumFactoring.BitStackListIndex
import OAI.Computability.QuantumFactoring.BitStackListLength
import OAI.Computability.QuantumFactoring.BitStackTabulate
import OAI.Optimization.LinearProgramming.PriceGame.LearningExperts

/-! Finite binary-stack programs for the historical-cell product. All list parsing,
copying, indexing and output growth are charged by the BitStack procedures. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Learning
namespace GenerationCost

open ExactQuantumFactoring.BitStackProgram
open ExactQuantumFactoring.BitStackProgram.Procedure

variable {α β γ : Type}

private theorem fold_append_eq (xs : List (List α)) (acc : List α) :
    xs.foldl (fun a x => a ++ x) acc = acc ++ xs.flatten := by
  induction xs generalizing acc with
  | nil => simp
  | cons x xs ih => simp [ih, List.append_assoc]

private theorem flatten_code_le (ea : α → List Bool) (xs : List (List α)) :
    (listCode ea xs.flatten).length ≤ (listCode (listCode ea) xs).length := by
  induction xs with
  | nil => simp [listCode]
  | cons x xs ih =>
    have h := listCode_length_append ea x xs.flatten
    simp only [List.flatten_cons, listCode_length_cons]
    omega

/-- Flatten a framed list, with an intermediate output bounded by the input
plus the old accumulator, even for arbitrary typed inputs. -/
noncomputable def flattenP (ea : α → List Bool) (da : α) :
    Procedure (listCode (listCode ea)) (listCode ea) List.flatten := by
  let step := (listAppend ea da).comp (swap (listCode ea) (listCode ea))
  let fold := foldList [] step Polynomial.X (by
    intro xs acc i
    change (listCode ea ((xs.take i).foldl (fun a x => a ++ x) acc)).length ≤ _
    rw [fold_append_eq]
    have h := listCode_length_append ea acc (xs.take i).flatten
    have h₁ := flatten_code_le ea (xs.take i)
    have h₂ := listCode_length_take_le (listCode ea) i xs
    simp only [Polynomial.eval_X]
    omega)
  exact (fold.comp ((identity (listCode (listCode ea))).pair
    (constant (listCode (listCode ea)) (listCode ea) []))).congrFun (by
      intro xs; simpa [Function.comp_apply, id_eq] using fold_append_eq xs [])

/-- Unary cardinality is bounded by the actual bit length of the input list. -/
noncomputable def lengthUnaryP (ea : α → List Bool) (da : α) :
    Procedure (listCode ea) unaryCode List.length := by
  let step := unarySuccessor.comp (second ea unaryCode)
  let rep := foldList da step Polynomial.X (by
    intro xs n i
    change (unaryCode ((xs.take i).foldl (fun n _ => n+1) n)).length ≤ _
    rw [fold_count]
    simp only [unaryCode, List.length_replicate, Polynomial.eval_X, List.length_take]
    have := list_length_le_code ea xs
    omega)
  exact (rep.comp ((identity (listCode ea)).pair (constant (listCode ea) unaryCode 0))).congrFun (by
    intro xs; simp [Function.comp_apply, id_eq])

/-- Map over a list while making the same separately framed context available
to each invocation. The length written to the tabulator is genuinely unary. -/
noncomputable def mapContextP {ea : α → List Bool} {eb : β → List Bool} {ec : γ → List Bool}
    (da : α) (db : β) {f : α × γ → β} (p : Procedure (prodCode ea ec) eb f) :
    Procedure (prodCode (listCode ea) ec) (listCode eb) (fun x => x.1.map fun a => f (a,x.2)) := by
  let env := prodCode (listCode ea) ec
  let whole := second unaryCode env
  let xs := first (listCode ea) ec
  let g := second (listCode ea) ec
  let i := unaryToBits.comp (first unaryCode env)
  let get := (listGet ea da).comp (i.pair (xs.comp whole))
  let body := p.comp (get.pair (g.comp whole))
  let run := tabulate (f := fun (x : List α × γ) k => f ((x.1.drop k).headD da,x.2)) db body
  exact (run.comp (((lengthUnaryP ea da).comp xs).pair (identity env))).congrFun (by
    rintro ⟨as,c⟩
    change (List.range as.length).map (fun k => f ((as.drop k).headD da, c)) =
      as.map (fun a => f (a,c))
    apply List.ext_getElem
    · simp
    · intro j hj hk
      have h : j < as.length := by simpa using hk
      simp [List.getElem?_eq_getElem h])

/-- Attach each entry in the first list to every tail in the second list. -/
def cross (xs : List α) (tails : List (List α)) : List (List α) :=
  xs.flatMap fun x => tails.map (x :: ·)

noncomputable def crossP (ea : α → List Bool) (da : α) :
    Procedure (prodCode (listCode ea) (listCode (listCode ea))) (listCode (listCode ea))
      (fun x => cross x.1 x.2) := by
  let row := mapContextP [] [] ((listCons ea).comp (swap (listCode ea) ea))
  let allRows := mapContextP da [] (row.comp (swap ea (listCode (listCode ea))))
  exact ((flattenP (listCode ea) []).comp allRows).congrFun (by
    intro x; rfl)

/-- A fixed number of possible features is compiled into the control, rather
than accepting an arbitrary depth from the input. -/
def boundedProduct (α : Type) : ℕ → List (List α) → List (List α)
  | 0, _ => [[]]
  | _+1, [] => [[]]
  | cap+1, xs :: rows => cross xs (boundedProduct α cap rows)

/-- For each absolute cap, one uniform finite program handles arbitrary input
lengths and entries. Its polynomial clock is part of the actual execution proof. -/
noncomputable def boundedProductP (ea : α → List Bool) (da : α) (cap : ℕ) :
    Procedure (listCode (listCode ea)) (listCode (listCode ea)) (boundedProduct α cap) := by
  induction cap with
  | zero => exact constant _ _ [[]]
  | succ k ih =>
    let en := listCode (listCode ea)
    let extend := (crossP ea da).comp
      ((listHead (listCode ea) []).pair (ih.comp (listTail (listCode ea))))
    exact ((choose extend (constant en en [[]])).comp
      ((listEmpty (listCode ea)).pair (identity en))).congrFun (by
        intro rows; cases rows <;> rfl)

theorem mem_boundedProduct_of_select {ι : Type} (choices : ι → List α) (chosen : ι → α)
    (rows : List ι) (cap : ℕ) (hcap : rows.length ≤ cap) (h : ∀ i ∈ rows, chosen i ∈ choices i) :
    rows.map chosen ∈ boundedProduct α cap (rows.map choices) := by
  induction cap generalizing rows with
  | zero => obtain rfl : rows = [] := List.length_eq_zero_iff.mp (by omega); simp [boundedProduct]
  | succ cap ih =>
    cases rows with
    | nil => simp [boundedProduct]
    | cons row rows =>
      have hh := h row (by simp)
      have ht := ih rows (by simpa using hcap) (by intro i hi; exact h i (by simp [hi]))
      simp only [List.map_cons, boundedProduct, cross, List.mem_flatMap, List.mem_map]
      exact ⟨chosen row,hh,rows.map chosen,ht,rfl⟩

end GenerationCost
end Learning
end PriceGame
end LinearProgramming
end Optimization
end OAI
