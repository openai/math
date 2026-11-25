import OAI.Hierarchy.TaggedWideControl

namespace OAI
/-! # Heights and numbers of row slots for the two kinds of control sort -/

noncomputable section
namespace Hierarchy.Tagged.WideHost
open scoped Classical BigOperators

namespace DualControlIndex

abbrev Bank := Fin 28 ⊕ Fin 28
def side : Fin 56 ≃ Bank := (finSumFinEquiv (m:=28) (n:=28)).symm
def bankSize (left right : ℕ) : Bank → ℕ := Sum.elim (fun _=>left) (fun _=>right)

theorem side_left (i : Fin 28) : side (i.castAdd 28)=Sum.inl i :=
  (finSumFinEquiv (m:=28) (n:=28)).symm_apply_apply (Sum.inl i)

theorem side_right (i : Fin 28) : side (Fin.natAdd 28 i)=Sum.inr i :=
  (finSumFinEquiv (m:=28) (n:=28)).symm_apply_apply (Sum.inr i)

end DualControlIndex
open DualControlIndex

def dualControlRows (h slots₀ slots₁ : ℕ) : Fin 57→ℕ :=
  Fin.cases (2^h) (fun j=>bankSize slots₀ slots₁ (side j))

def dualControlSizes (h m₀ m₁ : ℕ) : Fin 57→ℕ :=
  Fin.cases h (fun j=>bankSize m₀ m₁ (side j))

@[simp] theorem dual_rows_tag (h slots₀ slots₁ : ℕ) : dualControlRows h slots₀ slots₁ 0=2^h := rfl

@[simp] theorem dual_rows_prefix (h slots₀ slots₁ : ℕ) (i : Fin 28) :
    dualControlRows h slots₀ slots₁ (i.castAdd 28).succ=slots₀ :=
  congrArg (bankSize slots₀ slots₁) (side_left i)

@[simp] theorem dual_rows_paid (h slots₀ slots₁ : ℕ) (i : Fin 28) :
    dualControlRows h slots₀ slots₁ (Fin.natAdd 28 i).succ=slots₁ :=
  congrArg (bankSize slots₀ slots₁) (side_right i)

@[simp] theorem dual_sizes_tag (h m₀ m₁ : ℕ) : dualControlSizes h m₀ m₁ 0=h := rfl

@[simp] theorem dual_sizes_prefix (h m₀ m₁ : ℕ) (i : Fin 28) :
    dualControlSizes h m₀ m₁ (i.castAdd 28).succ=m₀ :=
  congrArg (bankSize m₀ m₁) (side_left i)

@[simp] theorem dual_sizes_paid (h m₀ m₁ : ℕ) (i : Fin 28) :
    dualControlSizes h m₀ m₁ (Fin.natAdd 28 i).succ=m₁ :=
  congrArg (bankSize m₀ m₁) (side_right i)

theorem dual_control_sizes (h slots₀ slots₁ : ℕ) :
    (fun j=>controlHeight h (dualControlRows h slots₀ slots₁ j))=
      dualControlSizes h (controlHeight h slots₀) (controlHeight h slots₁) := by
  funext j
  refine Fin.cases ?_ (fun i=>?_) j
  · simp [dualControlRows,dualControlSizes,controlHeight,Nat.clog_pow 2 h (by decide)]
  · change controlHeight h (bankSize slots₀ slots₁ (side i))=bankSize _ _ (side i)
    cases side i <;> rfl

theorem dual_control_count (h slots₀ slots₁ : ℕ) {limit : ℝ}
    (tagFits : (2:ℝ)^h≤limit) (prefixFits : (slots₀:ℝ)≤limit) (paidFits : (slots₁:ℝ)≤limit) :
    ∀ j,(dualControlRows h slots₀ slots₁ j:ℝ)≤limit := by
  intro j
  refine Fin.cases ?_ (fun i=>?_) j
  · simpa using tagFits
  · change (bankSize slots₀ slots₁ (side i):ℝ)≤limit
    cases side i
    · exact prefixFits
    · exact paidFits

/-- Charge the original tag once and each occurrence of the two concrete
sorts at its own arity. -/
theorem dual_control_sum (h m₀ m₁ : ℕ) (price : ℕ→ℕ) :
    (∑ j : Fin 57,price (dualControlSizes h m₀ m₁ j))=price h+28*price m₀+28*price m₁ := by
  let f : Bank→ℕ := fun j=>price (bankSize m₀ m₁ j)
  rw [Fin.sum_univ_succ]
  change price h+(∑ i : Fin 56,f (side i))=_
  rw [side.sum_comp f,Fintype.sum_sum_type]
  simp [f,bankSize,Finset.sum_const,add_assoc]

end Hierarchy.Tagged.WideHost

end
end OAI
