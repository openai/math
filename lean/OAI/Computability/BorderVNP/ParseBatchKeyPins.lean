import OAI.Computability.BorderVNP.ParseBatchLookupFrame

/-! # Physical pins of concatenated binary keys -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace ParseBatchLookup

/-- Pointwise functions commute with binary field concatenation. -/
theorem map_prepend {α β : Type*} {a w : ℕ} (f : α → β)
    (high : Fin a → α) (low : Fin w → α) :
    f ∘ prepend high low = prepend (f ∘ high) (f ∘ low) := by
  induction a with
  | zero => rfl
  | succ a ih =>
    funext i
    refine Fin.cases rfl (fun j => ?_) i
    exact congrFun (ih (fun k => high k.succ)) j

/-- Pointwise evaluation commutes with packing all three fields. -/
theorem map_bits {α β : Type*} {a w : ℕ} (f : α → β) (high : Fin a → α) (tag : α)
    (low : Fin w → α) : f ∘ bits high tag low = bits (f ∘ high) (f tag) (f ∘ low) := by
  simp only [bits, map_prepend]
  congr 1
  funext i
  exact Fin.cases rfl (fun _ => rfl) i

/-- The physical high-field pins are a left inverse to packing the high field. -/
theorem high_prepend {α : Type*} {a w : ℕ} (high : Fin a → α) (low : Fin w → α) :
    prepend high low ∘ highPin w = high := by
  induction a with
  | zero => exact Subsingleton.elim ..
  | succ a ih =>
    funext i
    refine Fin.cases rfl (fun j => ?_) i
    exact congrFun (ih (fun k => high k.succ)) j

/-- The physical low-field pins are a left inverse to packing the low field. -/
theorem low_prepend {α : Type*} {a w : ℕ} (high : Fin a → α) (low : Fin w → α) :
    prepend high low ∘ lowPin a = low := by
  induction a with
  | zero => rfl
  | succ a ih =>
    funext j
    exact congrFun (ih (fun k => high k.succ)) j

/-- All payload pins of a packed record read its original payload. -/
theorem selectedPayload_bits {a w : ℕ} (address : Fin a → Bool) (tag : Bool)
    (payload : Fin w → Bool) : selectedPayload a id (bits address tag payload) = payload := by
  funext j
  exact congrFun (low_prepend address (Fin.cons tag payload)) j.succ

/-- Every position of a concatenation has either a high-field or a low-field source. -/
theorem forall_prepend {α : Type*} {a w : ℕ} (P : α → Prop)
    (high : Fin a → α) (low : Fin w → α) (hh : ∀ i, P (high i)) (hl : ∀ j, P (low j)) :
    ∀ k, P (prepend high low k) := by
  induction a with
  | zero => exact hl
  | succ a ih => exact Fin.cases (hh 0) (ih (fun k => high k.succ) (fun k => hh k.succ))

end ParseBatchLookup

end BorderVNP
end Computability
end OAI
