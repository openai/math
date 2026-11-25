import OAI.Computability.BorderVNP.PackedHistoryBoxErasure

/-! # At most one known paid template per static history row

An empty initial roster passes unchanged through subdivisions and parallel
copies. Each newly installed seed site has either an empty roster or the one
public table of its designated paid site.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Inherited.BoxRoster

open Crossing CellSparse Shortening Shortening.StaticRows Shortening.CombiningStep
open scoped Classical

variable {D m : ℕ} {K : Type*} [Field K] (e : PaidIdentity K D m) (number : e.Entry → ℕ)

/-- Exact two possible shapes of an erased public slot. -/
def Known (tables : List (List Factor)) : Prop :=
  tables=[] ∨ ∃ (a : Fin e.count) (v : (e.net a).Site), tables=[[PaidBox.tableFactor e number a v]]

private theorem template_known (t : TemplateSite e) : Known e number (template e number t) := by
  rcases t with _ | u | ⟨a,v⟩
  · exact Or.inl rfl
  · exact Or.inl rfl
  · exact Or.inr ⟨a,v,rfl⟩

private theorem sewn_known {s n : ℕ} (base : Fin s → List (List Factor)) (h : ∀ i, Known e number (base i))
    (i : Fin (siteCapacity e s n)) : Known e number (sewn e number base i) := by
  unfold sewn
  split
  · exact h _
  · exact template_known e number _

/-- A fixed inner sequence preserves the zero-or-one-paid-table classification. -/
theorem steps_known {b k : ℕ} {V : ℕ → ℕ} (seeds : Fin b → ℕ)
    (rect : ∀ i : Fin b, V (i.val+1)=siteCapacity e (k*V i.val) (seeds i))
    (base : Fin (V 0) → List (List Factor)) (h : ∀ i, Known e number (base i)) (j : ℕ) (r : Fin (V j)) :
    Known e number (steps e number seeds rect base j r) := by
  induction j with
  | zero => exact h r
  | succ j ih =>
    rw [steps]
    split
    · exact sewn_known e number _ (fun _ => ih _) _
    · exact Or.inl rfl

end Packing.Inherited.BoxRoster

namespace PackedHistoryCircuit.Normalized.SelectedSchedule

open Crossing Cover BorderVNP.Epoch BorderVNP.Epoch.Round Shortening Shortening.Adaptive Shortening.PublicCapacity
open Packing Packing.Inherited CellSparse EnrichedOuter Diagonal.ExternalSew
open scoped Classical

variable {D m : ℕ} [NeZero D] {K : Type} [Field K] {e : PaidIdentity K D m} (S : SiteSchedule e)
    (start : ℕ) (number : e.Entry → ℕ)

/-- Every slot of the canonical erased outer history is either empty or the
genuine one-copy body of a specific paid template of the fixed identity. -/
theorem historyRoster_known (t : ℕ) (i : Fin (boundaryShape S start t).sites) :
    BoxRoster.Known e number (historyRoster S start number (fun _ => []) t i) := by
  induction t with
  | zero => exact Or.inl rfl
  | succ t ih =>
    rw [historyRoster]
    apply BoxRoster.steps_known
    intro j
    unfold BoxRoster.subdivided
    split
    · exact ih _
    · exact Or.inl rfl

end PackedHistoryCircuit.Normalized.SelectedSchedule

namespace Diagonal.ExternalSew

open Crossing Cover BorderVNP.Epoch BorderVNP.Epoch.Round Shortening Shortening.Adaptive Shortening.PublicCapacity
open Packing Packing.Inherited CellSparse PackedHistoryCircuit.Normalized PackedHistoryCircuit.Normalized.EnrichedOuter
open scoped Classical

variable {D m : ℕ} [NeZero D] {K : Type} [Field K] {e : PaidIdentity K D m} {S : PackedHistoryCircuit.Normalized.SiteSchedule e}
    {start T : ℕ} (dir : Directory.Layout) (count : dir.entries=(fan S)^T*dir.sites) (number : e.Entry → ℕ)
    (pos : 0<(SelectedSchedule.boundaryShape S start T).sites)

/-- The actual immutable box list is empty, one paid table, or one opaque
original delivery key. It never contains a copy-expanded payload. -/
theorem scheduledBoxes_cases (i : Fin (SelectedSchedule.boundaryShape S start T).sites) :
    let bs := scheduledBoxes dir count number pos i
    bs=[] ∨ (∃ a v, bs=[.inl [PaidBox.tableFactor e number a v]]) ∨ ∃ j, bs=[.inr j] := by
  intro bs
  dsimp only [bs,scheduledBoxes]
  cases Function.partialInv _ i with
  | some j => exact Or.inr (Or.inr ⟨j,rfl⟩)
  | none =>
    rcases SelectedSchedule.historyRoster_known S start number T i with hx | ⟨a,v,hx⟩
    · exact Or.inl (by rw [hx]; rfl)
    · exact Or.inr (Or.inl ⟨a,v,by rw [hx]; rfl⟩)

end Diagonal.ExternalSew

end BorderVNP
end Computability
end OAI
