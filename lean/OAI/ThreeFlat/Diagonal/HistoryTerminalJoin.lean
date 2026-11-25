import OAI.ThreeFlat.Diagonal.TickSlotForest
import OAI.ThreeFlat.Diagonal.HistoryPackedSources
import OAI.ThreeFlat.BitNetwork.PinMap

namespace OAI
/-! # Fusing terminal physical pin projection with the slot root copy -/

namespace ThreeFlat.Diagonal.HistoryTerminalJoin

open BitNetwork.Ordered
open private mapSource from OAI.ThreeFlat.BitNetwork.PinMap
open scoped BigOperators
variable {F : Type*} {p n : ℕ} {arity : Fin n→ℕ}
variable (N : ∀ i, BitNetwork F (arity i)) (pin : ∀ i,Fin (arity i)→Fin p)

/-- The private bit counts and all trivalent factors stay unchanged by
assigning their physical external addresses. -/
def projected (i : Fin n) := (N i).restrictPins (some ∘ pin i)

def wire (i : Fin n) (j : Fin (arity i)) : BitSource 0 p := .pin (pin i j)

theorem same_source (i : Fin n) (r : Fin (N i).cells) (j : Fin 3) :
    (glue N (wire pin)).source (finSigmaFinEquiv ⟨i,r⟩) j =
      (TickSlotForest.network (projected N pin)).source (finSigmaFinEquiv ⟨i,r⟩) j := by
  rw [source_at]
  unfold TickSlotForest.network
  rw [source_at]
  cases h : (N i).source r j with
  | hidden b =>
    have proj : (projected N pin i).source r j=.hidden b := by
      exact congrArg (mapSource (some ∘ pin i)) h
    rw [proj]
    rfl
  | constant b =>
    have proj : (projected N pin i).source r j=.constant b := by
      exact congrArg (mapSource (some ∘ pin i)) h
    rw [proj]
    rfl
  | pin q =>
    have proj : (projected N pin i).source r j=.pin (pin i q) := by
      exact congrArg (mapSource (some ∘ pin i)) h
    rw [proj]
    rfl

theorem same_table (i : Fin n) (r : Fin (N i).cells) :
    (glue N (wire pin)).table (finSigmaFinEquiv ⟨i,r⟩) =
      (TickSlotForest.network (projected N pin)).table (finSigmaFinEquiv ⟨i,r⟩) := by
  unfold TickSlotForest.network
  rw [table_at,table_at]; rfl

theorem eval [CommSemiring F] (x : Fin p→Bool) :
    (TickSlotForest.network (projected N pin)).eval x = ∏ i, (N i).eval (x ∘ pin i) := by
  rw [TickSlotForest.eval]
  apply Finset.prod_congr rfl
  intro i _
  rw [projected,BitNetwork.restrictPins_eval]
  rfl

end ThreeFlat.Diagonal.HistoryTerminalJoin

end OAI
