import OAI.Computability.NearSquareRoot.CRTControlledBenesParallel
import OAI.Computability.NearSquareRoot.PrecisionGridPassSpace

/-! # A bounded physical sweep of strongly typed stages

The available space must contain the descriptor forest, the array between any
two passes, and the workspace of one pass. The compiled loop reuses this allowance.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Controlled
open IntegerMultiplication IntegerMultiplication.Code NearSquareRoot.Space

/-- Run a variable supplied list of stages on arbitrary data with different array
types for different inputs. Time charges the descriptors and calls. -/
theorem boundedSchedule {X A : Type*} [Inhabited A] {D : X → Type*}
    (stages : X → List A) (key : X → A → Tree) (box : (x : X) → D x → Tree)
    (next : (x : X) → D x → A → D x) (charge : X → A → ℕ) (allowance volume : X → ℕ)
    (step : BoundedTask (fun i : (x : X) × {a // a ∈ stages x} × D x => charge i.1 i.2.1)
      (fun i => volume i.1)
      (fun i => .fork (key i.1 i.2.1) (box i.1 i.2.2))
      (fun i => box i.1 (next i.1 i.2.2 i.2.1)))
    (forestCap : ∀ x, (Task.forest (key x) (stages x)).count ≤ volume x)
    (dataCap : ∀ x d, (box x d).count ≤ volume x)
    (callCap : ∀ x, ∀ a ∈ stages x, charge x a + (key x a).count + 1 ≤ allowance x) :
    BoundedTask (fun i : (x:X) × D x => (stages i.1).length * allowance i.1 + 1)
      (fun i => volume i.1)
      (fun i => .fork (Task.forest (key i.1) (stages i.1)) (box i.1 i.2))
      (fun i => box i.1 ((stages i.1).foldl (next i.1) i.2)) := by
  let Y := (x : X) × D x
  let m (y : Y) := (stages y.1).length
  let atStage (y : Y) (j : ℕ) : A := ((stages y.1)[j]?).getD default
  let data (y : Y) j := ((stages y.1).take j).foldl (next y.1) y.2
  let visit (i : (y : Y) × Fin (m y)) : (x : X) × {a // a ∈ stages x} × D x :=
    ⟨i.1.1, ⟨(stages i.1.1)[i.2.val],List.getElem_mem i.2.isLt⟩, data i.1 i.2.val⟩
  have elem (y : Y) (i : Fin (m y)) : atStage y i.val = (stages y.1)[i.val] := by
    simp only [atStage,List.getElem?_eq_getElem i.isLt,Option.getD_some]
  have same (y : Y) : (List.range (m y)).map (atStage y) = stages y.1 := by
    apply List.ext_getElem
    · simp [m]
    · intro j h₁ h₂
      simp only [List.getElem_map, List.getElem_range]
      exact elem y ⟨j,h₂⟩
  have forestEq (y : Y) :
      Task.forest (fun j => key y.1 (atStage y j)) (List.range (m y)) =
        Task.forest (key y.1) (stages y.1) := by
    rw [← Task.forest_map, same]
  have sweep := BoundedTask.indexedPasses m (fun y j => key y.1 (atStage y j))
    (fun y j => box y.1 (data y j)) (fun y j => charge y.1 (atStage y j)) (fun y _ => volume y.1)
    (fun y => volume y.1) ((step.on visit).conform (fun i => by simp [visit,elem]) (fun _ => rfl)
      (fun i => by simp [visit,elem]) (fun i => by
        dsimp only [visit,data]
        rw [List.take_succ_eq_append_getElem i.2.isLt, List.foldl_append]
        rfl))
    (fun y => (forestEq y) ▸ forestCap y.1) (fun y j _ => dataCap _ _) (fun _ _ _ => le_rfl)
  have out := sweep.mono (time' := fun y => m y * allowance y.1 + 1)
    (fun y => Nat.succ_le_succ (by
      calc
        _ ≤ ∑ j ∈ Finset.range (m y), allowance y.1 := by
          apply Finset.sum_le_sum
          intro j hj
          let i : Fin (m y) := ⟨j, Finset.mem_range.mp hj⟩
          have hm : atStage y i.val ∈ stages y.1 := (elem y i) ▸ List.getElem_mem i.isLt
          exact callCap _ _ hm
        _ = _ := by simp)) (fun _ => le_rfl)
  exact out.conform (fun _ => rfl) (fun _ => rfl) (fun y => by simp [forestEq,data])
    (fun y => by simp [data,m])

end Controlled

end NearSquareRoot
end Computability
end OAI
