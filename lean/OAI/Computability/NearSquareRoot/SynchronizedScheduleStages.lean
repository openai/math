import OAI.Computability.NearSquareRoot.SynchronizedScheduleSemantics
import OAI.Computability.NearSquareRoot.SynchronizedAssembly

/-! # Global stages of the generated schedule

When the instructions actually occurring in a block are phases, permutations
and fixed-bit Walsh transforms, each encoded row acts by the corresponding
physical global stage.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace SynchronizedLayers.ScheduleProgram

open IntegerMultiplication.Code ShortFourier SynchronizedPadding

variable {X : Type} {n : ℕ} {A S : Fin n → Type}
  [∀ i, DecidableEq (A i)]
  [∀ i, DecidableEq (S i)]

/-- The global operator represented by one row of optional local instructions. -/
noncomputable def rowMatrix (eval : ∀ i : Fin n, X → Matrix (A i) (A i) ℂ) (r : Row X) :=
  tensorMatrix (fun i => ((readBlock r i.val).map (eval i)).getD 1)

private theorem layerStage (kind : X → Kind) (bits : ∀ i, A i ≃ Fin 2 × S i)
    (eval : ∀ i, X → Matrix (A i) (A i) ℂ) (l : Layer (fun _ : Fin n => X) (fun _ => kind))
    (h : ∀ i x, l.action i = some x → ∃ s : Slot (A i), s.kind = kind x ∧ s.matrix (bits i) = eval i x) :
    GlobalStage bits (rowMatrix eval (serialize kind l)) := by
  classical
  have step (i : Fin n) : ∃ o : Option (Slot (A i)),
      (∀ s, o = some s → s.kind = l.slot) ∧
      (o.map (Slot.matrix (bits i))).getD 1 = ((l.action i).map (eval i)).getD 1 := by
    cases he : l.action i with
    | none => exact ⟨none, by simp⟩
    | some x =>
      obtain ⟨s, hs, hmat⟩ := h i x he
      exact ⟨some s, by simpa using hs.trans (l.compatible i x he), by simpa using hmat⟩
  choose op hk hm using step
  let layer : Layer (fun i => Slot (A i)) (fun _ s => s.kind) := ⟨l.slot, op, hk⟩
  have heq : rowMatrix eval (serialize kind l) =
      tensorMatrix (applyLayer (fun _ s => s.kind) (fun i => Slot.matrix (bits i)) layer) := by
    unfold rowMatrix
    apply congrArg tensorMatrix
    funext i
    rw [readBlock_serialize]
    exact (hm i).symm
  rw [heq]
  exact GlobalStage.of_layer bits layer

/-- Every generated row is a legal global stage. Only opcodes that occur in
the supplied local words need to have the indicated local matrix and kind. -/
theorem plan_globalStage (kind : X → Kind) (bits : ∀ i, A i ≃ Fin 2 × S i)
    (eval : ∀ i, X → Matrix (A i) (A i) ℂ) (w : Fin n → List X) (D : ℕ)
    (h : ∀ i x, x ∈ w i → ∃ s : Slot (A i), s.kind = kind x ∧ s.matrix (bits i) = eval i x)
    (r : Row X) (hr : r ∈ plan kind (List.ofFn w,tally D)) :
    GlobalStage bits (rowMatrix eval r) := by
  rw [plan_eq_schedule] at hr
  obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hr
  apply layerStage kind bits eval l
  intro i x hx
  apply h i x
  have hm : x ∈ (schedule (fun _ => kind) D w).filterMap (fun t => t.action i) :=
    List.mem_filterMap.mpr ⟨l, hl, hx⟩
  rw [schedule_filterMap] at hm
  exact List.mem_of_mem_take hm

/-- Exact product, legal stages, and depth all hold for one and the same
encoded descriptor stream. -/
theorem plan_correct [∀ i, Fintype (A i)] (kind : X → Kind) (bits : ∀ i, A i ≃ Fin 2 × S i)
    (eval : ∀ i, X → Matrix (A i) (A i) ℂ) (w : Fin n → List X) {D : ℕ}
    (hd : ∀ i, (w i).length ≤ D)
    (h : ∀ i x, x ∈ w i → ∃ s : Slot (A i), s.kind = kind x ∧ s.matrix (bits i) = eval i x) :
    let rows := plan kind (List.ofFn w,tally D)
    (rows.map (rowMatrix eval)).prod = tensorMatrix (fun i => ((w i).map (eval i)).prod) ∧
      (∀ r ∈ rows, GlobalStage bits (rowMatrix eval r)) ∧ rows.length = 3 * D := by
  exact ⟨plan_tensor kind eval w hd, plan_globalStage kind bits eval w D h,
    by simp [plan_eq_schedule]⟩

end SynchronizedLayers.ScheduleProgram

end NearSquareRoot
end Computability
end OAI
