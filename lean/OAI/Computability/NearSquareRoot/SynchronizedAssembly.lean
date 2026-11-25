import OAI.Computability.NearSquareRoot.SynchronizedBlockSlots
import OAI.Computability.NearSquareRoot.SynchronizedSelected

/-! # Global slots for synchronized short Fourier transforms

Parallel local Fourier words on disjoint blocks become a word of global
permutations, product phase diagonals, and selected-bit normalized Walsh
transforms. There are at most 24 global slots per layer of the longest
local word.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace ShortFourier

open Matrix SynchronizedLayers SynchronizedPadding

variable {ι : Type} [Fintype ι] [DecidableEq ι] {A S : ι → Type}
  [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]
  [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)]

/-- The three allowed physical layer shapes in the synchronized transform. -/
inductive GlobalStage (address : ∀ i, A i ≃ Fin 2 × S i) :
    Matrix (∀ i, A i) (∀ i, A i) ℂ → Prop
  | permutation (p : ∀ i, Equiv.Perm (A i)) :
      GlobalStage address ((Equiv.piCongrRight p).toPEquiv.toMatrix : Matrix _ _ ℂ)
  | diagonal (d : ∀ i, A i → ℂ) (h : ∀ i x, ‖d i x‖ = 1) :
      GlobalStage address (Matrix.diagonal (fun x => ∏ i, d i (x i)))
  | walsh (active : Finset ι) :
      GlobalStage address (tensorMatrix (SynchronizedSelected.block active address))

private abbrev LocalScheduleLayer (A : ι → Type) :=
  Layer (fun i => Slot (A i)) (fun _ op => op.kind)

private def permutationOrId {X : Type} : Option (Slot X) → Equiv.Perm X
  | some (.permutation p) => p
  | _ => Equiv.refl X

private def phaseOrOne {X : Type} : Option (Slot X) → X → ℂ
  | some (.phase d _) => d
  | _ => fun _ => 1

private theorem phaseOrOne_norm {X : Type} (o : Option (Slot X)) (x : X) : ‖phaseOrOne o x‖ = 1 := by
  cases o with
  | none => exact norm_one
  | some op =>
    cases op with
    | phase _ h => exact h _
    | permutation _ | walsh => exact norm_one

noncomputable section

private abbrev localMatrix (address : ∀ i, A i ≃ Fin 2 × S i) (l : LocalScheduleLayer A) :=
  applyLayer (fun _ op => op.kind) (fun i => Slot.matrix (address i)) l

omit [∀ i, Fintype (A i)] [∀ i, Fintype (S i)] in
private theorem slot_shape (address : ∀ i, A i ≃ Fin 2 × S i) (l : LocalScheduleLayer A) :
    GlobalStage address (tensorMatrix (localMatrix address l)) := by
  classical
  cases hk : l.slot with
  | permutation =>
    let p (i : ι) := permutationOrId (l.action i)
    have hm (i : ι) : localMatrix address l i = (p i).toPEquiv.toMatrix := by
      cases ha : l.action i with
      | none =>
        simp [localMatrix, applyLayer, p, permutationOrId, ha]
      | some op =>
        have h := (l.compatible i op ha).trans hk
        cases op <;> simp_all [localMatrix, applyLayer, p, permutationOrId, Slot.kind, Slot.matrix]
    rw [funext hm, tensorMatrix_blockPerm]
    exact .permutation p
  | diagonal =>
    let d (i : ι) := phaseOrOne (l.action i)
    have hm (i : ι) : localMatrix address l i = diagonal (d i) := by
      cases ha : l.action i with
      | none => simp [localMatrix, applyLayer, d, phaseOrOne, ha]
      | some op =>
        have h := (l.compatible i op ha).trans hk
        cases op <;> simp_all [localMatrix, applyLayer, d, phaseOrOne, Slot.kind, Slot.matrix]
    rw [funext hm, tensorMatrix_diagonal]
    exact .diagonal d fun i x => phaseOrOne_norm _ x
  | walsh =>
    let active := Finset.univ.filter fun i => (l.action i).isSome
    have hm (i : ι) : localMatrix address l i = SynchronizedSelected.block active address i := by
      cases ha : l.action i with
      | none =>
        simp [localMatrix, applyLayer, active, ha, SynchronizedSelected.block]
      | some op =>
        have h := (l.compatible i op ha).trans hk
        cases op <;> simp_all [localMatrix, applyLayer, active, Slot.kind, Slot.matrix,
          SynchronizedSelected.block]
        rfl
    rw [funext hm]
    exact .walsh active

omit [∀ i, Fintype (A i)] [∀ i, Fintype (S i)] in
/-- Tensor the optional local operations in a single compatible slot. -/
theorem GlobalStage.of_layer (address : ∀ i, A i ≃ Fin 2 × S i)
    (l : Layer (fun i => Slot (A i)) (fun _ op => op.kind)) :
    GlobalStage address
      (tensorMatrix (applyLayer (fun _ op => op.kind) (fun i => Slot.matrix (address i)) l)) :=
  slot_shape address l

/-- The same Walsh and phase slots suffice across all blocks, even when the
local primitive words differ in their kinds, gates, and individual lengths. -/
theorem global_schedule (address : ∀ i, A i ≃ Fin 2 × S i)
    (M : ∀ i, Matrix (A i) (A i) ℂ) (d : ℕ) (hd : ∀ i, HasShortWord (M i) d) :
    ∃ word : List (Matrix (∀ i, A i) (∀ i, A i) ℂ),
      word.prod = tensorMatrix M ∧ (∀ N ∈ word, GlobalStage address N) ∧ word.length = 24 * d := by
  classical
  choose ops hop hlen using fun i => (hd i).compile (address i)
  let plan := schedule (fun (i : ι) (op : Slot (A i)) => op.kind) (8*d) ops
  refine ⟨plan.map (fun l => tensorMatrix (localMatrix address l)), ?_, ?_, ?_⟩
  · rw [show (plan.map (fun l => tensorMatrix (localMatrix address l))).prod =
        tensorMatrix (fun i => ((ops i).map (Slot.matrix (address i))).prod) from
          schedule_tensor _ _ ops hlen]
    simp only [hop]
  · intro N hN
    obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hN
    exact slot_shape address l
  · simp [plan, ← Nat.mul_assoc]

end

end ShortFourier

end NearSquareRoot
end Computability
end OAI
