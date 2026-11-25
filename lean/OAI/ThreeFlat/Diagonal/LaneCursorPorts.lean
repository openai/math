import OAI.ThreeFlat.Diagonal.LaneCursorContraction

namespace OAI
/-! # The cursor tensor as a function of its incident half-wires -/

namespace ThreeFlat.Diagonal.LaneCursor
open scoped Classical

variable {k r : ℕ} {O D : Type*}

/-- Labels on all slots incident from one direction at one vertex. -/
abbrev PortFields (r : ℕ) (O D : Type*) := Fin ((r + 1) * 2) → O × D → Bool

def outgoingPorts (fields : Fields (k + 1) r O D) (i : Fin (k + 1))
    (lane : Lane (k + 1)) : PortFields r O D := fun s => fields i s lane

/-- The number on an incoming half-wire is read through the inverse
permutation of the actual lifted graph. -/
def incomingPorts (hk : 2 ≤ k + 1) (fields : Fields (k + 1) r O D) (i : Fin (k + 1))
    (lane : Lane (k + 1)) : PortFields r O D := fun s =>
  let p := (graph hk (r + 1)).actualTarget.symm ((i,s),lane)
  fields p.1.1 p.1.2 p.2

private theorem incoming_rotate (hk : 2 ≤ k + 1) (mask : O → Lane (k + 1))
    (fields : Fields (k + 1) r O D) (prev : Fin (k + 1)) (lane : Lane (k + 1)) (tag : O × D) :
    incomingPorts hk fields (finRotate _ prev) lane (selected mask tag.1 prev) tag =
      fields prev (selected mask tag.1 prev) (lane - axis prev (mask tag.1 prev)) tag := by
  let s : Fin ((r + 1) * 2) := selected mask tag.1 prev
  change fields ((finRotate _).symm (finRotate _ prev)) s
    (lane - axis ((finRotate _).symm (finRotate _ prev)) (finProdFinEquiv.symm s).2) tag = _
  rw [Equiv.symm_apply_apply]
  have h : (finProdFinEquiv.symm s).2 = mask tag.1 prev := by
    dsimp only [s, selected]
    rw [Equiv.symm_apply_apply]
  rw [h]

private theorem next_eq (prev i : Fin (k + 1)) (h : i.val = prev.val + 1) :
    finRotate _ prev = i := by
  apply Fin.ext
  have hn : prev ≠ Fin.last k := by
    intro hl
    simp only [hl, Fin.val_last] at h
    omega
  rw [coe_finRotate_of_ne_last hn, h]

/-- The actual local tests applied to outgoing and incoming port strings. -/
def PortChecks (mask : O → Lane (k + 1)) (i : Fin (k + 1))
    (outwards inwards : PortFields r O D) : Prop :=
  (∀ s tag, s ≠ selected mask tag.1 i → outwards s tag = false) ∧
  ∀ prev : Fin (k + 1), i.val = prev.val + 1 → ∀ tag,
    outwards (selected mask tag.1 i) tag = inwards (selected mask tag.1 prev) tag

theorem portChecks_iff (hk : 2 ≤ k + 1) (mask : O → Lane (k + 1)) (fields : Fields (k + 1) r O D)
    (i : Fin (k + 1)) (lane : Lane (k + 1)) :
    PortChecks mask i (outgoingPorts fields i lane) (incomingPorts hk fields i lane) ↔
      LocalChecks mask fields i lane := by
  constructor <;> rintro ⟨unused, same⟩ <;> refine ⟨unused, ?_⟩ <;> intro prev step tag
  · simpa only [outgoingPorts, ← next_eq prev i step, incoming_rotate] using same prev step tag
  · simpa only [outgoingPorts, ← next_eq prev i step, incoming_rotate] using same prev step tag

variable {F : Type*} [CommSemiring F]

/-- This tensor has two port-string arguments. It can be used as an initial
vertex factor for a wire graph with independently numbered incoming slots. -/
noncomputable def portTensor (mask : O → Lane (k + 1))
    (bucket : Lane (k + 1) → (O × D → Bool) → (O × D → Bool) → F)
    (i : Fin (k + 1)) (lane : Lane (k + 1)) (outwards inwards : PortFields r O D) : F :=
  if PortChecks mask i outwards inwards then
    if i = 0 then bucket lane
      (fun tag => outwards (selected mask tag.1 0) tag)
      (fun tag => inwards (selected mask tag.1 (Fin.last k)) tag)
    else 1
  else 0

theorem portTensor_eq (hk : 2 ≤ k + 1) (mask : O → Lane (k + 1))
    (bucket : Lane (k + 1) → (O × D → Bool) → (O × D → Bool) → F)
    (fields : Fields (k + 1) r O D) (i : Fin (k + 1)) (lane : Lane (k + 1)) :
    portTensor mask bucket i lane (outgoingPorts fields i lane) (incomingPorts hk fields i lane) =
      vertexFactor mask bucket fields i lane := by
  have last (tag : O × D) : incomingPorts hk fields 0 lane (selected mask tag.1 (Fin.last k)) tag =
      delivered mask fields lane tag := by
    simpa only [finRotate_last, delivered] using incoming_rotate hk mask fields (Fin.last k) lane tag
  by_cases hi : i = 0
  · subst i
    simp only [portTensor, portChecks_iff, vertexFactor, last, outgoingPorts]
    rfl
  · simp only [portTensor, portChecks_iff, vertexFactor, hi, ite_false]

end ThreeFlat.Diagonal.LaneCursor

end OAI
