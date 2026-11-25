import OAI.Hierarchy.ProbeFabricAddress
import OAI.Hierarchy.ProbePayloadPlacement

namespace OAI
/-! # Public address injection from the flat permutation board to the fabric's recursive columns -/
namespace Hierarchy.ProbeStage
noncomputable section

private def exterior (h : ℕ) : Fin (2^h) ↪ (Unit × Fin (2^h)) :=
  ⟨fun p=>((),p),fun _ _ eq=>congrArg Prod.snd eq⟩

def fabricBoard (h d : ℕ) : PayloadColumns h d ↪ (permutationFabric h d).AllColumns :=
  (exterior h).sumMap ((permutationFabric h d).unflatten.sumMap (exterior h))

@[simp] theorem fabricBoard_input (h d : ℕ) (p : Fin (2^h)) :
    fabricBoard h d (.inl p)=.inl ((),p) := rfl

@[simp] theorem fabricBoard_output (h d : ℕ) (p : Fin (2^h)) :
    fabricBoard h d (.inr (.inr p))=.inr (.inr ((),p)) := rfl

@[simp] theorem fabricBoard_stage (h d : ℕ) (z : StageColumns h d) :
    fabricBoard h d (.inr (.inl z))=.inr (.inl ((permutationFabric h d).unflatten z)) := rfl

end
end Hierarchy.ProbeStage

end OAI
