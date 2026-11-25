import OAI.Computability.NearSquareRoot.InterchangeBQuestCore
import OAI.Computability.NearSquareRoot.InterchangeBQuestProduct

/-!
# Preserving a spectator during a bounded recursive call

A subtree can stay below the active tree on register zero. Its linear
volume is charged to the parent allowance. The child tariffs, data peak
and return peak are inherited unchanged.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace InterchangeSpace

open IntegerMultiplication.Code IntegerMultiplication.Strip IntegerMultiplication.Loom
  NearSquareRoot.Space

variable {I Y : Type} {job : Job Y} {w : I → ℕ} {uses : I → List Y} {p q : I → Tree}

/-- Execute the body on the first field while the second is parked. -/
theorem Body.pack (h : Body job w uses p q) (v : I → Tree)
    (hv : ∃ C : ℕ, ∀ i, (v i).count ≤ C*(w i+1)) :
    Body job w uses (together p v) (together q v) := by
  obtain ⟨cmd,K,exec⟩ := h.build
  obtain ⟨C,sz⟩ := hv
  refine ⟨onFirst cmd,K+C+7,?_⟩
  intro i parent env price childSpace childDepth child deck base hdeck
  have e := exec i parent env price childSpace childDepth child (pile 0 (v i) deck)
    (base+(v i).count) (hdeck.pile 0 _)
  apply (BoundedFits.onFirst e).mono
  all_goals
    have := sz i
    simp only [Nat.add_mul]
    omega

variable {r : Regime I} {n l : I → ℕ} {zone : I → Y → Prop} {limit : ℤ}

/-- An `Alive` witness supplies the spectator allowance at a single common
polynomial degree for the whole body. -/
theorem BQuest.pack (h : BQuest job r n l uses p q) (v : I → Tree)
    (hv : Alive r n l v) : BQuest job r n l uses (together p v) (together q v) := by
  obtain ⟨k,body⟩ := h.eligible
  obtain ⟨d,C,hs⟩ := rip_volumes hv
  have run := body.mono (massNat_mono r n l (le_max_left k d))
  refine ⟨max k d,?_⟩
  apply run.pack v
  refine ⟨C, fun i => (hs i).1.trans (Nat.mul_le_mul_left _ ?_)⟩
  exact (massNat_mono r n l (le_max_right k d) i).trans (Nat.le_succ _)

/-- Preserving a spectator uses the same list of recursive requests. -/
theorem BHop.pack (h : BHop job r n l zone limit p q) (v : I → Tree)
    (hv : Alive r n l v) : BHop job r n l zone limit (together p v) (together q v) := by
  obtain ⟨used,allowed,price,body⟩ := h.safe
  exact ⟨used,allowed,price,body.pack v hv⟩

end InterchangeSpace

end NearSquareRoot
end Computability
end OAI
