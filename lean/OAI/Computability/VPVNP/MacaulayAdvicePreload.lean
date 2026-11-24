import OAI.Computability.VPVNP.MacaulayLeafBudgets
import OAI.Computability.VPVNP.MacaulaySignedCoefficient

/-! # Capacity of the actual coefficient-reader advice banks

The checker serialization and the selected mask and extension-field values
are present in full. Both banks use finite port types. Each immutable stack
fits the common live-space budget used by the row phases.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RankQuery.Stack.MacaulayRead.Arms

open RAMTape RadicalCertificate.MonomialIndex

variable {p e t : ℕ} {c : SliceArithmetic.Vector p e}

/-- Immutable pin mask, scalar table, width markers and arithmetic advice. -/
theorem pin_preload_length (w v : ℕ) (pins : Finset (Fin t)) (a : Fin t → Scalar c)
    (i : AffinePin.Query.Port) :
    (AffinePin.Query.frame (AffinePin.Query.advice w v pins a) c v {} i).length ≤ AffinePin.Query.storage t e w v := by
  rcases i with i|i
  · cases i <;> simp [AffinePin.Query.frame, AffinePin.Stage.frame, AffinePin.Query.advice,
      AffinePin.Query.mask_length, AffinePin.Query.values_length, AffinePin.Query.storage] <;> omega
  · rcases i with i|i
    · simp [AffinePin.Query.frame, SliceArithmetic.AddCall.clean]
    · cases i <;> simp [AffinePin.Query.frame, SliceArithmetic.AddCall.clean, SliceArithmetic.MultiplyCall.external,
        AffinePin.Query.storage] <;> omega

/-- Disjoint ports for the signed equation-coefficient reader and the affine pin mask and value
reader. -/
abbrev CoefficientPort := JointScalar.Leaf.Port ⊕ AffinePin.Query.Port

/-- The checker words and affine advice occupy disjoint physical banks. -/
def coefficientAdvice (L : JointScalar.Leaf.Layout) (w v : ℕ) (pins : Finset (Fin t)) (a : Fin t → Scalar c) :
    Stacks CoefficientPort :=
  Sum.elim (JointScalar.Leaf.clean L [] [] []) (AffinePin.Query.frame (AffinePin.Query.advice w v pins a) c v {})

theorem coefficientAdvice_loaded (L : JointScalar.Leaf.Layout) (w v : ℕ) (pins : Finset (Fin t))
    (a : Fin t → Scalar c) :
    SignedLeaf.Loaded L Sum.inl (coefficientAdvice L w v pins a) ∧
    Pin.Preloaded (Function.Embedding.inr) (AffinePin.Query.advice w v pins a) c v (coefficientAdvice L w v pins a) :=
  ⟨fun _ _ _ _ => rfl, fun _ => rfl⟩

/-- The same prime-independent bound covers all immutable coefficient slots
and the constant zero and one field encodings. -/
theorem coefficientAdvice_preload {P : ReaderPlan} {w v signedSpace E V : ℕ} {L : JointScalar.Leaf.Layout}
    (ht : P.arity=t) (he : e≤E) (hv : v≤V)
    (hs : JointScalar.Leaf.bankSize L w (t*w) ≤ signedSpace)
    (pins : Finset (Fin t)) (a : Fin t → Scalar c) (data : Bool → PairCall.Inputs) (harity : ∀ b, (data b).arity=t)
    (constants : Bool → List Bool) (hconst : ∀ b, (constants b).length ≤ e*v) :
    Preload (w := w) (P.live E V w signedSpace) data constants (coefficientAdvice L w v pins a) := by
  have hsize := Nat.mul_le_mul he hv
  have hpin : AffinePin.Query.storage t e w v ≤ AffinePin.Query.space t E w V :=
    (Nat.le_add_right ..).trans (ReaderPlan.pin_space_mono t w he hv)
  refine ⟨by dsimp [ReaderPlan.live]; omega, fun b => ?_, fun b => ?_, fun j => ?_⟩
  · rw [harity b,← ht]
    dsimp [ReaderPlan.live]; omega
  · have h := (hconst b).trans hsize
    dsimp [ReaderPlan.live]; omega
  · cases j with
    | inl i =>
      have h := (JointScalar.Leaf.clean_length_le L w (t*w) i).trans hs
      change (JointScalar.Leaf.clean L [] [] [] i).length ≤ _
      dsimp only [ReaderPlan.live]; omega
    | inr i =>
      have h := (pin_preload_length w v pins a i).trans hpin
      change (AffinePin.Query.frame (AffinePin.Query.advice w v pins a) c v {} i).length ≤ _
      dsimp only [ReaderPlan.live]; rw [ht]; omega

end RankQuery.Stack.MacaulayRead.Arms

end VPVNP
end Computability
end OAI
