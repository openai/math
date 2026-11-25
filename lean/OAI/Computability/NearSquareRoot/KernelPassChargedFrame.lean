import OAI.Computability.NearSquareRoot.KernelPassMonomial
import OAI.LinearAlgebra.FiniteFourier.PrimeRectangleTransfer

/-! # Binary coordinates for the paired label frames

The distinguished component occupies coordinate zero, followed by the auxiliary
coordinates. In these coordinates each label's two frames carry the routing
form to the ordinary dot product.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

noncomputable section

namespace KernelPass

open OAI.LinearAlgebra.FiniteFourier

/-- Attach the distinguished bit to the front of the auxiliary word. -/
def prependCoord : (D : ℕ) → 0 < D → (ZMod 2 × Bits (D-1)) ≃ₗ[ZMod 2] Bits D
  | 0, h => (Nat.not_lt_zero _ h).elim
  | n+1, _ => Fin.consLinearEquiv (ZMod 2) (fun _ : Fin (n+1) => ZMod 2)

theorem prependCoord_pair (D : ℕ) (h : 0 < D) (x y : ZMod 2 × Bits (D-1)) :
    dotProduct (prependCoord D h x) (prependCoord D h y) =
      x.1 * y.1 + ∑ i, x.2 i * y.2 i := by
  cases D with
  | zero => exact (Nat.not_lt_zero _ h).elim
  | succ n =>
    rw [dotProduct, Fin.sum_univ_succ]
    rfl

@[simp] theorem prependCoord_zeroCoord (D : ℕ) (h : 0 < D) (x : ZMod 2 × Bits (D-1)) :
    prependCoord D h x ⟨0,h⟩ = x.1 := by
  cases D with
  | zero => exact (Nat.not_lt_zero _ h).elim
  | succ n => rfl

theorem prependCoord_unit (D : ℕ) (h : 0 < D) :
    prependCoord D h (1,0) = Pi.single ⟨0,h⟩ 1 := by
  cases D with
  | zero => exact (Nat.not_lt_zero _ h).elim
  | succ n =>
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · change (1 : ZMod 2) = (Pi.single (0 : Fin (n+1)) 1 : Bits (n+1)) 0
      simp
    · change (0 : ZMod 2) = (Pi.single (0 : Fin (n+1)) 1 : Bits (n+1)) j.succ
      simp

variable {L b : ℕ} (G : BitRoutingGeometry 2 L b) (v : BitLabel L b)

/-- The paired coordinate maps of a label, with the distinguished slot and
auxiliary word concatenated into a single fixed-width binary address. -/
def labelFrame (second : Bool) : G.Space ≃ₗ[ZMod 2] Bits G.D :=
  (G.halfChart v second).trans (prependCoord G.D G.dim_pos)

theorem labelFrame_pair (x y : G.Space) :
    G.form x y = dotProduct (labelFrame G v false x) (labelFrame G v true y) := by
  rw [labelFrame, labelFrame, LinearEquiv.trans_apply, LinearEquiv.trans_apply,
    prependCoord_pair]
  exact (G.labelCharts v).pair x y

theorem labelFrame_symm_pair (x y : Bits G.D) :
    G.form ((labelFrame G v false).symm x) ((labelFrame G v true).symm y) = dotProduct x y := by
  rw [labelFrame_pair G v, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]

theorem labelFrame_zeroCoord (second : Bool) (x : G.Space) :
    labelFrame G v second x ⟨0,G.dim_pos⟩ = G.form (G.vector v) x := by
  rw [labelFrame, LinearEquiv.trans_apply, prependCoord_zeroCoord, G.halfChart_coordinate]

theorem labelFrame_vector (second : Bool) :
    labelFrame G v second (G.vector v) = Pi.single ⟨0,G.dim_pos⟩ 1 := by
  rw [labelFrame, LinearEquiv.trans_apply]
  have hv : G.halfChart v second (G.vector v) = (1,0) := by
    cases second
    · exact (G.labelCharts v).first_vector
    · exact (G.labelCharts v).second_vector
  rw [hv, prependCoord_unit]

end KernelPass

end

end NearSquareRoot
end Computability
end OAI
