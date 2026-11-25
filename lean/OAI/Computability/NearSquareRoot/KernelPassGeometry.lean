import OAI.Computability.NearSquareRoot.KernelPassFreeGeometry
import OAI.Computability.NearSquareRoot.KernelPassChargedLabels
import OAI.Computability.NearSquareRoot.KernelBinaryQueryTransfer

/-! # The compiled binary rectangle pencil

The free and charged routes use the same archived transfer in physical
coordinates. Their signed weights cancel every cross-label route. On each
label the diagonal transfer is the binary quadratic query.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace KernelPass.Rect.Binary

open OAI.LinearAlgebra.FiniteFourier BinaryQuery KernelNormalization
open scoped CyclotomicCode Classical BigOperators

noncomputable section

variable {L b : ℕ} {W : Type} [Fintype W] [DecidableEq W]
variable (S : System L b) (m : ℕ)

private def freePlans (r : Free L b) :
    FreeData (Charged.Axes (m := m) S.geometry) (Label L b) (Fin (m+1)) :=
  freeGeometry S.geometry r (physical (m+1) (S.D-1)) (freeSupport S r).weight

private def chargedPlans (r : Paid L b) :
    ChargedData (Charged.Axes (m := m) S.geometry) (Label L b) (Fin (m+1)) :=
  Charged.rectangleData S.geometry m (chargedSupport S r)

/-- A single finite restricted instruction list for the full row pencil. -/
def geometricPencil (B₀ : W → W → Coefficient) (B : Fin (m+1) → W → W → Coefficient) :
    On (Charged.Axes (m := m) S.geometry) (Label L b × W) (Label L b × W) :=
  pencil (freePlans S m) (chargedPlans S m) B₀ B

/-- Every label block carries the constant and quadratic-query row matrices. -/
theorem block_geometricPencil (B₀ : W → W → Coefficient) (B : Fin (m+1) → W → W → Coefficient)
    (h : ℕ) (w v : Label L b) (k l : W) :
    block (I := Label L b × W) (O := Label L b × W) (geometricPencil S m B₀ B) h (w,k) (v,l) =
      if w = v then value (B₀ k l) • (1 : Mat (Charged.Axes (m := m) S.geometry) h) +
        ∑ j, value (B j k l) • rationalLift (A := Charged.Axes (m := m) S.geometry) h (query (u := S.D-1) j) else 0 := by
  refine (block_pencil (freePlans S m) (chargedPlans S m) B₀ B (Charged.routed S.geometry m)
    (fun r => freeGeometry_factors S.geometry r (physical (m+1) (S.D-1)) (freeSupport S r).weight)
    (fun r => Charged.rectangleData_factors S.geometry m (chargedSupport S r))
    (weight_identity S) h w v k l).trans ?_
  by_cases e : w = v
  · subst v
    simp only [ite_true, Charged.routed]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    exact congrArg (fun M => value (B j k l) • rationalLift h M)
      (BinaryQuery.transfer_self S.geometry j w)
  · simp [e]

/-- The endpoint realizations give the binary stage bound for arbitrary
dyadic clock coefficients. -/
theorem calls_geometricPencil (B₀ : W → W → Coefficient) (B : Fin (m+1) → W → W → Coefficient) :
    (geometricPencil S m B₀ B).calls ≤ 2*S.D*Fintype.card W *
      (2*(2^b)^L*(1+b)^L + (m+1)*(2^L*(2^b)^(L/2))) := by
  simpa only [geometricPencil, Fintype.card_fin] using
    calls_binary_le S (freePlans S m) (chargedPlans S m) (fun _ => rfl) B₀ B
      (fun r v _ => freeGeometry_source_calls S.geometry r (physical (m+1) (S.D-1)) _ v)
      (fun r w _ => freeGeometry_target_calls S.geometry r (physical (m+1) (S.D-1)) _ w)
      (fun r j => Charged.rectangleData_calls S.geometry m (chargedSupport S r) j)

end
end KernelPass.Rect.Binary

end NearSquareRoot
end Computability
end OAI
