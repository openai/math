import OAI.Computability.NearSquareRoot.KernelPassBridge
import OAI.Computability.NearSquareRoot.KernelPassEndpoints
import OAI.Computability.NearSquareRoot.KernelPassRectBinary
import OAI.Computability.NearSquareRoot.KernelPassRational

/-! # Physical endpoint plans for every free incidence of the binary system -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace KernelPass.Rect.Binary

open OAI.LinearAlgebra.FiniteFourier KernelNormalization Module Matrix
open scoped Classical

noncomputable section

variable {A L b m : ℕ} (G : BitRoutingGeometry 2 L b) (R : Free L b)
  (e : Bits A ≃ₗ[ZMod 2] G.RowAddress m 1)

private abbrev H := G.targetSpan R.val
private abbrev P := (H G R).orthogonalBilin G.form

private theorem dim_add : finrank (ZMod 2) (P G R) + finrank (ZMod 2) (H G R) = G.D := by
  let s := G.sharedCharts R.val
  have eq : finrank (ZMod 2) (P G R) = s.c := by
    have e' := endpointAxisEquiv ((s.dual).trans (LinearEquiv.prodComm _ _ _)) (P G R)
      (fun x => s.mem_dual x)
    simpa using e'.finrank_eq
  rw [eq, Nat.add_comm]
  exact s.dim_eq

private def sourceM {v : Label L b} (hv : v ∈ bitSources R.val) : Local A :=
  (((2:ℂ)⁻¹ ^ finrank (ZMod 2) (H G R)) •
    primeSourceEndpoint (f := 1) (J := Fin m) binaryRoot 1
      (G.sourceSlice R.val R.property hv false) (G.sourceSlice R.val R.property hv true)).submatrix e e

private def targetM {w : Label L b} (hw : w ∈ bitTargets R.val) : Local A :=
  (((2:ℂ)⁻¹ ^ finrank (ZMod 2) (P G R)) •
    primeTargetEndpoint (f := 1) (J := Fin m) binaryRoot 1
      (G.targetSlice R.val hw false) (G.targetSlice R.val hw true)).submatrix e e

private theorem sourceReal {v : Label L b} (hv : v ∈ bitSources R.val) :
    Realizes (2*finrank (ZMod 2) (H G R)) (sourceM G R e hv) :=
  (Realizes.geometricEndpoints (G.sourceSlice R.val R.property hv false)
    (G.sourceSlice R.val R.property hv true) e).1

private theorem targetReal {w : Label L b} (hw : w ∈ bitTargets R.val) :
    Realizes (2*finrank (ZMod 2) (P G R)) (targetM G R e hw) :=
  (Realizes.geometricEndpoints (G.targetSlice R.val hw false) (G.targetSlice R.val hw true) e).2

set_option synthInstance.maxSize 2048 in
private theorem middleReal (j : Fin m) {w v : Label L b}
    (hw : w ∈ bitTargets R.val) (hv : v ∈ bitSources R.val) :
    ∃ p : Plan A 1 1, p.calls = 0 ∧ ∀ h, oneRow (((targetReal G R e hw).choose).eval h) *
      oneRow (p.eval h) * oneRow (((sourceReal G R e hv).choose).eval h) =
      rationalLift h ((G.transfer binaryRoot 1 1 j w v).submatrix e e) := by
  have eq := normalizedFree_factor e G.D G.form G.nondegenerate G.symm (H G R) (dim_add G R)
    (G.sourceSlice R.val R.property hv false) (G.sourceSlice R.val R.property hv true)
    (G.targetSlice R.val hw false) (G.targetSlice R.val hw true)
    (G.labelCharts v).pair (G.labelCharts w).pair j
  obtain ⟨mid,⟨p,hp,hm⟩,eq⟩ := eq
  refine ⟨p,Nat.le_zero.mp hp,fun h => ?_⟩
  have hT := (targetReal G R e hw).choose_spec.2
  have hS := (sourceReal G R e hv).choose_spec.2
  apply Implements.product_eq hT hm hS _ h
  exact eq.symm

/-- All three plans are selected before the number of address columns. Source
and target choices use just the incidence and are independent of the query. -/
def freeGeometry (weight : Coefficient) : FreeData A (Label L b) (Fin m) where
  sources := (bitSources R.val).toFinset
  destinations := (bitTargets R.val).toFinset
  weight := weight
  source v := if hv : v ∈ bitSources R.val then (sourceReal G R e hv).choose else identity
  target w := if hw : w ∈ bitTargets R.val then (targetReal G R e hw).choose else identity
  middle j w v := if h : w ∈ bitTargets R.val ∧ v ∈ bitSources R.val then
    (middleReal G R e j h.1 h.2).choose else identity
  middle_free j w v := by
    split
    · rename_i h
      exact (middleReal G R e j h.1 h.2).choose_spec.1
    · rfl

theorem freeGeometry_factors (weight : Coefficient) :
    (freeGeometry G R e weight).Factors
      (fun h j w v => rationalLift h ((G.transfer binaryRoot 1 1 j w v).submatrix e e)) := by
  intro h j w v hv hw
  have hs : v ∈ bitSources R.val := Set.mem_toFinset.mp hv
  have ht : w ∈ bitTargets R.val := Set.mem_toFinset.mp hw
  simpa only [freeGeometry, dite_eq_left hs, dite_eq_left ht, dite_eq_left (And.intro ht hs)] using
    (middleReal G R e j ht hs).choose_spec.2 h

theorem freeGeometry_source_calls (weight : Coefficient) (v : Label L b) :
    ((freeGeometry G R e weight).source v).calls ≤ 2*G.D := by
  have hd := dim_add G R
  simp only [freeGeometry]
  split
  · rename_i hv
    exact (sourceReal G R e hv).choose_spec.1.trans (by omega)
  · exact Nat.zero_le _

theorem freeGeometry_target_calls (weight : Coefficient) (w : Label L b) :
    ((freeGeometry G R e weight).target w).calls ≤ 2*G.D := by
  have hd := dim_add G R
  simp only [freeGeometry]
  split
  · rename_i hw
    exact (targetReal G R e hw).choose_spec.1.trans (by omega)
  · exact Nat.zero_le _

end
end KernelPass.Rect.Binary

end NearSquareRoot
end Computability
end OAI
