import OAI.Computability.NearSquareRoot.KernelEndpointCross
import OAI.Computability.NearSquareRoot.KernelPassFactors
import OAI.LinearAlgebra.FiniteFourier.PrimeRectangleEndpointFactor

/-! # The normalized free-rectangle bridge

After putting one factor of two from each pair of Walsh axes in the source
and destination transforms, the bridge is a binary linear permutation and a
sign. Both are uniform stream programs without child transforms. -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace KernelPass
noncomputable section

open OAI.LinearAlgebra.FiniteFourier KernelEndpointCross KernelNormalization Module Matrix
open scoped Classical

variable {A : ℕ}

theorem realizes_bridge
    {X H P S T U : Type*}
    [AddCommGroup X] [AddCommGroup H] [AddCommGroup P] [AddCommGroup S] [AddCommGroup T]
    [AddCommGroup U] [Module (ZMod 2) X]
    (e : Bits A ≃ₗ[ZMod 2] X) (xv : H × S ≃+ X) (zw : P × T ≃+ X)
    (s : S ≃+ P × U) (t : T ≃+ H × U) (z : P × T → ZMod 2) :
    Realizes 0 ((Matrix.reindex zw.toEquiv xv.toEquiv
      (endpointBridge s.toEquiv t.toEquiv (character ∘ z))).submatrix e e) := by
  let k := e.toAddEquiv.trans (zw.symm.trans
    ((bridgeAdd s t).trans (xv.trans e.symm.toAddEquiv)))
  let g := linear (ℓ := 2) k
  let q (o : Bits A) := z (zw.symm (e o))
  have h := (Realizes.sign q).mul (Realizes.permutation g.symm)
  convert h using 1
  ext o i
  change (if endpointBridgeEquiv s.toEquiv t.toEquiv (zw.symm (e o)) = xv.symm (e i)
    then character (q o) else 0) = _
  rw [Matrix.diagonal_mul]
  change _ = character (q o) * (if o = g.symm i then 1 else 0)
  have he : endpointBridgeEquiv s.toEquiv t.toEquiv (zw.symm (e o)) = xv.symm (e i) ↔ o = g.symm i := by
    rw [g.eq_symm_apply]
    change _ ↔ e.symm (xv (endpointBridgeEquiv s.toEquiv t.toEquiv (zw.symm (e o)))) = i
    rw [LinearEquiv.symm_apply_eq, AddEquiv.eq_symm_apply]
  by_cases h : o = g.symm i
  · rw [ite_eq_left (he.mpr h), ite_eq_left h, mul_one]
  · rw [ite_eq_right (fun t => h (he.mp t)), ite_eq_right h, mul_zero]

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxSize 2048 in
theorem normalizedFree_factor {E U J : Type} [AddCommGroup E] [Module (ZMod 2) E]
    [FiniteDimensional (ZMod 2) E] [Fintype U] [Fintype J]
    (e : Bits A ≃ₗ[ZMod 2] PrimeSpectrumDigits (Fin 1 × (J ⊕ U)) 2)
    (D : ℕ) (B : LinearMap.BilinForm (ZMod 2) E) (hB : B.Nondegenerate) (hsym : B.IsSymm)
    (H : Submodule (ZMod 2) E) (hd : finrank (ZMod 2) (H.orthogonalBilin B) + finrank (ZMod 2) H = D)
    {v₁ v₂ w₁ w₂ : E ≃ₗ[ZMod 2] ZMod 2 × (U → ZMod 2)}
    (X₁ : AuxiliarySlice v₁ H) (X₂ : AuxiliarySlice v₂ H)
    (Z₁ : AuxiliarySlice w₁ (H.orthogonalBilin B)) (Z₂ : AuxiliarySlice w₂ (H.orthogonalBilin B))
    [Fintype X₁.C] [Fintype X₂.C] [Fintype Z₁.C] [Fintype Z₂.C]
    (hv : ∀ x y, B x y = (v₁ x).1 * (v₂ y).1 + ∑ u, (v₁ x).2 u * (v₂ y).2 u)
    (hw : ∀ x y, B x y = (w₁ x).1 * (w₂ y).1 + ∑ u, (w₁ x).2 u * (w₂ y).2 u)
    (j : J) :
    ∃ mid : Local A, Realizes 0 mid ∧
      ((primeCommonKernel (C := Fin 1) binaryRoot B 1 D).submatrix
        (primeCommonQueryChart j (primeCommonLabelMap w₁) (primeCommonLabelMap w₂))
        (primeCommonQueryChart j (primeCommonLabelMap v₁) (primeCommonLabelMap v₂))).submatrix e e =
      (((2:ℂ)⁻¹ ^ finrank (ZMod 2) (H.orthogonalBilin B)) •
        primeTargetEndpoint (f := 1) (J := J) binaryRoot 1 Z₁ Z₂).submatrix e e *
      mid * (((2:ℂ)⁻¹ ^ finrank (ZMod 2) H) •
        primeSourceEndpoint (f := 1) (J := J) binaryRoot 1 X₁ X₂).submatrix e e := by
  let P := H.orthogonalBilin B
  let xv := endpointLabelAddChart (C := Fin 1) (J := J) X₁ X₂
  let zw := endpointLabelAddChart (C := Fin 1) (J := J) Z₁ Z₂
  let cv := primeCommonQueryChart (C := Fin 1) j (primeCommonLabelMap v₁) (primeCommonLabelMap v₂)
  let cw := primeCommonQueryChart (C := Fin 1) j (primeCommonLabelMap w₁) (primeCommonLabelMap w₂)
  let X := cv ∘ xv
  let Z := cw ∘ zw
  let bH := (finBasis (ZMod 2) H).equivFun
  let bP := (finBasis (ZMod 2) P).equivFun
  obtain ⟨s,t,r,hs,ht,hc⟩ := exists_endpointLabelCross_add (f := 1) B hB hsym H X₁ X₂ Z₁ Z₂ j
  let dot {n : ℕ} (x y : PrimeCommonPair 2 1 n) := ∑ c, ∑ k, (x.1 c k*y.1 c k + x.2 c k*y.2 c k)
  have hf := primeCommonKernel_free_factor binaryRoot B 1 D X Z s.toEquiv t.toEquiv
    (fun q h => dot h q) (fun p μ => dot μ p) r
    (endpointLabelCoordinateAux X₁ X₂ bH) (endpointLabelCoordinateAux Z₁ Z₂ bP)
    (fun v => endpointLabelDistExponent j v.1) (fun v => endpointLabelDistExponent j v.1)
    (fun i => (hs i.2).symm) (fun o => (ht o.2).symm)
    (endpointLabelCoordinateChart_self X₁ X₂ bH j B hv)
    (endpointLabelCoordinateChart_self Z₁ Z₂ bP j B hw) hc
  let phase := fun (o : PrimeCommonPair 2 1 (finrank (ZMod 2) P) ×
      EndpointLabelResidualIndex (Fin 1) J (ZMod 2) Z₁.C Z₂.C) =>
    let u := s.symm (o.1, (t o.2).2)
    (↑((1 : (ZMod 2)ˣ)⁻¹) : ZMod 2) * (r u o.2 - endpointLabelDistExponent j u.1 - endpointLabelDistExponent j o.2.1)
  let M := Matrix.reindex zw.toEquiv xv.toEquiv (endpointBridge s.toEquiv t.toEquiv (character ∘ phase))
  refine ⟨M.submatrix e e, realizes_bridge e xv zw s t phase, ?_⟩
  let T := primeTargetEndpoint (f := 1) (J := J) binaryRoot 1 Z₁ Z₂
  let S := primeSourceEndpoint (f := 1) (J := J) binaryRoot 1 X₁ X₂
  let n := (2:ℂ)⁻¹ ^ D
  have he : (primeCommonKernel binaryRoot B 1 D).submatrix cw cv = T * (n • M) * S := by
    let mid := endpointBridge s.toEquiv t.toEquiv (fun o => n * character (phase o))
    have hM : n • M = Matrix.reindex zw.toEquiv xv.toEquiv mid := by
      ext o i
      simp only [M, mid, Matrix.smul_apply, smul_eq_mul, Matrix.reindex_apply,
        Matrix.submatrix_apply, endpointBridge, Function.comp_apply, mul_ite, mul_zero]
    rw [hM]
    apply endpointFactor_reindex xv.toEquiv zw.toEquiv
    extract_lets b F G w src dst at hf
    convert! hf using 1
    congr! 3
    · funext o
      simp only [w, Fintype.card_fin, one_mul, n, character, phase, b, invOf_eq_inv]
      rfl
    · ext o i
      by_cases hi : o = i
      · subst i; simp only [Matrix.diagonal_apply_eq]; rfl
      · simp [hi]
  change ((primeCommonKernel binaryRoot B 1 D).submatrix cw cv).submatrix e.toEquiv e.toEquiv =
    ((2:ℂ)⁻¹^finrank (ZMod 2) P • T).submatrix e.toEquiv e.toEquiv * M.submatrix e.toEquiv e.toEquiv *
    ((2:ℂ)⁻¹^finrank (ZMod 2) H • S).submatrix e.toEquiv e.toEquiv
  rw [Matrix.submatrix_mul_equiv _ _ _ e.toEquiv _, Matrix.submatrix_mul_equiv _ _ _ e.toEquiv _, he]
  simp only [Matrix.mul_smul, Matrix.smul_mul, smul_smul, n]
  rw [mul_comm ((2 : ℂ)⁻¹ ^ _), ← pow_add, hd]

end
end KernelPass

end NearSquareRoot
end Computability
end OAI
