import OAI.LinearAlgebra.SpectralBooks.SiteTensor.StretchClassSum
import OAI.LinearAlgebra.SpectralBooks.StretchEstimate
import OAI.LinearAlgebra.SpectralBooks.StretchClassPrice
import OAI.LinearAlgebra.SpectralBooks.PermutationStretch.StretchTargetClass
import OAI.LinearAlgebra.SpectralBooks.DoublingSelection

/-! # The permutation-stretch estimate for spectral prices over a field

All prices here are scaled logarithms of normalized spectral points on the
same tensor semiring, including its auxiliary sites. The ordinary summands may
start in an arbitrary representative of the target restriction class.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

open MatrixMultiplication.Foundation
open scoped BigOperators Classical

namespace SiteTensor
open BookFactors PermutationStretch SitePriceEval

variable {K : Type*} [Field K] {B C O : Type} [Fintype B] [Fintype C] [Fintype O]

/-- Lemma `stretch` for any shared diagonal dimension `R > 0`, in an arbitrary
representative of the nonzero class of the diagonal times the private tensors. -/
theorem ClassOrdinarySum.stretch_in_format {a b c : NonzeroProduct.{0} (BookSite B C ⊕ O) K →+ ℝ}
    (ha : IsSpectralPrice unit_le_nonzeroClass a) (hb : IsSpectralPrice unit_le_nonzeroClass b)
    (hc : IsSpectralPrice unit_le_nonzeroClass c) {lam : ℝ} (hlam : 0 ≤ lam)
    (hbc : (ofSupportedClassPrice b hb).MonoGroupedC) (hcb : (ofSupportedClassPrice c hc).MonoGroupedB)
    (hagB : ∀ P : PrivateData K B, b (P.left O C) = a (P.left O C))
    (hagC : ∀ Q : PrivateData K C, c (Q.right O B) = a (Q.right O B))
    (hD : a (jointDiagonal K B C O) = a ((privateDiagonal K B).left O C))
    {R L : ℕ} (hR : 0 < R) (P : PrivateData K B) (Q : PrivateData K C) (Z : Fin L → _)
    {A : NonzeroProduct.{0} (BookSite B C ⊕ O) K}
    (hformat : ofRaw (Raw.withTrivial O (bookRaw (sharedTarget (R := Fin R) P.coeff Q.coeff))) = classOfProduct A)
    (hs : ClassOrdinarySum A L Z) :
    ∃ l, (lam • a + b + c) A ≤ (lam • a + b + c) (Z l) +
      ((lam + 1) * a ((privateDiagonal K B).left O C) + a ((privateDiagonal K C).right O B)) * Real.logb 2 L := by
  let ap := ofSupportedClassPrice a ha
  let bp := ofSupportedClassPrice b hb
  let cp := ofSupportedClassPrice c hc
  let S := sharedTarget (R := Fin R) P.coeff Q.coeff
  let H := lam • a + b + c
  have hB : bp.AgreesB ap := by
    intro U X _ _ T hn
    let p : PrivateData K B := ⟨U, X, inferInstance, inferInstance, T, hn⟩
    exact (ofSupportedClassPrice_agrees b hb _ (p.left O C) rfl).trans
      ((hagB p).trans (ofSupportedClassPrice_agrees a ha _ (p.left O C) rfl).symm)
  have hC : cp.AgreesC ap := by
    intro U Y _ _ T hn
    let q : PrivateData K C := ⟨U, Y, inferInstance, inferInstance, T, hn⟩
    exact (ofSupportedClassPrice_agrees c hc _ (q.right O B) rfl).trans
      ((hagC q).trans (ofSupportedClassPrice_agrees a ha _ (q.right O B) rfl).symm)
  have hdAll : ap.value (diagAll (K := K) B C (Fin 2)) = a (jointDiagonal K B C O) :=
    ofSupportedClassPrice_agrees a ha _ _ rfl
  have hdB : ap.value (diagB (K := K) B C (Fin 2)) = a ((privateDiagonal K B).left O C) :=
    ofSupportedClassPrice_agrees a ha _ _ rfl
  have hdC : ap.value (diagC (K := K) B C (Fin 2)) = a ((privateDiagonal K C).right O B) :=
    ofSupportedClassPrice_agrees a ha _ _ rfl
  apply hs.exists_selected_of_book_format S hformat H
    (fun {x y} hxy => add_le_add (add_le_add (mul_le_mul_of_nonneg_left (ha.mono hxy) hlam) (hb.mono hxy)) (hc.mono hxy))
    (fun T => lam * ap.value T + (bp.value T + cp.value T))
  · intro T t ht
    change lam * (ofSupportedClassPrice a ha).value T +
      ((ofSupportedClassPrice b hb).value T + (ofSupportedClassPrice c hc).value T) = lam * a t + b t + c t
    rw [ofSupportedClassPrice_agrees a ha T t ht, ofSupportedClassPrice_agrees b hb T t ht,
      ofSupportedClassPrice_agrees c hc T t ht, add_assoc]
  · exact add_nonneg (mul_nonneg (by positivity) (ha.nonneg _)) (ha.nonneg _)
  · intro N hN T hT he
    have hh := permutationStretch_of_collapses hR hN hlam ap bp cp
      (ofSupportedClassPrice_binaryProductAdditive a ha) (ofSupportedClassPrice_binaryProductAdditive b hb)
      (ofSupportedClassPrice_binaryProductAdditive c hc) (ofSupportedClassPrice_ordinarySumBound_diagAll a ha)
      (ofSupportedClassPrice_ordinarySumBound_diagAll c hc) hbc hcb hB hC (hdAll.trans (hD.trans hdB.symm))
      P.coeff Q.coeff P.coeff_ne Q.coeff_ne T hT he
    obtain ⟨i, hi⟩ := hh
    exact ⟨i, by simpa only [hdAll, hD, hdC] using hi⟩

/-- Lemma `stretch`, on actual tensor classes, for a power of the binary joint
diagonal and two arbitrary nonzero private tensors. Collapse is expressed by
monotonicity under linear maps at the grouped site. -/
theorem ClassOrdinarySum.stretch {a b c : NonzeroProduct.{0} (BookSite B C ⊕ O) K →+ ℝ}
    (ha : IsSpectralPrice unit_le_nonzeroClass a) (hb : IsSpectralPrice unit_le_nonzeroClass b)
    (hc : IsSpectralPrice unit_le_nonzeroClass c) {lam : ℝ} (hlam : 0 ≤ lam)
    (hbc : (ofSupportedClassPrice b hb).MonoGroupedC) (hcb : (ofSupportedClassPrice c hc).MonoGroupedB)
    (hagB : ∀ P : PrivateData K B, b (P.left O C) = a (P.left O C))
    (hagC : ∀ Q : PrivateData K C, c (Q.right O B) = a (Q.right O B))
    (hD : a (jointDiagonal K B C O) = a ((privateDiagonal K B).left O C))
    {k L : ℕ} (P : PrivateData K B) (Q : PrivateData K C) (Z : Fin L → _)
    (hs : ClassOrdinarySum (k • jointDiagonal K B C O + P.left O C + Q.right O B) L Z) :
    let A := k • jointDiagonal K B C O + P.left O C + Q.right O B
    ∃ l, (lam • a + b + c) A ≤ (lam • a + b + c) (Z l) +
      ((lam + 1) * a ((privateDiagonal K B).left O C) + a ((privateDiagonal K C).right O B)) * Real.logb 2 L := by
  exact ClassOrdinarySum.stretch_in_format ha hb hc hlam hbc hcb hagB hagC hD
    (R := 2^k) (by positivity) P Q Z (congrArg classOfProduct (bookProduct_sharedTarget (O := O) k P Q)) hs

end SiteTensor

end SpectralBooks
end LinearAlgebra
end OAI
