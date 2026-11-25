import OAI.LinearAlgebra.SpectralBooks.DoublingTheorem
import OAI.LinearAlgebra.SpectralBooks.PlacementPullback

/-! # Doubling three lists of placements in a spectral space -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

noncomputable section

namespace SiteTensor.BookFactors

open PermutationStretch

variable {K : Type*} [Field K] {B C O : Type} [Fintype B] [Fintype C] [Fintype O]

/-- The raw private tensor with all ambient sites present. -/
abbrev PrivateData.leftRaw (O C : Type) [Fintype O] [Fintype C] (p : PrivateData K B) :=
  Raw.withTrivial O (bookRaw (placeB C p.coeff))

/-- The raw private tensor with all ambient sites present, for the second side. -/
abbrev PrivateData.rightRaw (O B : Type) [Fintype O] [Fintype B] (q : PrivateData K C) :=
  Raw.withTrivial O (bookRaw (placeC B q.coeff))

/-- A binary diagonal on the joint grid with scalar slots at `O`. -/
abbrev jointRaw (K : Type*) [Field K] (B C O : Type) [Fintype B] [Fintype C] [Fintype O] :=
  Raw.withTrivial O (bookRaw (diagAll (K := K) B C (Fin 2)))

variable {X : Type*} [MetricSpace X] (H : SpectralPlacementPrices K X)

private theorem price_eq_if_moved_scalar {I : Type} [Fintype I] (T : Raw.{0} I K)
    {x y : I → X} (h : ∀ i, x i = y i ∨ Fintype.card (T.Leg i) = 1) :
    H.price T x = H.price T y := by
  have hcost (i : I) : dist (x i) (y i) * Real.logb 2 (Fintype.card (T.Leg i)) = 0 := by
    rcases h i with he | he <;> simp [he]
  exact dist_le_zero.mp (by simpa only [hcost, Finset.sum_const_zero] using H.transport T x y)

/-- Realize the three price placements in the cube argument. In the second
placement `y` the sites of `C` all coincide with the center, and in `z` the
sites of `B` do. Auxiliary sites are arbitrary. The bound is valid at every
raw tensor, including the zero tensor. -/
theorem doubling_of_placements [Nonempty B] [Nonempty C]
    (x y z : BookSite B C ⊕ O → X)
    (hyu : y (.inl (.inl ())) = x (.inl (.inl ())))
    (hzu : z (.inl (.inl ())) = x (.inl (.inl ())))
    (hyB : ∀ b : B, y (.inl (.inr (.inl b))) = x (.inl (.inr (.inl b))))
    (hzC : ∀ c : C, z (.inl (.inr (.inr c))) = x (.inl (.inr (.inr c))))
    (hyC : ∀ c : C, y (.inl (.inr (.inr c))) = y (.inl (.inl ())))
    (hzB : ∀ b : B, z (.inl (.inr (.inl b))) = z (.inl (.inl ())))
    (hD : H.price (jointRaw K B C O) x = H.price ((privateDiagonal K B).leftRaw O C) x)
    (hpos : 0 < H.price ((privateDiagonal K B).leftRaw O C) x) (lam : ℝ) (hlam : 0 ≤ lam) :
    let upper (T : Raw.{0} (BookSite B C ⊕ O) K) := lam * H.price T x + H.price T y + H.price T z
    ∃ g : NonzeroProduct.{0} (BookSite B C ⊕ O) K →+ ℝ, IsSpectralPrice unit_le_nonzeroClass g ∧
      (∀ T, classPrice g (ofRaw T) ≤ upper T) ∧
      (∀ p : PrivateData K B, classPrice g (ofRaw (p.leftRaw O C)) = upper (p.leftRaw O C)) ∧
      (∀ q : PrivateData K C, classPrice g (ofRaw (q.rightRaw O B)) = upper (q.rightRaw O B)) ∧
      classPrice g (ofRaw (jointRaw K B C O)) = upper (jointRaw K B C O) := by
  obtain ⟨a, ha, hax⟩ := H.exists_spectralPrice_of_placement x
  obtain ⟨b, hb, hby⟩ := H.exists_spectralPrice_of_placement y
  obtain ⟨c, hc, hcz⟩ := H.exists_spectralPrice_of_placement z
  have leftEval (p : PrivateData K B) : classOfProduct (p.left O C) = ofRaw (p.leftRaw O C) := rfl
  have rightEval (p : PrivateData K C) : classOfProduct (p.right O B) = ofRaw (p.rightRaw O B) := rfl
  have jointEval : classOfProduct (jointDiagonal K B C O) = ofRaw (jointRaw K B C O) := rfl
  have hbc : WireCollapseC b := by
    intro j
    rw [← hby, ← H.group, H.wire]
    change dist (y (.inl (.inl ()))) (y (.inl (.inr (.inr j)))) = 0
    simp [hyC]
  have hcb : WireCollapseB c := by
    intro i
    rw [← hcz, ← H.group, H.wire]
    change dist (z (.inl (.inl ()))) (z (.inl (.inr (.inl i)))) = 0
    simp [hzB]
  have hBag (p : PrivateData K B) : b (p.left O C) = a (p.left O C) := by
    rw [← classPrice_eq b, ← classPrice_eq a, leftEval, ← hby, ← hax]
    apply price_eq_if_moved_scalar
    rintro ((u | (i | j)) | o)
    · cases u; exact Or.inl hyu
    · exact Or.inl (hyB i)
    · exact Or.inr Fintype.card_unit
    · exact Or.inr (Fintype.card_unique : Fintype.card PUnit = 1)
  have hCag (q : PrivateData K C) : c (q.right O B) = a (q.right O B) := by
    rw [← classPrice_eq c, ← classPrice_eq a, rightEval, ← hcz, ← hax]
    apply price_eq_if_moved_scalar
    rintro ((u | (i | j)) | o)
    · cases u; exact Or.inl hzu
    · exact Or.inr Fintype.card_unit
    · exact Or.inl (hzC j)
    · exact Or.inr (Fintype.card_unique : Fintype.card PUnit = 1)
  rw [hax, ← jointEval, classPrice_eq, hax, ← leftEval, classPrice_eq] at hD
  rw [hax, ← leftEval, classPrice_eq] at hpos
  obtain ⟨g, hg, hle, heqB, heqC, heqAll⟩ :=
    doubling a b c ha hb hc hbc hBag hcb hCag hD hpos lam hlam
  let upper (T : Raw.{0} (BookSite B C ⊕ O) K) := lam * H.price T x + H.price T y + H.price T z
  have hprice (T : Raw.{0} (BookSite B C ⊕ O) K) (t : NonzeroProduct _ K)
      (ht : classOfProduct t = ofRaw T) : (lam • a + b + c) t = upper T := by
    simp only [upper, hax, hby, hcz, ← ht, classPrice_eq]
    rfl
  refine ⟨g, hg, ?_, fun p => ?_, fun q => ?_, ?_⟩
  · intro T
    by_cases hzero : T.coeff = 0
    · rw [(ofRaw_eq_zero_iff T).mpr hzero]
      simp [classPrice, H.zero_tensor T hzero]
    · let t : NonzeroProduct _ K := Additive.ofMul ⟨ofRaw T, fun he => hzero ((ofRaw_eq_zero_iff T).mp he)⟩
      exact (classPrice_eq g t).le.trans ((hle t).trans_eq (hprice T t rfl))
  · exact (classPrice_eq g _).trans ((heqB p).trans (hprice _ _ (leftEval p)))
  · exact (classPrice_eq g _).trans ((heqC q).trans (hprice _ _ (rightEval q)))
  · exact (classPrice_eq g _).trans (heqAll.trans (hprice _ _ jointEval))

end SiteTensor.BookFactors

end

end SpectralBooks
end LinearAlgebra
end OAI
