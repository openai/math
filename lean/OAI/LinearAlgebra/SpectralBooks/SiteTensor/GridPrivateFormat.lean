import OAI.LinearAlgebra.SpectralBooks.PrivateProducts

/-! # Recognizing the private tensors in a doubled-grid selection

When a nonzero coefficient tensor has subsingleton legs outside a private
page, those legs are one-dimensional. Reading its coefficients on the
remaining sites recovers a private tensor with exactly the same class.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

namespace SiteTensor.BookFactors

open PermutationStretch

variable {B C O : Type} [Fintype B] [Fintype C] [Fintype O] {K : Type*} [Field K]

private def equivSingletonLeg {A D : Type} [Unique A] (d : D) (h : Subsingleton D) : A ≃ D :=
  ⟨fun _ ↦ d, fun _ ↦ default, fun _ ↦ Subsingleton.elim _ _, fun _ ↦ h.elim _ _⟩

/-- A nonzero raw tensor trivial on the right page and auxiliary sites is a left private class. -/
theorem exists_privateData_left_of_subsingleton (T : Raw.{0} (BookSite B C ⊕ O) K)
    (hT : T.coeff ≠ 0) (hC : ∀ c, Subsingleton (T.Leg (.inl (.inr (.inr c)))))
    (hO : ∀ o, Subsingleton (T.Leg (.inr o))) :
    ∃ P : PrivateData K B, classOfProduct (P.left O C) = ofRaw T := by
  classical
  obtain ⟨a, ha⟩ : ∃ a, T.coeff a ≠ 0 := by
    by_contra! h
    exact hT (funext h)
  let extend (u : T.Leg (.inl (.inl ()))) (x : ∀ b : B, T.Leg (.inl (.inr (.inl b)))) :
      ∀ i, T.Leg i
    | .inl (.inl ()) => u
    | .inl (.inr (.inl b)) => x b
    | .inl (.inr (.inr c)) => a (.inl (.inr (.inr c)))
    | .inr o => a (.inr o)
  let P : PrivateData K B := {
    Center := T.Leg (.inl (.inl ()))
    Leg := fun b ↦ T.Leg (.inl (.inr (.inl b)))
    finiteCenter := inferInstance
    finiteLeg := fun _ ↦ inferInstance
    coeff := fun u x ↦ T.coeff (extend u x)
    coeff_ne := by
      intro hz
      have he : extend (a (.inl (.inl ()))) (fun b ↦ a (.inl (.inr (.inl b)))) = a := by
        funext i
        rcases i with ((⟨⟩ | (_ | _)) | _) <;> rfl
      apply ha
      rw [← he]
      exact congrFun (congrFun hz _) _ }
  refine ⟨P, ofRaw_eq_iff.mpr ?_⟩
  let R := Raw.withTrivial O (bookRaw (placeB C P.coeff))
  let e (i : BookSite B C ⊕ O) : R.Leg i ≃ T.Leg i := by
    rcases i with ((⟨⟩ | (b | c)) | o)
    · exact Equiv.refl _
    · exact Equiv.refl _
    · exact equivSingletonLeg (A := Unit) (a _) (hC c)
    · exact equivSingletonLeg (A := PUnit) (a _) (hO o)
  apply Raw.reindex_equivalent e
  intro y
  apply congrArg T.coeff
  funext i
  rcases i with ((⟨⟩ | (_ | _)) | _) <;> rfl

/-- A nonzero raw tensor trivial on the left page and auxiliary sites is a right private class. -/
theorem exists_privateData_right_of_subsingleton (T : Raw.{0} (BookSite B C ⊕ O) K)
    (hT : T.coeff ≠ 0) (hB : ∀ b, Subsingleton (T.Leg (.inl (.inr (.inl b)))))
    (hO : ∀ o, Subsingleton (T.Leg (.inr o))) :
    ∃ P : PrivateData K C, classOfProduct (P.right O B) = ofRaw T := by
  classical
  obtain ⟨a, ha⟩ : ∃ a, T.coeff a ≠ 0 := by
    by_contra! h
    exact hT (funext h)
  let extend (u : T.Leg (.inl (.inl ()))) (x : ∀ c : C, T.Leg (.inl (.inr (.inr c)))) :
      ∀ i, T.Leg i
    | .inl (.inl ()) => u
    | .inl (.inr (.inl b)) => a (.inl (.inr (.inl b)))
    | .inl (.inr (.inr c)) => x c
    | .inr o => a (.inr o)
  let P : PrivateData K C := {
    Center := T.Leg (.inl (.inl ()))
    Leg := fun c ↦ T.Leg (.inl (.inr (.inr c)))
    finiteCenter := inferInstance
    finiteLeg := fun _ ↦ inferInstance
    coeff := fun u x ↦ T.coeff (extend u x)
    coeff_ne := by
      intro hz
      have he : extend (a (.inl (.inl ()))) (fun c ↦ a (.inl (.inr (.inr c)))) = a := by
        funext i
        rcases i with ((⟨⟩ | (_ | _)) | _) <;> rfl
      apply ha
      rw [← he]
      exact congrFun (congrFun hz _) _ }
  refine ⟨P, ofRaw_eq_iff.mpr ?_⟩
  let R := Raw.withTrivial O (bookRaw (placeC B P.coeff))
  let e (i : BookSite B C ⊕ O) : R.Leg i ≃ T.Leg i := by
    rcases i with ((⟨⟩ | (b | c)) | o)
    · exact Equiv.refl _
    · exact equivSingletonLeg (A := Unit) (a _) (hB b)
    · exact Equiv.refl _
    · exact equivSingletonLeg (A := PUnit) (a _) (hO o)
  apply Raw.reindex_equivalent e
  intro y
  apply congrArg T.coeff
  funext i
  rcases i with ((⟨⟩ | (_ | _)) | _) <;> rfl

end SiteTensor.BookFactors

end SpectralBooks
end LinearAlgebra
end OAI
