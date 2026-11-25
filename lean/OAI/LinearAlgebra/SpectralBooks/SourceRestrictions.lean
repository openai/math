import OAI.LinearAlgebra.SpectralBooks.Interpolation

/-! # Local coefficient maps for the common-label restriction

The diagonal on the original sites supplies `h`. Of these sites, `k + 1`
also receive a leg of an auxiliary diagonal, and `m` sites carry only `h`.
The final leg of the auxiliary diagonal supplies the new site with `g`.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

/-- One coordinate in the output format for the common-label construction. -/
structure IncrementCoordinate (q k m : ℕ) where
  h : Fin q
  a : Fin q
  g : Fin q
  hOther : Fin k → Fin q
  v : Fin k → Fin q
  hExtra : Fin m → Fin q

/-- Every copy of the original diagonal label agrees with the first site's copy. -/
def IncrementCoordinate.shared {q k m : ℕ} (c : IncrementCoordinate q k m) : Prop :=
  (∀ j, c.hOther j = c.h) ∧ (∀ j, c.hExtra j = c.h)

instance {q k m : ℕ} (c : IncrementCoordinate q k m) : Decidable c.shared := by
  unfold IncrementCoordinate.shared
  infer_instance

/-- Tensors obtained by choosing local coefficient maps on the legs of the
auxiliary diagonal and retaining the original common label at every old site. -/
def commonLabelRestrictions (F : Type*) [Field F] (q k m L : ℕ) :
    Set (IncrementCoordinate q k m → F) :=
  {T | ∃ (U : Fin q → Fin q → Fin L → F) (V : Fin k → Fin q → Fin q → Fin L → F)
      (Z : Fin q → Fin L → F), ∀ c, T c =
        if c.shared then ∑ l, U c.h c.a l * (∏ j, V j (c.hOther j) (c.v j) l) * Z c.g l
        else 0}

/-- Scaling each output basis by its local factors amounts to scaling the
rows of the corresponding local coefficient maps. -/
theorem localScaling_preserves_commonLabelRestrictions {F : Type*} [Field F] (q k m L : ℕ)
    (u : Fin q → Fin q → F) (b : Fin k → Fin q → Fin q → F) (z : Fin q → F) :
    Set.MapsTo (fun T c ↦ (u c.h c.a * (∏ j, b j (c.hOther j) (c.v j)) * z c.g) * T c)
      (commonLabelRestrictions F q k m L) (commonLabelRestrictions F q k m L) := by
  rintro T ⟨U, V, Z, hT⟩
  refine ⟨fun h a l ↦ u h a * U h a l, fun j h v l ↦ b j h v * V j h v l,
    fun g l ↦ z g * Z g l, fun c ↦ ?_⟩
  simp only [hT c]
  by_cases hc : c.shared
  · simp only [hc, ite_true, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro l _
    rw [Finset.prod_mul_distrib]
    ac_rfl
  · simp [hc]

/-- The interpolation construction is a restriction by local maps at all
sites, with the same one of `2 * (k + 1) * (q - 1) + 1` evaluation labels. -/
theorem commonLabelEquation_mem_restrictions (F : Type*) [Field F] [Infinite F] (q k m : ℕ) :
    (fun c : IncrementCoordinate q k m ↦
      if c.shared ∧ (c.g.val : ℤ) = c.h.val + (∑ j, ((c.v j).val : ℤ)) - (k : ℤ) * c.a.val
      then 1 else 0) ∈ commonLabelRestrictions F q k m (2 * (k + 1) * (q - 1) + 1) := by
  obtain ⟨x, w, h⟩ := exists_equation_restriction F q k
  refine ⟨fun h a l ↦ w l * x l ^ (q - 1 - h.val + k * a.val),
    fun _ _ v l ↦ x l ^ (q - 1 - v.val), fun g l ↦ x l ^ g.val, fun c ↦ ?_⟩
  by_cases hc : c.shared
  · simpa only [hc, true_and, ite_true] using (h c.h c.g c.a c.v).symm
  · simp [hc]

end SpectralBooks
end LinearAlgebra
end OAI
