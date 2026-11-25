import OAI.LinearAlgebra.SpectralBooks.CopyLabelTensor
import OAI.LinearAlgebra.SpectralBooks.DiagonalProduct

/-! # Factoring the output of label copying

The free equal pair of labels forms a wire. The third label augments the old
tensor at its receiving site. Separating the marked factors in each fiber
gives this factorization even when several marked sites agree.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

namespace SiteTensor.Raw

noncomputable section
open scoped Classical

variable {I : Type} [Fintype I] {K : Type*} [CommSemiring K]

omit [Fintype I] in
/-- Appending a uniquely prescribed label preserves nonzero coefficients. -/
theorem appendLabel_nonzero_iff (T : Raw.{0} I K) (s : I) (D : Type) [Fintype D]
    (label : (∀ i, T.Leg i) → D) :
    (T.appendLabel s D label).coeff ≠ 0 ↔ T.coeff ≠ 0 := by
  apply not_congr
  constructor
  · intro h
    funext x
    let y (i : I) : (T.appendLabel s D label).Leg i := (x i, fun _ => label x)
    simpa [y, appendLabel] using congrFun h y
  · intro h
    funext y
    simp [appendLabel, h]

private def copyLegEquiv {D : Type} (σ : Fin 3 → I) (i : I) :
    ({t : Fin 3 // σ t = i} → D) ≃
      ({_u : Unit // σ 2 = i} → D) × ({r : Fin 2 // ![σ 0, σ 1] r = i} → D) where
  toFun x := (fun u => x ⟨2, u.property⟩, fun r =>
    x ⟨r.val.castSucc, (show σ r.val.castSucc = ![σ 0, σ 1] r.val by
      obtain ⟨k,hk⟩ := r
      fin_cases k <;> rfl).trans r.property⟩)
  invFun y t := by
    obtain ⟨k,hk⟩ := t
    by_cases h₀ : k = 0
    · exact y.2 ⟨0, h₀ ▸ hk⟩
    by_cases h₁ : k = 1
    · exact y.2 ⟨1, h₁ ▸ hk⟩
    have h₂ : k = 2 := by omega
    exact y.1 ⟨(), h₂ ▸ hk⟩
  left_inv x := by
    funext ⟨k,hk⟩
    fin_cases k <;> rfl
  right_inv y := by
    apply Prod.ext
    · funext u
      rfl
    · funext ⟨k,hk⟩
      fin_cases k <;> rfl

/-- The copying output is the tensor with its label appended, tensored with
the independent wire between the first two marked slots. -/
theorem copyOutput_equivalent (T : Raw.{0} I K) (σ : Fin 3 → I) {q : ℕ}
    (hA : T.Leg (σ 0) → Fin q) :
    (T.copyOutput σ hA).Equivalent
      ((T.appendLabel (σ 2) (Fin q) (fun t => hA (t (σ 0)))).mul
        ((diagonal (Fin 2) K (Fin q)).group ![σ 0, σ 1])) := by
  let e (i : I) := ((Equiv.refl (T.Leg i)).prodCongr (copyLegEquiv (D := Fin q) σ i)).trans
    (Equiv.prodAssoc _ _ _).symm
  apply reindex_equivalent e
  intro x
  let z (r : Fin 2) : Fin q := (e (![σ 0, σ 1] r) (x _)).2 ⟨r, rfl⟩
  have hd : (diagonal (Fin 2) K (Fin q)).coeff z = if z 0 = z 1 then 1 else 0 := by
    rw [diagonal_coeff_at (1 : Fin 2)]
    simp [Fin.forall_fin_two]
  change _ = _ * (diagonal (Fin 2) K (Fin q)).coeff z
  rw [hd]
  have z₀ : z 0 = (x (σ 0)).2 ⟨0,rfl⟩ := rfl
  have z₁ : z 1 = (x (σ 1)).2 ⟨1,rfl⟩ := rfl
  rw [z₀,z₁]
  change T.coeff (fun i => (x i).1) *
    (if (x (σ 0)).2 ⟨0,rfl⟩ = (x (σ 1)).2 ⟨1,rfl⟩ ∧
      (x (σ 2)).2 ⟨2,rfl⟩ = hA (x (σ 0)).1 then 1 else 0) =
    @ite K ((x (σ 2)).2 ⟨2,rfl⟩ = hA (x (σ 0)).1) (Classical.propDecidable _)
      (T.coeff (fun i => (x i).1)) 0 *
      (if (x (σ 0)).2 ⟨0,rfl⟩ = (x (σ 1)).2 ⟨1,rfl⟩ then 1 else 0)
  split_ifs <;> simp_all

end
end SiteTensor.Raw

end SpectralBooks
end LinearAlgebra
end OAI
