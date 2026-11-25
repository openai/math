import OAI.LinearAlgebra.SpectralBooks.RawPriceTransport
import OAI.LinearAlgebra.SpectralBooks.SiteTensor.Push

/-! # Wire distance is bounded by the price of a diagonal

A grouped diagonal distributes one common basis label to every recipient.
Projecting, or copying, the local basis indices restricts this tensor to any
list of recipients selected from the original placement.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

noncomputable section

namespace SiteTensor

open scoped Classical

variable {H I J : Type} {K : Type*} [Fintype H] [Fintype I] [Fintype J]

omit [Fintype J] in
private theorem grouped_diagonal_coeff [CommSemiring K] (σ : I → J) (D : Type) [Fintype D] :
    ((Raw.diagonal I K D).group σ).coeff =
      pushCoeff (fun d (j : J) (_ : {i // σ i = j}) ↦ d) (fun _ : D ↦ (1 : K)) := by
  funext x
  apply Finset.sum_congr rfl
  intro d _
  change (if (fun i ↦ x (σ i) ⟨i, rfl⟩) = (fun _ ↦ d) then 1 else 0) =
    (if (fun _ _ ↦ d) = x then 1 else 0)
  congr 1
  apply propext
  constructor
  · intro hx
    funext j p
    obtain ⟨i, rfl⟩ := p
    exact (congrFun hx i).symm
  · intro hx
    funext i
    exact (congrFun (congrFun hx (σ i)) ⟨i, rfl⟩).symm

/-- A list of recipients, with repetitions allowed, receives a common label
by selecting basis indices independently at each occupied site. -/
theorem Raw.group_diagonal_restricts_of_comp [CommSemiring K] (σ : I → J) (f : H → I)
    (D : Type) [Fintype D] :
    ((diagonal H K D).group (σ ∘ f)).Restricts ((diagonal I K D).group σ) := by
  let crop (j : J) (a : {i // σ i = j} → D) (p : {h // (σ ∘ f) h = j}) : D :=
    a ⟨f p.val, p.property⟩
  have h := pushCoeff_restricts crop ((diagonal I K D).group σ).coeff
  change Crossing.IsRestriction _ _
  have he : ((diagonal H K D).group (σ ∘ f)).coeff =
      pushCoeff (fun x j ↦ crop j (x j)) ((diagonal I K D).group σ).coeff := by
    rw [grouped_diagonal_coeff, grouped_diagonal_coeff]
    erw [pushCoeff_comp]
    rfl
  rw [he]
  exact h

/-- The binary diagonal of an entire placement dominates the wire between
any two of its sites. -/
theorem rawWireDistance_le_group_diagonal [Field K] [Nonempty J]
    (φ : normalizedSpectrum ((· ≤ ·) : TensorClass.{0} J K → _ → Prop))
    {c : ℝ} (hc : 0 ≤ c) (x : I → J) (i j : I) :
    rawWireDistance φ c (x i) (x j) ≤ rawLogPrice φ c ((Raw.diagonal I K (Fin 2)).group x) := by
  have hf : x ∘ ![i, j] = ![x i, x j] := by funext k; fin_cases k <;> rfl
  simpa only [rawWireDistance, hf] using
    rawLogPrice_mono φ hc (Raw.group_diagonal_restricts_of_comp x ![i, j] (Fin 2))

end SiteTensor

end

end SpectralBooks
end LinearAlgebra
end OAI
