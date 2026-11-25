import OAI.LinearAlgebra.SpectralBooks.TensorGroupRaw
import OAI.LinearAlgebra.SpectralBooks.TensorGroupAdd
import OAI.LinearAlgebra.SpectralBooks.SiteTensor.Diagonal
import OAI.LinearAlgebra.SpectralBooks.SiteTensor.DiagonalEmbedding
import OAI.LinearAlgebra.SpectralBooks.RawLogPrice
import OAI.LinearAlgebra.SpectralBooks.NatSpectralExponent

/-! # Grouping placed tensors on restriction classes

Even with unoccupied sites, grouping commutes with tensor products and is
monotone for restriction. Applied to a diagonal of arbitrary label dimension,
any normalized spectral point therefore evaluates a power of that dimension.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

namespace SiteTensor

noncomputable section
open scoped NNReal

universe v u u' w
variable {I : Type u} {J : Type u'} {K : Type w} [Fintype I] [Fintype J] [CommSemiring K]

/-- Group local indices over the fibers of a placement at the level of tensor classes. -/
def groupClass (σ : I → J) : TensorClass.{v} I K → TensorClass.{max u v} J K :=
  Quotient.map (fun X => X.group σ) fun _ _ h =>
    ⟨Raw.group_restricts σ h.1, Raw.group_restricts σ h.2⟩

@[simp] theorem groupClass_ofRaw (σ : I → J) (X : Raw.{v} I K) :
    groupClass σ (ofRaw X) = ofRaw (X.group σ) := rfl

theorem groupClass_mono (σ : I → J) : Monotone (groupClass (K := K) σ) :=
  fun X Y => Quotient.inductionOn₂ X Y fun _ _ => Raw.group_restricts σ

/-- Arbitrary (possibly colliding) placements preserve products and the scalar unit. -/
def groupMulHom [Nonempty I] [Nonempty J] (σ : I → J) :
    TensorClass.{v} I K →* TensorClass.{max u v} J K where
  toFun := groupClass σ
  map_one' := ofRaw_eq_iff.mpr (Raw.group_one_equivalent σ)
  map_mul' X Y := Quotient.inductionOn₂ X Y fun x y =>
    ofRaw_eq_iff.mpr (Raw.group_mul_equivalent σ x y)

/-- Grouping along a surjection also preserves direct sums, because each grouped
site can distinguish the two uniform tags. -/
def groupRingHom [Nonempty I] [Nonempty J] (σ : I → J) (hs : Function.Surjective σ) :
    TensorClass.{v} I K →+* TensorClass.{max u v} J K where
  __ := groupMulHom σ
  map_zero' := ofRaw_eq_iff.mpr (Raw.group_zero_equivalent σ hs)
  map_add' X Y := Quotient.inductionOn₂ X Y fun x y =>
    ofRaw_eq_iff.mpr (Raw.group_add_equivalent σ hs x y)

/-- Pull back a normalized spectral point when sites have been identified. -/
def groupSpectralPoint [Nonempty I] [Nonempty J] (σ : I → J) (hs : Function.Surjective σ)
    (φ : normalizedSpectrum ((· ≤ ·) : TensorClass.{max u v} J K → _ → Prop)) :
    normalizedSpectrum ((· ≤ ·) : TensorClass.{v} I K → _ → Prop) := by
  let ψ := (normalizedSpectrum.toRingHom φ).comp (groupRingHom σ hs)
  exact ⟨ψ, ψ.map_zero, ψ.map_one, ψ.map_add, ψ.map_mul,
    fun x y h => φ.property.2.2.2.2 _ _ (groupClass_mono σ h)⟩

section Logarithms

variable {A B : Type} {F : Type*} [Fintype A] [Nonempty A] [Fintype B] [Nonempty B] [Field F]
variable (φ : normalizedSpectrum ((· ≤ ·) : TensorClass.{0} B F → _ → Prop))

/-- A grouped diagonal, including a wire with arbitrary endpoints, has log price
equal to its binary price times the base-two logarithm of its dimension. -/
theorem rawLogPrice_group_diagonal (σ : A → B) (c : ℝ) {α : Type} [Fintype α] [Nonempty α] :
    rawLogPrice φ c ((Raw.diagonal A F α).group σ) =
      rawLogPrice φ c ((Raw.diagonal A F (Fin 2)).group σ) * Real.logb 2 (Fintype.card α) := by
  let v : TensorClass.{0} A F →* ℝ≥0 := (normalizedSpectrum.toRingHom φ).toMonoidHom.comp (groupMulHom σ)
  have hv : ∀ {m n : ℕ}, 0 < m → m ≤ n → v m ≤ v n := by
    intro m n _ h
    apply φ.property.2.2.2.2
    apply groupClass_mono σ
    rw [← ofRaw_diagonal_fin_eq_natCast A F m, ← ofRaw_diagonal_fin_eq_natCast A F n]
    exact Raw.diagonal_restricts_of_embedding A F (Fin.castLEEmb h)
  have h := spectral_natCast_logb v hv (Fintype.card α) Fintype.card_pos
  have eval (β : Type) [Fintype β] : φ.val (ofRaw ((Raw.diagonal A F β).group σ)) =
      v (Fintype.card β : TensorClass.{0} A F) := by
    rw [← ofRaw_diagonal_eq_natCast A F β]
    rfl
  rw [rawLogPrice, rawLogPrice, eval α, eval (Fin 2), Fintype.card_fin, Nat.cast_ofNat, h, mul_assoc]

end Logarithms
end
end SiteTensor

end SpectralBooks
end LinearAlgebra
end OAI
