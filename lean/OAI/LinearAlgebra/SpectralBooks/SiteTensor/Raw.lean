import OAI.LinearAlgebra.SpectralBooks.SiteTensor.Restriction

/-! # Finite coefficient tensors and local restriction

The coordinate type at each site is arbitrary and finite. Keeping the local
types in the format lets the tensor product use pairs of basis indices and the
direct sum use disjoint unions. Mutual restriction identifies changes of basis
and redundant local dimensions.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

namespace SiteTensor

universe v u w

/-- A finite local format, together with the tensor's coefficients. -/
structure Raw (I : Type u) (K : Type w) where
  Leg : I → Type v
  finiteLeg : ∀ i, Fintype (Leg i)
  coeff : (∀ i, Leg i) → K

attribute [instance] Raw.finiteLeg

namespace Raw

variable {I : Type u} {K : Type w}

noncomputable section
open scoped Classical

/-- Restriction by one matrix at each site, expressed in the chosen bases. -/
abbrev Restricts [Fintype I] [CommSemiring K] (X Y : Raw.{v} I K) :=
  Crossing.IsRestriction X.coeff Y.coeff

/-- The equivalence relation used to form the tensor semiring. -/
def Equivalent [Fintype I] [CommSemiring K] (X Y : Raw.{v} I K) : Prop :=
  X.Restricts Y ∧ Y.Restricts X

/-- Mutual restriction is a setoid by composition of local matrices. -/
def setoid (I : Type u) (K : Type w) [Fintype I] [CommSemiring K] : Setoid (Raw.{v} I K) where
  r := Equivalent
  iseqv := ⟨fun X => ⟨restrict_refl X.coeff, restrict_refl X.coeff⟩,
    fun h => And.symm h, fun h g => ⟨restrict_trans h.1 g.1, restrict_trans g.2 h.2⟩⟩

/-- Relabeling each coordinate basis by a bijection preserves mutual restriction. -/
theorem reindex_equivalent [Fintype I] [CommSemiring K] {X Y : Raw.{v} I K}
    (e : ∀ i, X.Leg i ≃ Y.Leg i) (h : ∀ x, X.coeff x = Y.coeff (fun i => e i (x i))) :
    X.Equivalent Y := by
  refine ⟨restrict_of_equiv e h, restrict_of_equiv (fun i => (e i).symm) ?_⟩
  intro y
  simpa using (h (fun i => (e i).symm (y i))).symm

/-- The empty local format represents the additive identity. -/
def zero (I : Type u) (K : Type w) [Zero K] : Raw.{v} I K :=
  ⟨fun _ => PEmpty, fun _ => inferInstance, fun _ => 0⟩

/-- The scalar unit has one basis vector at each site. -/
def one (I : Type u) (K : Type w) [One K] : Raw.{v} I K :=
  ⟨fun _ => PUnit, fun _ => inferInstance, fun _ => 1⟩

/-- Tensor multiplication groups the two local factors at each site. -/
def mul [Mul K] (X Y : Raw.{v} I K) : Raw.{v} I K :=
  ⟨fun i => X.Leg i × Y.Leg i, fun _ => inferInstance,
    fun x => X.coeff (fun i => (x i).1) * Y.coeff (fun i => (x i).2)⟩

/-- The common-label diagonal, with one summand per label. -/
def diagonal (I : Type u) (K : Type w) (α : Type v) [Fintype α] [CommSemiring K] : Raw.{v} I K :=
  ⟨fun _ => α, fun _ => inferInstance, fun x => ∑ a : α, if x = fun _ => a then 1 else 0⟩

end
end Raw

end SiteTensor

end SpectralBooks
end LinearAlgebra
end OAI
