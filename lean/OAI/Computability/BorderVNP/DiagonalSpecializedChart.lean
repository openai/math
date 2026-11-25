import OAI.Computability.BorderVNP.DiagonalStagedChart
import OAI.Computability.BorderVNP.DiagonalSpecializedHistory

/-! # The same finite-field scalar advice in a fixed geometric replay -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal

open Crossing MvPolynomial
open scoped Classical

variable {K : Type*} [Field K] {D m : ℕ} {ι : Type} [Fintype ι] {G : PaidIdentity K D m}
    {aux : ι → K} {q k s : ℕ} {ord : Fin (k+1) × Bool ≃ Fin (2*(k+1))}
    {R : CommonField G aux q k s ord} (chart : AdvisedBranch R)

omit [Fintype ι] in
/-- The finite chart's shortening entries satisfy every integral relation in
the reference field. They occupy the first block of the shared scalar advice. -/
theorem AdvisedBranch.preserves_paid (f : MvPolynomial G.Entry ℤ)
    (h : eval₂Hom (Int.castRingHom K) G.entry f = 0) :
    eval₂Hom (Int.castRingHom chart.E) (chart.gadgets ∘ Sum.inl) f = 0 := by
  have hf := chart.preserves_tables (rename (Sum.inl : G.Entry → G.Entry ⊕ ι) f)
  simpa [AdvisedBranch.gadgets, eval₂Hom_rename, Function.comp_def, h] using hf

/-- The paid identity interpreted by the reader in this chart. Its public
histogram count, layouts and widths are those of the fixed reference identity. -/
noncomputable def AdvisedBranch.shortening : PaidIdentity chart.E D m :=
  G.specialize (chart.gadgets ∘ Sum.inl) chart.preserves_paid

omit [Fintype ι] in
/-- The reader fetches the shortening scalar at its exact joint table position. -/
theorem AdvisedBranch.shortening_entry (a : G.Entry) :
    chart.shortening.entry a = chart.gadgets (.inl a) := rfl

end Diagonal

end BorderVNP
end Computability
end OAI
