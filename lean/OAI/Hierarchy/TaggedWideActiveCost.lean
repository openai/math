import OAI.Hierarchy.ProtocolRAMPrune

namespace OAI
/-! # Injecting live reported charges into their original finite catalogue -/
noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.CatalogueRows
open ProtocolRAMEmit
open scoped Classical BigOperators

/-- Inactive padding has no opening charge. The whole terminal cost on true
reported rows embeds in the real edge catalogue; opening fees are charged for
all real cores and witnessed purchases, including any presently unused ones. -/
theorem active_le_catalogue {E : Type*} [Fintype E] {n : ℕ} (rows : Fin n→Row)
    (ordinal : E ↪Fin n) (priced : E→ℝ) (native : ActiveRows rows→ℝ)
    (supports : ∀i : ActiveRows rows,∃e,ordinal e=i.val ∧ native i=priced e)
    (nonneg : ∀e,0≤priced e) : (∑i,native i)≤∑e,priced e := by
  choose edge located paid using supports
  have injective : Function.Injective edge := by
    intro i j h
    apply Subtype.ext
    exact (located i).symm.trans ((congrArg ordinal h).trans (located j))
  let lookup : ActiveRows rows↪E := ⟨edge,injective⟩
  have sum := Finset.sum_map (s:=Finset.univ) lookup priced
  calc
    (∑i,native i)=∑i,priced (lookup i) := Finset.sum_congr rfl (fun i _=>paid i)
    _=∑e∈Finset.univ.map lookup,priced e := sum.symm
    _≤∑e,priced e := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun i _ _=>nonneg i)

end Hierarchy.ProtocolRAM.Calendar.CatalogueRows

end
end OAI
