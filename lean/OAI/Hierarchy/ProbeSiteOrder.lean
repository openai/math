import OAI.Hierarchy.ProbeFormats
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.Perm

namespace OAI
/-! # Naming a finite local format by its order in the physical layout -/

namespace Hierarchy.AdaptiveProbe

noncomputable section

variable {X : Type*} [Fintype X] {S : ℕ}

/-- The rank in the occupied physical rows names each local site. The order
embedding recovers the actual row, including any intervening unoccupied rows. -/
structure SiteOrder (place : X ↪ Fin S) where
  name : X ≃ Fin (Fintype.card X)
  ord : Fin (Fintype.card X) ↪o Fin S
  reconstruct : ∀ x, ord (name x) = place x

def SiteOrder.ofEmbedding (place : X ↪ Fin S) : SiteOrder place := by
  classical
  let occupied := Finset.univ.map place
  have card : occupied.card = Fintype.card X := by simp [occupied]
  let row (x : X) : occupied := ⟨place x, Finset.mem_map.mpr ⟨x,Finset.mem_univ _,rfl⟩⟩
  have bij : Function.Bijective row := by
    constructor
    · intro x y h
      exact place.injective (congrArg Subtype.val h)
    · rintro ⟨v,hv⟩
      obtain ⟨x,_,h⟩ := Finset.mem_map.mp hv
      exact ⟨x,Subtype.ext h⟩
  let rank := occupied.orderIsoOfFin card
  refine ⟨(Equiv.ofBijective row bij).trans rank.symm.toEquiv, occupied.orderEmbOfFin card, ?_⟩
  intro x
  exact congrArg Subtype.val (rank.apply_symm_apply (row x))

/-- One radius threshold works for all possible orders of a given format.
At each admissible radius, every physical naming uses the same tolerance. -/
theorem SiteOrder.common_tolerance (good : (X ≃ Fin (Fintype.card X)) → ℕ → ℝ → Prop)
    (monotone : ∀ e M, ∀ {a b : ℝ}, a ≤ b → good e M b → good e M a)
    (each : ∀ e, ∃ N : ℕ, ∀ M ≥ N, ∃ ε : ℝ, 0 < ε ∧ good e M ε) :
    ∃ N : ℕ, ∀ M ≥ N, ∃ ε : ℝ, 0 < ε ∧ ∀ e, good e M ε := by
  classical
  exact finite_tolerances good monotone each


end
end Hierarchy.AdaptiveProbe

end OAI
