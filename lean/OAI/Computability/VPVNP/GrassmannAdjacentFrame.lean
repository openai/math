import OAI.Computability.VPVNP.GrassmannIndependent
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas

/-!
# A shared frame for adjacent binary Grassmannian planes

Two planes at distance one have bases with all but their last columns in
common. The tuple consisting of the common columns and both last columns is
independent. This gives coordinates for the adjacent-pair sampling in §5.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace Grassmann

open Module Submodule Set

/-- A common basis for the intersection and one additional column from each
of an ordered pair of adjacent planes. -/
theorem exists_adjacent_frame {n : ℕ} (p : Pair (n + 1) 1) :
    ∃ (b : Fin n → Space (n + 1)) (u v : Space (n + 1)),
      LinearIndependent (ZMod 2) (Fin.snoc (Fin.snoc b u) v : Fin (n + 2) → _) ∧
      LinearIndependent (ZMod 2) (Fin.snoc b u : Fin (n + 1) → _) ∧
      LinearIndependent (ZMod 2) (Fin.snoc b v : Fin (n + 1) → _) ∧
      span (ZMod 2) (range (Fin.snoc b u : Fin (n + 1) → _)) = p.val.1.val ∧
      span (ZMod 2) (range (Fin.snoc b v : Fin (n + 1) → _)) = p.val.2.val := by
  let U := p.val.1.val
  let V := p.val.2.val
  let I := U ⊓ V
  have hU : finrank (ZMod 2) U = n + 1 := p.val.1.property
  have hV : finrank (ZMod 2) V = n + 1 := p.val.2.property
  have hS : finrank (ZMod 2) (U ⊔ V : Submodule _ _) = n + 2 := p.property
  have hI : finrank (ZMod 2) I = n := by
    have hd := U.finrank_sup_add_finrank_inf_eq V
    rw [hS, hU, hV] at hd
    change finrank (ZMod 2) (U ⊓ V : Submodule _ _) = n
    omega
  have outside (W : Submodule (ZMod 2) (Space (n + 1))) (hW : finrank (ZMod 2) W = n + 1) :
      ∃ x ∈ W, x ∉ I := by
    apply Set.not_subset_iff_exists_mem_notMem.mp
    intro h
    have := Submodule.finrank_mono (show W ≤ I from h)
    omega
  obtain ⟨u, hu, huI⟩ := outside U hU
  obtain ⟨v, hv, hvI⟩ := outside V hV
  let basis := finBasisOfFinrankEq (ZMod 2) I hI
  let b := I.subtype ∘ basis
  have hb : LinearIndependent (ZMod 2) b := basis.linearIndependent.map' I.subtype I.ker_subtype
  have hspan : span (ZMod 2) (range b) = I := by
    rw [show range b = I.subtype '' range basis from Set.range_comp ..,
      Submodule.span_image, basis.span_eq, Submodule.map_subtype_top]
  have hu' := hb.finSnoc (hspan ▸ huI)
  have hv' := hb.finSnoc (hspan ▸ hvI)
  have span_eq (W : Submodule (ZMod 2) (Space (n + 1))) (hIW : I ≤ W)
      (hW : finrank (ZMod 2) W = n + 1) (x : Space (n + 1)) (hx : x ∈ W)
      (hbx : LinearIndependent (ZMod 2) (Fin.snoc b x : Fin (n + 1) → _)) :
      span (ZMod 2) (range (Fin.snoc b x : Fin (n + 1) → _)) = W := by
    apply Submodule.eq_of_le_of_finrank_eq
    · rw [Fin.range_snoc, span_le]
      exact Set.insert_subset hx ((span_le.mp (hspan ▸ hIW)))
    · rw [finrank_span_eq_card hbx, Fintype.card_fin, hW]
  have hsu := span_eq U inf_le_left hU u hu hu'
  have hsv := span_eq V inf_le_right hV v hv hv'
  refine ⟨b, u, v, hu'.finSnoc ?_, hu', hv', hsu, hsv⟩
  rw [hsu]
  exact fun h => hvI ⟨h, hv⟩

end Grassmann

end VPVNP
end Computability
end OAI
