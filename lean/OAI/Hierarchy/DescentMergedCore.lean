import OAI.Hierarchy.DescentMergedCableCost

namespace OAI
/-! # Core marks and original tethers after a physical subround -/

namespace Hierarchy.DescentSixParty.GadgetNetwork

open Computability.BorderVNP.Crossing
open scoped BigOperators Classical
noncomputable section

variable {I C : Type} [Fintype I] {D d : ℕ} {P : Type*} {bits : P → ℕ}
variable (N : Network D P bits) (pick : I × Fin 2 ↪ N.Edge) (sw : I → Fin 8 → ℕ)
variable (layout : Bool) (pack : N.Site → C)
variable (pos : Merged N pick layout pack → EuclideanSpace ℝ (Fin d)) (hpos : ∀ c, ‖pos c‖ ≤ 1)
local notation "Q" => merged N pick sw layout pack pos hpos
local notation "M" => physical N pick sw

private def keeps (old : Finset N.Edge) (fresh : Bool) : Edge (I:=I) N → Prop
  | .inl e => e ∈ old
  | .inr _ => fresh = true

private def marked (old : Finset N.Edge) (fresh : Bool) : Finset (Q).Edge :=
  Finset.univ.filter fun e => keeps N old fresh e.val

/-- Untouched original edges inherit their marks. Every surviving supply edge is core. -/
def nextCore (core : Finset N.Edge) : Finset (Q).Edge := marked N pick sw layout pack pos hpos core true

@[simp] theorem mem_nextCore (core : Finset N.Edge) (e : (Q).Edge) :
    e ∈ nextCore N pick sw layout pack pos hpos core ↔
      (match e.val with | .inl t => t ∈ core | .inr _ => True) := by
  simp only [nextCore, marked, Finset.mem_filter, Finset.mem_univ, true_and]
  rcases e with ⟨t, ht⟩
  cases t <;> simp [keeps]

private theorem marked_width_le (old : Finset N.Edge) (fresh : Bool) :
    (∑ e ∈ marked N pick sw layout pack pos hpos old fresh, (Q).width e) ≤
      (∑ e ∈ old \ Finset.univ.map pick, N.width e) + (if fresh = true then surviving sw layout else 0) := by
  classical
  let cost (e : (M).Edge) := if keeps N old fresh e then chargedWidth N pick sw layout e else 0
  calc
    _ = ∑ e : (Q).Edge, cost e.val := by
      rw [marked, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro e _
      change (if keeps N old fresh e.val then (M).width e.val else 0) = _
      simp only [cost, external_width N pick sw layout pack e.val e.property]
    _ ≤ ∑ e : (M).Edge, cost e := crossing_sum_le N pick sw layout pack pos hpos cost
    _ = _ := by
      change (∑ e : Edge (I:=I) N, if keeps N old fresh e then chargedWidth N pick sw layout e else 0) = _
      rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
      cases fresh <;>
        simp only [keeps, chargedWidth, Fintype.sum_prod_type, Bool.false_eq_true, ↓reduceIte,
          Finset.sum_const_zero, zero_add, add_zero, surviving]
      case' true => apply congrArg₂ Nat.add ?_ rfl
      all_goals
        rw [← Finset.sum_ite_mem_eq (old \ Finset.univ.map pick)]
        apply Finset.sum_congr rfl
        intro e _
        by_cases hOld : e ∈ old <;> by_cases hPick : e ∈ Finset.univ.map pick <;> simp [hOld,hPick]

/-- After removing the two real selected inputs per instance, charge only surviving supply widths. -/
theorem nextCore_width_paid (core : Finset N.Edge) (picked : ∀ t, pick t ∈ core)
    (b : ℕ) (z : I → ℕ) (fit : ∀ i s, N.width (pick (i,s)) = z i * b) :
    (∑ e ∈ nextCore N pick sw layout pack pos hpos core, (Q).width e) + 2*b*(∑ i, z i) ≤
      (∑ e ∈ core, N.width e) + surviving sw layout := by
  have subset : Finset.univ.map pick ⊆ core := by
    intro e he
    obtain ⟨t, _, rfl⟩ := Finset.mem_map.mp he
    exact picked t
  have split := Finset.sum_sdiff (f := N.width) subset
  have paid := picked_width N pick b z fit
  have bound := marked_width_le N pick sw layout pack pos hpos core true
  rw [ite_eq_left rfl] at bound
  calc
    _ ≤ ((∑ e ∈ core \ Finset.univ.map pick, N.width e) + surviving sw layout) +
        2*b*(∑ i, z i) := Nat.add_le_add_right bound _
    _ = _ := by omega

/-- Every new tether is an untouched old tether crossing two different contracted parts. -/
theorem nextTether_width_le (core : Finset N.Edge) :
    (∑ e ∈ (nextCore N pick sw layout pack pos hpos core)ᶜ, (Q).width e) ≤ ∑ e ∈ coreᶜ, N.width e := by
  classical
  have other : (nextCore N pick sw layout pack pos hpos core)ᶜ =
      marked N pick sw layout pack pos hpos coreᶜ false := by
    ext e
    rcases e with ⟨t, ht⟩
    cases t <;> simp [nextCore, marked, keeps]
  rw [other]
  have bound := marked_width_le N pick sw layout pack pos hpos coreᶜ false
  simp only [Bool.false_eq_true, ↓reduceIte, add_zero] at bound
  exact bound.trans (Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset (fun _ _ _ => Nat.zero_le _))

end
end Hierarchy.DescentSixParty.GadgetNetwork

end OAI
