import OAI.Hierarchy.TaggedShorterProfile
import OAI.Hierarchy.TaggedPruneBudget

namespace OAI
/-! # Active shorter transports in a retained routing summand -/

namespace Hierarchy.TaggedShorterBudget

open Real Finset Set
noncomputable section

variable {u : ℝ→ℝ} {A ε p q Q σ L δ η ξ : ℝ}

/-- Direct interface for retained protocol summands. After subtracting the
different-layer flow, only positive-scale links enter the shorter calls. -/
theorem Choice.pruned_active_types (h : Choice u A ε p q Q σ L δ η ξ) {C : ℝ} (hC : 0≤C) :
    ∃ m : ℕ, ∀ a∈Icc 1 A, ∀ (ι : Type*) [Fintype ι] (scale : ι→ℕ) (t l y : ι→ℝ)
      (cross : Finset ι) (n w M Nc : ℕ),
      (∀ i,0≤t i) → (∀ i,0≤l i) → (∀ i,0≤y i) →
      (∀ i∈cross,t i=0) →
      (∀ i,0<t i → t i=dyadic (scale i) ∧ L*t i^σ≤l i) →
      ((Finset.univ.filter (fun i=>0<t i)).card:ℝ)≤C*n →
      AdaptiveProbe.TermBudget p q Q L n w M Nc t l y →
      2*(M:ℝ)*Nc/w-n ≤ ∑ i∈cross,l i*y i →
      ∀ j k, (active (Finset.univ.filter (fun i=>0<t i)) scale y m j k:ℝ) ≤
        fraction ξ (u a+a*(-deriv u a)-δ) (1-(-deriv u a)-δ) j k*n := by
  obtain ⟨m,usable⟩ := h.active_types hC
  refine ⟨m,?_⟩
  intro a ha ι _ scale t l y cross n w M Nc ht hl hy hz indexed card budget kept j k
  let links := Finset.univ.filter (fun i=>0<t i)
  have hlp : 0<L := zero_lt_one.trans_le h.one_le_price
  have data (i : ι) (hi : i∈links) : t i=dyadic (scale i) ∧ L*t i^σ≤l i :=
    indexed i (Finset.mem_filter.mp hi).2
  have pos := TaggedPrune.positive_budget hlp.le ht hl hy hz budget kept
  apply usable a ha ι links scale l y n (Nat.cast_nonneg _) card _ _ j k
  · intro i hi
    obtain ⟨eq,hprice⟩ := data i hi
    rw [eq] at hprice
    exact ⟨(mul_pos hlp (rpow_pos_of_pos (dyadic_pos _) _)).trans_le hprice,hy i,hprice⟩
  · apply le_trans _ pos
    apply le_of_eq (sum_congr rfl ?_)
    intro i hi
    obtain ⟨eq,_⟩ := data i hi
    simp only [eq, AdaptiveProbe.capacity,ite_eq_right (dyadic_pos (scale i)).ne',capacity]


end
end Hierarchy.TaggedShorterBudget

end OAI
