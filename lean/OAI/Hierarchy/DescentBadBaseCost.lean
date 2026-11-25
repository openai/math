import OAI.Hierarchy.DescentForcedBudget
import OAI.Hierarchy.DescentLayoutEstimator

namespace OAI
/-! # Light bad bases, overloaded bases and both endpoints of capacity failures -/

namespace Hierarchy.DescentColonies
open DescentGL DescentBaseVariance
open scoped Classical BigOperators
noncomputable section

/-- Light bad bases are bought at their threshold; heavy bases are charged to
the full mass of the heavy level-zero bins. This avoids any independence
assumption between overflow and forced splitting. -/
theorem mass_of_bad {U : Type*} [Fintype U] (bad : Finset U) (w : U → ℝ) :
    ∑ u∈bad,w u ≤ 2*(bad.card:ℝ) + ∑ u∈Finset.univ.filter (fun t => 2<w t),w u := by
  have unit (u : U) : (if u∈bad then w u else 0) ≤
      (if u∈bad then 2 else 0)+(if 2<w u then w u else 0) := by
    by_cases b : u∈bad <;> by_cases heavy : 2<w u <;> simp [b,heavy] <;> linarith
  have total := Finset.sum_le_sum (s:=Finset.univ) (fun u _ => unit u)
  rw [Finset.sum_add_distrib] at total
  have univBad : Finset.univ.filter (fun u : U => u ∈ bad) = bad :=
    Finset.filter_mem_eq_of_subset (Finset.subset_univ bad)
  rw [← Finset.sum_filter, ← Finset.sum_filter, ← Finset.sum_filter,
    univBad] at total
  simpa only [Finset.sum_const, nsmul_eq_mul, mul_comm (bad.card : ℝ) 2] using total

variable {k : ℕ} {V C : Type*} [Fintype V] [Fintype C] [DecidableEq V]

/-- A failing neighbor pair marks the precise two adjoining bases. Endpoints can
coincide so the price is an upper bound on the number of distinct marked bases. -/
def capacityEnds (j : C → ℕ) (hj : ∀ e,j e≤k) (L : Layout k) (core : C → Block k → ℝ)
    (K : ℝ) (ends : ∀ e,Block (j e) → (V × ℕ) × (V × ℕ)) : Finset (V × ℕ) :=
  Finset.univ.biUnion (fun e : C =>
    (Finset.univ.filter fun z => mean (core e) (Block (j e))+1/K <
      load (dyadicLayout (hj e) L) (core e) z).biUnion fun z => {(ends e z).1,(ends e z).2})

omit [Fintype V] in
theorem capacityEnds_card (j : C → ℕ) (hj : ∀ e,j e≤k) (L : Layout k) (core : C → Block k → ℝ)
    (K : ℝ) (pos : 0<K) (ends : ∀ e,Block (j e) → (V × ℕ) × (V × ℕ)) :
    ((capacityEnds j hj L core K ends).card:ℝ) ≤
      2*∑ e,K^2*variance (DescentLinearLayouts.layout (hj e) L) (core e ∘ address k) := by
  let heavy (e : C) := Finset.univ.filter fun z => mean (core e) (Block (j e))+1/K <
    load (dyadicLayout (hj e) L) (core e) z
  have pair (p q : V×ℕ) : ({p,q}:Finset (V×ℕ)).card≤2 :=
    (Finset.card_insert_le _ _).trans (by simp)
  have size : (capacityEnds j hj L core K ends).card≤∑e,2*(heavy e).card := by
    apply Finset.card_biUnion_le.trans
    apply Finset.sum_le_sum
    intro e _
    apply Finset.card_biUnion_le.trans
    change (∑ z ∈ heavy e, ({(ends e z).1,(ends e z).2} : Finset (V × ℕ)).card) ≤ 2 * (heavy e).card
    calc
      _ ≤ ∑ _z ∈ heavy e, 2 := Finset.sum_le_sum fun z _ => pair (ends e z).1 (ends e z).2
      _ = _ := by simp [Nat.mul_comm]
  apply (show ((capacityEnds j hj L core K ends).card:ℝ)≤ ∑e,2*((heavy e).card:ℝ) by exact_mod_cast size).trans
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro e _
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  rw [←address_variance]
  exact capacity_marks (dyadicLayout (hj e) L) (core e) K pos

/-- The positional identifiers of the two bases adjoining a genuine
intersection prefix. Its depth is the larger of the two endpoint depths. -/
def reservationEndpoints (base : V → ℕ) (s t : C → V) (e : C)
    (q : Block (max (base (s e)) (base (t e)))) : (V×ℕ)×(V×ℕ) :=
  let j := max (base (s e)) (base (t e))
  ((s e,q.val/2^(j-base (s e))),(t e,q.val/2^(j-base (t e))))

end
end Hierarchy.DescentColonies

end OAI
