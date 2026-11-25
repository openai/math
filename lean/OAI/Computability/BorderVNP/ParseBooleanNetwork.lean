import OAI.Computability.BorderVNP.ParseBooleanLayout

/-! # Weighted Boolean verifiers as bounded-degree bit networks

The network sums over each original guess once. The checks fix the two constant
wires and all intermediate gate values, and the chains fix every copy bit.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace ParseBatch.BooleanLayout

open VPVNP.BooleanTranscript
open scoped Classical

variable {X W J : Type} {s : ℕ} [Fintype X] [Fintype W] [Fintype J]

/-- The physical layout of the verifier and its unary weights. -/
noncomputable def layout (c : Circuit (X ⊕ W) s) (weighted : J → W) :
    Layout X (Hidden W s) (Tests J s) := Layout.ofArguments arity (args c weighted)

private theorem sum_split {α β R : Type*} [Fintype α] [Fintype β] [AddCommMonoid R]
    (f : (α ⊕ β → Bool) → R) :
    ∑ z, f z = ∑ a : α → Bool, ∑ b : β → Bool, f (Sum.elim a b) := by
  rw [← (Equiv.sumArrowEquivProdArrow α β Bool).symm.sum_comp f, Fintype.sum_prod_type]
  rfl

private theorem sum_split_with {α β R : Type*} [Fintype α] [Fintype β] [AddCommMonoid R]
    [Fintype (α ⊕ β → Bool)] [Fintype (α → Bool)] [Fintype (β → Bool)]
    (f : (α ⊕ β → Bool) → R) :
    ∑ z, f z = ∑ a : α → Bool, ∑ b : β → Bool, f (Sum.elim a b) := by
  convert (sum_split f) using 1
  · apply Finset.sum_congr (Finset.ext fun z => by simp)
    intros; rfl
  · apply Finset.sum_congr (Finset.ext fun a => by simp)
    intro a _
    apply Finset.sum_congr (Finset.ext fun b => by simp)
    intros; rfl

variable (c : Circuit (X ⊕ W) s) (weighted : J → W)

/-- Each accepted original guess contributes its product of unary weights. -/
theorem value_eq {R : Type*} [CommSemiring R] (weight : J → Bool → R) (x : X → Bool) :
    (layout c weighted).network.value ((layout c weighted).tables (factor c weight))
        (fun i _ => x i) =
      ∑ w : W → Bool, if c.eval (Sum.elim x w) then ∏ j, weight j (w (weighted j)) else 0 := by
  refine ((layout c weighted).network_value (factor c weight) x).trans ?_
  trans ∑ h : Hidden W s → Bool, ∏ t, factor c weight t (Sum.elim x h ∘ args c weighted t)
  · unfold Layout.contract
    apply Finset.sum_congr (Finset.ext fun h => by simp)
    intro h _
    apply Finset.prod_congr (Finset.ext fun t => by simp)
    intro t _
    rfl
  let contribution (h : Hidden W s → Bool) := ∏ t, factor c weight t
    (Sum.elim x h ∘ args c weighted t)
  refine (sum_split_with (α := W) (β := Fin s ⊕ Bool) contribution).trans ?_
  apply Finset.sum_congr (Finset.ext fun w => by simp)
  intro w _
  refine (sum_split_with (α := Fin s) (β := Bool) (fun h => contribution (Sum.elim w h))).trans ?_
  change (∑ v : Fin s → Bool, ∑ k : Bool → Bool, ∏ t, factor c weight t
    (assignment x w v k ∘ args c weighted t)) = _
  simp only [factors_eq, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  split <;> simp_all

/-- All vertices in the physical network have at most three incident endpoints. -/
theorem degree_bound (v : (layout c weighted).Site) :
    (Finset.univ.filter (fun e : (layout c weighted).Endpoint =>
      (layout c weighted).incident e = v)).card ≤ 3 := by
  have ht (t : Tests J s) : (layout c weighted).arity t ≤ 3 := by
    rcases t with i | t
    · exact le_rfl
    · exact Nat.le_add_right 1 2
  convert (layout c weighted).degree_le_three ht v using 2
  ext e
  simp

/-- Vertices, wires and external pins together have linear size. -/
theorem volume_bound :
    Fintype.card (layout c weighted).Site + Fintype.card (layout c weighted).Edge + Fintype.card X ≤
      20 * (Fintype.card X + Fintype.card W + Fintype.card J + s + 1) := by
  rw [Layout.volume_eq, Layout.uses_eq]
  change Fintype.card (Tests J s) + 3 * (∑ t : Tests J s, arity t) +
    3 * Fintype.card (X ⊕ Hidden W s) + Fintype.card X ≤ _
  simp [Tests, Hidden, arity, Fintype.sum_sum_type]
  omega

omit [Fintype X] [Fintype W] [Fintype J] in
/-- Every original table except the specified unary weight tables has Boolean entries. -/
theorem factor_zero_one {R : Type*} [CommSemiring R] (weight : J → Bool → R) (t : Tests J s)
    (h : ∀ j : J, t ≠ .inr (.inr (.inr j))) (z : Fin (arity t) → Bool) :
    factor c weight t z = 0 ∨ factor c weight t z = 1 := by
  rcases t with i | (b | (u | j))
  · simp only [factor]; split <;> simp
  · simp only [factor]; split <;> simp
  · simp only [factor]; split <;> simp
  · exact (h j rfl).elim

end ParseBatch.BooleanLayout

end BorderVNP
end Computability
end OAI
