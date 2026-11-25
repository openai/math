import OAI.ThreeFlat.ExpanderBasic
import Mathlib.Combinatorics.SimpleGraph.Acyclic

namespace OAI
/-! # Connectivity from a real Poincaré bound

The indicator of a component has zero energy. Two different components
would give this indicator strictly positive variance.
-/

namespace ThreeFlat.Expander

open Finset
open scoped BigOperators

private theorem avg_pos_at {V : Type*} [Fintype V] {g : V → ℝ} (v : V)
    (h : ∀ i, 0 ≤ g i) (hv : 0 < g v) : 0 < avg g := by
  let : Nonempty V := ⟨v⟩
  have hsum : 0 < ∑ i, g i := sum_pos' (fun i _ => h i) ⟨v, mem_univ _, hv⟩
  exact div_pos hsum (Nat.cast_pos.mpr Fintype.card_pos)

/-- Any symmetric arc table admitting a real Poincaré bound is connected
through its positive entries. -/
theorem connected_of_real_bound {V : Type*} [Fintype V] (c : V → V → ℕ) {d : ℕ} {γ : ℝ}
    (hsymm : ∀ i j, c i j = c j i) (hbound : Bound (transition c d) ℝ γ) (u v : V) :
    Relation.ReflTransGen (fun i j => 0 < c i j) u v := by
  classical
  let reach := Relation.ReflTransGen (fun i j => 0 < c i j) u
  by_contra hv
  have hu : reach u := Relation.ReflTransGen.refl
  have hv' : ¬ reach v := hv
  let f (i : V) : ℝ := if reach i then 1 else 0
  have edge (i j : V) : transition c d i j * dist (f i) (f j) ^ 2 = 0 := by
    by_cases hij : 0 < c i j
    · have hji : 0 < c j i := hsymm i j ▸ hij
      have same : reach i ↔ reach j := ⟨fun hi => hi.tail hij, fun hj => hj.tail hji⟩
      simp [f, same]
    · simp [transition, Nat.eq_zero_of_not_pos hij]
  have hzero : energy (transition c d) f = 0 := by simp [energy, avg, edge]
  have hpos : 0 < variance f := by
    apply avg_pos_at u (fun _ => avg_nonneg fun _ => sq_nonneg _)
    apply avg_pos_at v (fun _ => sq_nonneg _)
    simp [f, hu, hv']
  have hle := hbound f
  rw [hzero, mul_zero] at hle
  exact (not_lt_of_ge hle) hpos

/-- A nonempty real-expanding arc table supports a spanning tree.
Loops may occur in the arc table. -/
theorem exists_port_spanning_tree {V : Type*} [Fintype V] [Nonempty V] (c : V → V → ℕ)
    {d : ℕ} {γ : ℝ} (hsymm : ∀ i j, c i j = c j i) (hbound : Bound (transition c d) ℝ γ) :
    ∃ T : SimpleGraph V, T.IsTree ∧ ∀ i j, T.Adj i j → 0 < c i j := by
  let G := SimpleGraph.fromRel fun i j => 0 < c i j
  have hconn : G.Connected := by
    refine ⟨?_⟩
    intro u v
    rw [SimpleGraph.reachable_iff_reflTransGen]
    induction connected_of_real_bound c hsymm hbound u v with
    | refl => exact .refl
    | @tail i j _ h ij =>
      by_cases he : i = j
      · subst j; exact ij
      · exact ij.tail ⟨he, Or.inl h⟩
  obtain ⟨T, hsub, hT⟩ := hconn.exists_isTree_le
  refine ⟨T, hT, fun i j hij => ?_⟩
  have h : G.Adj i j := hsub hij
  exact h.2.elim id (fun hji => hsymm j i ▸ hji)

end ThreeFlat.Expander

end OAI
