import OAI.Computability.BorderVNP.PackedBottomReportSources
import OAI.Computability.BorderVNP.PackedGridWitnessUse

/-! # Counting the true weighted source inventory after routing and cell partition

Each original weighted vertex gives one private sidecar position. Subdivision
inserts only ordinary checks, and every fine vertex belongs to one cell. Thus
summing the per-cell private sidecar counts recovers the exact source count,
independently of the private route choices.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.BottomReports

open Crossing CellSparse GridBoxes
open scoped Classical

/-- A one-copy source contributes one entry exactly when its original unary factor
carries a named weight. -/
theorem count_eq_sum (fs : List Factor) :
    count fs = (fs.map (fun f => (factorTag f).isSome.toNat)).sum := by
  induction fs with
  | nil => rfl
  | cons f fs ih => cases f <;> simp [count,factorTag,ih,Nat.add_comm]

variable {D : ℕ} {P C : Type} [Fintype P] [Fintype C] {bits : P → ℕ}
variable (N : Network D P bits) (cell : N.Site → C)
variable {ne np ns : ℕ} (sites : N.Site ↪ Fin ns) (edges : N.Edge ↪ Fin ne) (ports : P ↪ Fin np)
variable (rules : ∀ w : N.Site, Rule N w)

omit [Fintype C] in
/-- The one-copy sidecar count in a particular cell counts exactly the original
fine sites whose rule carries a unary source label. -/
theorem grid_count (c : C) :
    count (factors N cell c sites edges ports (fun w => rules w.val)) =
      ∑ w : {u : N.Site // cell u = c}, (ruleTag (rules w.val)).isSome.toNat := by
  let V := {u : N.Site // cell u = c}
  have order : ∃ e : Fin (Fintype.card V) ≃ V, siteList N cell c sites = List.ofFn e := by
    unfold siteList
    exact ⟨_,rfl⟩
  obtain ⟨e,he⟩ := order
  rw [count_eq_sum]
  simp only [factors,he,List.map_ofFn,List.sum_ofFn,Function.comp_def,factorTag_rule]
  exact e.sum_comp (fun w : V => (ruleTag (rules w.val)).isSome.toNat)

/-- The real lists across the whole grid contain exactly the number of original
weighted sites; the upper bound is an equality even when many share a cell. -/
theorem total_grid_count {J : Type} [Fintype J] (weight : J ↪ N.Site)
    (named : ∀ w, (ruleTag (rules w)).isSome = true ↔ w ∈ Set.range weight) :
    (∑ c, count (factors N cell c sites edges ports (fun w => rules w.val))) = Fintype.card J := by
  simp_rw [grid_count]
  rw [Fintype.sum_fiberwise cell (fun w => (ruleTag (rules w)).isSome.toNat)]
  have hc : ∀ w, (ruleTag (rules w)).isSome.toNat = if w ∈ Set.range weight then 1 else 0 := by
    intro w
    cases h : (ruleTag (rules w)).isSome
    · have hn : w ∉ Set.range weight := fun hw => by simpa [h] using (named w).mpr hw
      simp [hn]
    · simp [(named w).mp h]
  simp_rw [hc]
  rw [← Finset.card_filter]
  let e := Equiv.ofInjective weight weight.injective
  exact (Fintype.card_subtype _).symm.trans (Fintype.card_congr e.symm)

open ParseBatch VPVNP.BooleanTranscript

/-- Rewiring and subdivision create no additional named source positions, for
arbitrary one-copy topology, table choices and report labels. -/
theorem routed_verifier_names {X W J R : Type} [Fintype X] [Fintype W] [Fintype J] [CommSemiring R]
    {s : ℕ} (c : Circuit (X ⊕ W) s) (weighted : J → W) (value : J → Bool → R)
    (tag : J → Port) (routes : (BooleanLayout.layout c weighted).network.WireRoutes)
    (w : ((BooleanLayout.layout c weighted).network.subdivide routes).Site) :
    (ruleTag (routedRule (BooleanLayout.layout c weighted).network routes (verifierRule c weighted value tag) w)).isSome =
      true ↔ w ∈ Set.range ((BooleanLayout.weightSite c weighted).trans Function.Embedding.inl) := by
  rw [routed_tag]
  cases w with
  | inr w =>
    change false = true ↔ ∃ j, Sum.inl (BooleanLayout.weightSite c weighted j) = Sum.inr w
    simp
  | inl w =>
    change (ruleTag (verifierRule c weighted value tag w)).isSome = true ↔
      ∃ j, (Sum.inl (BooleanLayout.weightSite c weighted j) : (BooleanLayout.layout c weighted).network.Site ⊕ _) =
        Sum.inl w
    by_cases h : ∃ j, BooleanLayout.weightSite c weighted j = w <;> simp [verifierRule,h,ruleTag]

end Packing.BottomReports

end BorderVNP
end Computability
end OAI
