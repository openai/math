import OAI.Computability.BorderVNP.ShortenStaticRowsAccess

/-!
# Occupancy of the static hook and retained rectangles

A charged, matched-prefix band occupies both hook rows. Every other band
occupies its retained row. A hook's seed is recovered from the original
bin by the inverse public direction permutation.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Shortening.StaticRows

open Crossing SeedIntervals CombiningStep
open scoped Classical

variable {D m : ℕ} [NeZero D] {P : Type*} {bits : P → ℕ} {K : Type*} [Field K]
variable (e : PaidIdentity K D m) (p : Pack D P bits K)
variable {A : Type} [Fintype A] (bin : p.layout.Edge → Option A) (perm : Fin D → Equiv.Perm A)

omit [Field K] [Fintype A] in
/-- Matched-prefix rows at the actual permuted source bin have one unique recovered seed. -/
theorem prefix_mem_iff (a : A) (d : Fin D) (c : p.layout.Edge) :
    (c, some (d,true)) ∈ (partition p.layout bin perm m).part a ↔ bin c = some (perm d a) := by
  constructor
  · exact fun h => (Finset.mem_filter.mp h).2.2
  · exact fun h => Finset.mem_filter.mpr ⟨Finset.mem_univ _,rfl,h⟩

omit [Field K] in
/-- The hook rectangle is occupied exactly for a direction prefix of a charged old cable. -/
theorem selected_iff (c : p.layout.Edge) (b : Band D) :
    (c,b) ∈ (partition p.layout bin perm m).selected ↔
      (bin c).isSome = true ∧ ∃ d : Fin D, b = some (d,true) := by
  constructor
  · intro h
    let t := partition p.layout bin perm m
    obtain ⟨⟨a,v⟩,he⟩ := t.edgeIndex.surjective ⟨(c,b),h⟩
    have hv : v.val = (c,b) := congrArg Subtype.val he
    have ha : (c,b) ∈ t.part a := hv ▸ v.property
    obtain ⟨hb,hc⟩ := (Finset.mem_filter.mp ha).2
    exact ⟨by rw [hc]; rfl, ⟨direction b,hb⟩⟩
  · rintro ⟨hc,d,rfl⟩
    cases h : bin c with
    | none => simp [h] at hc
    | some x =>
      let t := partition p.layout bin perm m
      have hs : (c, some (d,true)) ∈ t.part ((perm d).symm x) :=
        (prefix_mem_iff (m := m) p bin perm _ _ _).mpr (by rw [Equiv.apply_symm_apply]; exact h)
      exact (t.includeEdge _ ⟨(c,some (d,true)),hs⟩).property

omit [Field K] [Fintype A] in
private theorem prefix_preimage (a : A) (c : ↥((partition p.layout bin perm m).part a)) :
    ∃ (d : Fin D) (u : {u : p.layout.Edge // bin u = some (perm d a)}),
      (prefixEdge p.layout bin perm m a d u).val = c := by
  let d := direction c.val.2
  let u : {u : p.layout.Edge // bin u = some (perm d a)} := ⟨c.val.1, bin_selected p.layout bin perm m c⟩
  refine ⟨d,u,Subtype.ext ?_⟩
  change (c.val.1, some (d,true)) = c.val
  exact Prod.ext rfl (Finset.mem_filter.mp c.property).2.1.symm

/-- The explicit named hook rows exhaust the actual cut ports of the sewn graph. -/
theorem hook_exhaustive (u : (layout p.layout bin perm m).CutPorts (partition p.layout bin perm m).selected) :
    ∃ (a : A) (d : Fin D) (c : {c : p.layout.Edge // bin c = some (perm d a)}) (source : Bool),
      seedHook e p bin perm a d c source = Sum.inl u := by
  let t := partition p.layout bin perm m
  obtain ⟨⟨a,s⟩,hs⟩ := t.portIndex.surjective u
  cases s with
  | inl c =>
    obtain ⟨d,v,h⟩ := prefix_preimage p bin perm a c
    refine ⟨a,d,v,true,?_⟩
    change Sum.inl (t.includePort a (.inl (prefixEdge p.layout bin perm m a d v).val)) = Sum.inl u
    rw [h]
    exact congrArg Sum.inl hs
  | inr c =>
    obtain ⟨d,v,h⟩ := prefix_preimage p bin perm a c
    refine ⟨a,d,v,false,?_⟩
    change Sum.inl (t.includePort a (.inr (prefixEdge p.layout bin perm m a d v).val)) = Sum.inl u
    rw [h]
    exact congrArg Sum.inl hs

/-- The row number of a physical edge is identical in any two histogram branches. -/
theorem same_histogram_rows {nEdges nSeeds : ℕ} (old : p.layout.Edge ↪ Fin nEdges) (seed : A ↪ Fin nSeeds)
    (positive : p.layout.Edge → Bool) (first : Fin D × Bool) (q r : Counts e p bin perm)
    (c : EdgeShape e p bin perm) :
    outputRows e p bin perm positive first q old seed c = outputRows e p bin perm positive first r old seed c := rfl

end Shortening.StaticRows

end BorderVNP
end Computability
end OAI
