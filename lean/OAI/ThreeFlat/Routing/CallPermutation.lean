import OAI.ThreeFlat.Routing.Lookup
import Mathlib.Data.Finset.Sort

namespace OAI
/-! # Completing the partial permutation in one pool call

The occupied slots on each side are indexed by the same units. The
completion takes the unused left slots, in increasing order, to the
unused right slots in increasing order. Pinning all of these slots to
zero leaves exactly the prescribed unit equalities.
-/

namespace ThreeFlat.Routing.CallPool

open scoped Classical
noncomputable section

variable {A : Type*} [Fintype A] {m : ℕ}

/-- Match active positions by their common unit. -/
def activeEquiv (L R : A ↪ Fin m) : Set.range L ≃ Set.range R :=
  (Equiv.ofInjective L L.injective).symm.trans (Equiv.ofInjective R R.injective)

private theorem idle_card (L R : A ↪ Fin m) :
    Fintype.card {x : Fin m // x ∉ Set.range L} =
      Fintype.card {x : Fin m // x ∉ Set.range R} := by
  rw [Fintype.card_subtype_compl, Fintype.card_subtype_compl]
  exact congrArg (fun v => Fintype.card (Fin m) - v) (Fintype.card_congr (activeEquiv L R))

/-- The unique increasing bijection of the unused slots. -/
def idleOrderIso (L R : A ↪ Fin m) :
    {x : Fin m // x ∉ Set.range L} ≃o {x : Fin m // x ∉ Set.range R} :=
  (Fintype.orderIsoFinOfCardEq _ rfl).symm.trans
    (Fintype.orderIsoFinOfCardEq _ (idle_card R L))

/-- The deterministic permutation deployed at a call. -/
def completePermutation (L R : A ↪ Fin m) : Equiv.Perm (Fin m) :=
  Equiv.subtypeCongr (activeEquiv L R) (idleOrderIso L R).toEquiv

theorem completePermutation_active (L R : A ↪ Fin m) (u : A) :
    completePermutation L R (L u) = R u := by
  have hu : L u ∈ Set.range L := ⟨u, rfl⟩
  simp only [completePermutation, Equiv.subtypeCongr, Equiv.trans_apply,
    Equiv.sumCompl_symm_apply_of_pos hu, Equiv.sumCongr_apply, Sum.map_inl, Equiv.sumCompl_apply_inl]
  change ((Equiv.ofInjective R R.injective) ((Equiv.ofInjective L L.injective).symm
    ((Equiv.ofInjective L L.injective) u))).val = _
  rw [Equiv.symm_apply_apply]
  rfl

theorem completePermutation_idle (L R : A ↪ Fin m) (i : Fin m) (h : i ∉ Set.range L) :
    completePermutation L R i = (idleOrderIso L R ⟨i,h⟩).val := by
  simp [completePermutation, Equiv.subtypeCongr, Equiv.sumCompl_symm_apply_of_neg h]

/-- A padded call checks the payloads on its assigned units. -/
theorem taggedSwitch_complete (K : Type*) [Zero K] [One K] {V : Type*} (zero : V)
    (L R : A ↪ Fin m) (src dst : Fin m → V)
    (hs : ∀ i, i ∉ Set.range L → src i = zero)
    (hd : ∀ i, i ∉ Set.range R → dst i = zero) :
    taggedSwitch K (completePermutation L R) src dst =
      if ∀ u, dst (R u) = src (L u) then 1 else 0 := by
  classical
  have h : Routed (completePermutation L R) src dst ↔ ∀ u, dst (R u) = src (L u) := by
    constructor
    · intro routed u
      simpa only [completePermutation_active] using routed.2 (L u)
    · intro ok
      refine ⟨(completePermutation L R).bijective, fun i => ?_⟩
      by_cases hi : i ∈ Set.range L
      · obtain ⟨u, rfl⟩ := hi
        simpa only [completePermutation_active] using ok u
      · rw [completePermutation_idle L R i hi, hd _ (idleOrderIso L R ⟨i,hi⟩).property, hs i hi]
  simp only [taggedSwitch, h]

end
end ThreeFlat.Routing.CallPool

end OAI
