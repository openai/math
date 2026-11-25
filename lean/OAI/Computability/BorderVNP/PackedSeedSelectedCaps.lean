import OAI.Computability.BorderVNP.PackedSeedBaseCaps

/-!
# The two final cell thresholds for the actual initialized grid

The numeric bounds already include the full native birth table and the
length of its opaque bit payload. They apply simultaneously to every
processor count in the allowed range and every chosen initial cover level.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.DeckGrid

open Cover CoverScale TeamScales Filter

/-- Both final thresholds and the input threshold with the published base
budgets substituted. The integral one-plus local-record counts are what
the geometric record recurrence propagates. -/
theorem eventually_seed_actual_caps {α τ : ℝ} (hα : 0 < α) (hα' : α < 1/1000) (hτ : 0 < τ)
    (ht : τ < α/100) {fan C : ℕ} (hfan : 1 ≤ fan) (hc : 1 ≤ C)
    (fanGrowth : τ*Real.logb 2 fan ≤ α) (growth : τ*Real.logb 2 C ≤ α/10)
    (q headerFactor : ℕ) [NeZero q] :
    ∃ ω : ℝ, 0 < ω ∧ ∀ᶠ n : ℕ in atTop, ∀ r : ℕ, 1 ≤ r → (r : ℝ) ≤ 2^((n:ℝ)^ω) →
      ∀ depth, depth+1 = initialDepth (Fin q) r n →
      let degree := Fintype.card (Direction q)
      let H := seedChannelWidth n r q depth
      let cap := seedBoxCapacity n r q depth degree
      let dB := seedDescriptionWidth n r q depth (headerFactor*logWidth r n) (BottomGridBank.bodyBudget cap)
      let b := width n α
      let T := epochs τ n
      let B := baseMass degree cap H b dB
      5*b*(C^T*seedPublicBase degree) ≤ width n (1/100) ∧
        7*(C^T*B) ≤ width n (1/5) ∧ B ≤ width n (1/5) := by
  let deg := Fintype.card (Direction q)
  let A := seedPublicBase deg + 12 + 810489*(11+2*deg)+(2*deg+1)+1
  obtain ⟨ω,hω,h⟩ := eventually_seed_sewn_caps hα hα' hτ ht hfan hc fanGrowth growth q deg headerFactor A
  refine ⟨ω,hω,?_⟩
  filter_upwards [h,eventually_ge_atTop 1] with n hn hn1
  intro r hr hm depth hd degree H cap dB b T B
  have hpos : 0 < b := by
    change 1 ≤ ⌊(n:ℝ)^α⌋₊
    exact Nat.le_floor (by simpa using (Real.one_le_rpow (by exact_mod_cast hn1) hα.le))
  obtain ⟨hp,he⟩ := baseMass_scale n r q depth degree b dB hpos
  exact hn r hr hm depth hd _ _ hp he

end Packing.DeckGrid

end BorderVNP
end Computability
end OAI
