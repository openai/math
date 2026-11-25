import OAI.Computability.BorderVNP.DiagonalPowerWords

/-! # Reading a single fine unary site as a one-bit power word -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal.CellEntries.PowerSites

open Crossing
open scoped BigOperators Classical

variable {D b : ℕ} {P : Type*} {bits : P → ℕ} {N : Network D P bits}
    {Team Param Gadget : Type*} [Fintype Team] [Fintype Param] {tags : N.Tables (Entry Param Gadget)}
    (sites : PowerSites Team Param Gadget b N tags)

/-- Before any boxes are merged, each named site selects only its unique
occurrence, exactly when its fine parameter tally is nonzero. -/
noncomputable def toWords : PowerWords Team Param Gadget b N tags where
  site := sites.site
  selected v z x w := decide (sites.site w = v ∧ (counters (tags v z x)).1 ≠ 0)
  located v z x w h := (of_decide_eq_true h).1
  exact v z x := by
    by_cases hz : (counters (tags v z x)).1 = 0
    · simp [hz]
    obtain ⟨w,rfl⟩ : v ∈ Set.range sites.site :=
      by_contra fun hv => hz (sites.other v hv z x)
    have hw := (sites.named w z x).resolve_left hz
    conv_lhs => rw [hw]
    symm
    calc
      _ = slotPower w (decide (sites.site w = sites.site w ∧ (counters (tags (sites.site w) z x)).1 ≠ 0)) := by
        apply Finset.sum_eq_single w
        · intro u _ hu
          have hne : sites.site u ≠ sites.site w := sites.site.injective.ne hu
          simp [hne]
        · simp
      _ = Finsupp.single w.2.1 (2 ^ w.2.2.val) := by simp [hz, slotPower]

end Diagonal.CellEntries.PowerSites

end BorderVNP
end Computability
end OAI
