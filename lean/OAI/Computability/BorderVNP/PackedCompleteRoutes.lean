import OAI.Computability.BorderVNP.DiagonalExternalSewVolume
import OAI.Computability.BorderVNP.PackedTerminalPhysical

/-! # Accounting for every cable that crosses a physical cell boundary -/

namespace OAI
namespace Computability
namespace BorderVNP

open Cover Crossing Epoch Shortening
open scoped Classical BigOperators

variable {D d : ℕ} {P I : Type} [Fintype I] {K : Type*} {bits : P → ℕ} {L : ℝ}

/-- Every cable with different reduced endpoint addresses is active on this route. -/
def Cover.SiteRoutes.CoversCrossings {p : Pack D P bits K} (s : SiteRoutes p I d L) : Prop :=
  ∀ c, reduceMove d (s.origin (p.layout.src c)) ≠ reduceMove d (s.origin (p.layout.dst c)) → s.active c

/-- The active mask is precisely the set of cables between different reduced endpoint addresses. -/
def Cover.SiteRoutes.ExactCrossings {p : Pack D P bits K} (s : SiteRoutes p I d L) : Prop :=
  ∀ c, s.active c ↔ reduceMove d (s.origin (p.layout.src c)) ≠ reduceMove d (s.origin (p.layout.dst c))

/-- All cables with distinct surface endpoints belong to the physical charge mask. -/
def Shortening.PlacedPack.CoversCrossings (p : PlacedPack D P bits K I d) : Prop :=
  ∀ c, p.site (p.pack.layout.src c) ≠ p.site (p.pack.layout.dst c) → p.charged c

/-- For an exact boundary the sum of all crossing cable widths is precisely the measured nonlocal width. -/
theorem Cover.SiteRoutes.intercellWidth_eq {p : Pack D P bits K} (s : SiteRoutes p I d L)
    (mask : s.ExactCrossings) :
    (Diagonal.ExternalSew.intercellWidth p.layout (fun v => reduceMove d (s.origin v)) : ℝ) = s.nonlocalWidth := by
  unfold Diagonal.ExternalSew.intercellWidth testedWidth SiteRoutes.nonlocalWidth
  push_cast
  apply Finset.sum_congr rfl
  intro c _
  by_cases h : s.active c
  · simp [h,(mask c).mp h]
  · simp [h,mt (mask c).mpr h]

/-- On a complete route the measured active width pays for all actual cables that cross its cells. -/
theorem Cover.SiteRoutes.intercellWidth_le {p : Pack D P bits K} (s : SiteRoutes p I d L)
    (complete : s.CoversCrossings) :
    (Diagonal.ExternalSew.intercellWidth p.layout (fun v => reduceMove d (s.origin v)) : ℝ) ≤ s.nonlocalWidth := by
  unfold Diagonal.ExternalSew.intercellWidth testedWidth SiteRoutes.nonlocalWidth
  push_cast
  apply Finset.sum_le_sum
  intro c _
  by_cases h : reduceMove d (s.origin (p.layout.src c)) ≠ reduceMove d (s.origin (p.layout.dst c))
  · simp [h,complete c h]
  · simp only [h,ite_false]
    split_ifs <;> positivity

end BorderVNP
end Computability
end OAI
