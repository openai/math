import OAI.Computability.BorderVNP.ShortenPlacedStep
import OAI.Computability.BorderVNP.ShortenEpochRoundInitial

/-!
# Starting a physical epoch at the actual subdivided site pack

The initial midpoint of each charged subsegment is the projection of its
catalog frame center. Only positive-length segments enter the population
used by the combining step.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cover.SiteRoutes

open BorderVNP.Shortening BorderVNP.Shortening.CombiningStep BorderVNP.Epoch BorderVNP.Crossing Finset
open scoped Classical

variable {D d : ℕ} {I P : Type} [Fintype I] {R : Type*} [CommSemiring R]
  {bits : P → ℕ} {L h : ℝ} {p : Pack D P bits R} (s : SiteRoutes p I d L)

/-- The physical input pack, with its true retained sites and translated catalog midpoints. -/
noncomputable def initialPlacedPack (hh : 0 < h) : PlacedPack D P bits R I d where
  pack := s.subdivided h
  site := s.physical h
  charged e := s.active e.1
  midpoint e := if he : s.active e.1 then productProjection (d+1)
    (translatePoint (s.origin (p.layout.src e.1)) (framedHop hh
      (s.step e.1 he,⟨e.2.val,s.hop_index he e.2⟩)).center)
    else surfaceMidpoint (s.physical h ((s.subdivided h).layout.src e)) (s.physical h ((s.subdivided h).layout.dst e))

private theorem pop_le (hh : 0 < h) (t : I → Deck (d+1)) :
    (testedWidth (s.initialPlacedPack hh).pack.layout.width ((s.initialPlacedPack hh).occupies t) : ℝ) ≤
      s.midpointBits hh t := by
  classical
  let F (e : p.layout.Edge) := if he : s.active e then
    ∑ j : Fin (hopCount L h), if s.segmentAddress hh ⟨e,he⟩ j = t then (p.layout.width e : ℝ) else 0 else 0
  have hF : (∑ e, F e) = s.midpointBits hh t := by
    rw [← Fintype.sum_subtype_add_sum_subtype (p := fun e => s.active e = true) F]
    have hn : (∑ e : {e // ¬ s.active e = true}, F e.val) = 0 :=
      sum_eq_zero (fun e _ => by simp [F,e.property])
    rw [hn,add_zero]
    apply sum_congr rfl
    intro e _
    simp [F,e.property]
  rw [← hF]
  unfold testedWidth
  push_cast
  change (∑ x : Σ e, Fin ((s.routes h).interior e + 1), if (s.initialPlacedPack hh).occupies t x then (p.layout.width x.1 : ℝ) else 0) ≤ _
  rw [Fintype.sum_sigma]
  apply sum_le_sum
  intro e _
  by_cases he : s.active e
  · have hn : (s.routes h).interior e + 1 = hopCount L h := by simp [routes,he,hopCount]
    simp only [F,he,reduceDIte]
    rw [← Equiv.sum_comp (finCongr hn) (fun j => if s.segmentAddress hh ⟨e,he⟩ j = t then (p.layout.width e : ℝ) else 0)]
    apply sum_le_sum
    intro j _
    by_cases ho : (s.initialPlacedPack hh).occupies t ⟨e,j⟩
    · have ht := ho.2.2
      change productTileName d (if hh' : s.active e then _ else _) = t at ht
      simp only [he,reduceDIte] at ht
      have haddr : s.segmentAddress hh ⟨e,he⟩ (finCongr hn j) = t := ht
      change (if (s.initialPlacedPack hh).occupies t ⟨e,j⟩ then (p.layout.width e : ℝ) else 0) ≤
        (if s.segmentAddress hh ⟨e,he⟩ (finCongr hn j) = t then (p.layout.width e : ℝ) else 0)
      simp only [ho,haddr,ite_true,le_refl]
    · simp [ho]
      split_ifs <;> positivity
  · simp only [F,he]
    have hn (j : Fin ((s.routes h).interior e + 1)) : ¬(s.initialPlacedPack hh).occupies t ⟨e,j⟩ :=
      fun hh' => he hh'.1
    simp [hn]

/-- Actual input coordinates for the recurrence. The input tensor is exactly the
site pack tensor. The initial concentration omits any geometrically coincident edge. -/
theorem initial_placed_bounds (hh : 0 < h) (hL : 0 ≤ L) {weight M : ℝ} (hw : 0 < weight)
    (hM : s.potential weight ≤ M) :
    (s.initialPlacedPack hh).pack.tensor = p.tensor ∧ (s.initialPlacedPack hh).length ≤ M*L ∧
    (s.initialPlacedPack hh).concentration ≤ M * (Fintype.card (Hop I L h) / weight) := by
  obtain ⟨hlen,hx⟩ := s.initial_for_recurrence hh hL hw hM
  refine ⟨s.tensor_subdivided h,hlen,le_trans ?_ hx⟩
  apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
  apply Real.sqrt_le_sqrt
  exact sum_le_sum (fun t _ => pow_le_pow_left₀ (Nat.cast_nonneg _) (s.pop_le hh t) 2)

end Cover.SiteRoutes

end BorderVNP
end Computability
end OAI
