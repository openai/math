import OAI.Computability.BorderVNP.CoverLorentzSiteLoad

/-!
# Incidence concentration for the actual geodesic catalog

The old site count charges each original active wire at both ends. The
subdivided segment count charges each oriented hop once, in the tile of its
midpoint. The normalized ℓ² concentration of these actual counts grows by at
most the size of the fixed subdivision catalog.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cover.SiteRoutes

open BorderVNP.Crossing BorderVNP.Shortening Finset
open scoped Classical

variable {I : Type*} [Fintype I] {d D : ℕ} {L h : ℝ} {P R : Type*} {bits : P → ℕ}
  {p : Pack D P bits R} (r : SiteRoutes p I d L)

/-- The active wire indices, preserving distinct cables between the same two sites. -/
abbrev Active := {e : p.layout.Edge // r.active e}

/-- Width of the physical active wires incident at each site, counting both ends. -/
noncomputable def incidence (b : I → Deck (d+1)) : ℝ :=
  (∑ e : r.Active, if r.sourceAddress e.val = b then (p.layout.width e.val : ℝ) else 0) +
  ∑ e : r.Active, if reduceMove d (r.origin (p.layout.dst e.val)) = b then (p.layout.width e.val : ℝ) else 0

/-- The actual quotient tile of an oriented subsegment's midpoint. -/
noncomputable def segmentAddress (hh : 0 < h) (e : r.Active) (j : Fin (hopCount L h)) : I → Deck (d+1) :=
  productAddress d (productProjection (d+1) (translatePoint (r.origin (p.layout.src e.val))
    (framedHop hh (r.step e.val e.property,j)).center))

/-- Width of the subdivided segments binned by their actual geometric midpoint tiles. -/
noncomputable def midpointBits (hh : 0 < h) (b : I → Deck (d+1)) : ℝ :=
  ∑ e : r.Active, ∑ j : Fin (hopCount L h), if r.segmentAddress hh e j = b then (p.layout.width e.val : ℝ) else 0

/-- The initial `X` in the midpoint metric is bounded by the catalog size times the initial
`Xsite`. Both expressions use exactly the same level's tile-count normalization. -/
theorem initial_midpoint_concentration (hh : 0 < h) :
    Real.sqrt (Fintype.card (I → Deck (d+1))) * Real.sqrt (∑ b, (r.midpointBits hh b)^2) ≤
      Fintype.card (Hop I L h) * (Real.sqrt (Fintype.card (I → Deck (d+1))) *
        Real.sqrt (∑ b, (r.incidence b)^2)) := by
  classical
  let start (e : r.Active) := r.sourceAddress e.val
  let kind (e : r.Active) := r.step e.val e.property
  let w (e : r.Active) : ℝ := p.layout.width e.val
  let rows := sourceRows start kind w
  let offset (t : Hop I L h) := reduceMove d (centerCarry hh t)
  have hp : ∀ a s, 0 ≤ rows a s := sourceRows_nonneg start kind (fun e => Nat.cast_nonneg _)
  have hb (b : I → Deck (d+1)) : r.midpointBits hh b = slotMass rows offset b := by
    unfold midpointBits
    change _ = slotMass (sourceRows start kind w) offset b
    rw [slotMass_rows]
    apply sum_congr rfl
    intro e _
    apply sum_congr rfl
    intro j _
    have haddr : r.segmentAddress hh e j = start e * offset (kind e,j) := centerAddress _ _ _ _
    rw [haddr]
  have hsrc (a : I → Deck (d+1)) : sourceMass rows a ≤ r.incidence a := by
    change sourceMass (sourceRows start kind w) a ≤ _
    rw [sourceMass_rows]
    unfold incidence
    apply le_add_of_nonneg_right
    exact sum_nonneg (fun e _ => by split_ifs <;> positivity)
  have henergy := slotMass_energy rows offset hp
  have he : (∑ a, sourceMass rows a^2) ≤ ∑ a, r.incidence a^2 :=
    sum_le_sum (fun a _ => pow_le_pow_left₀ (sum_nonneg (fun s _ => hp a s)) (hsrc a) 2)
  have hz := Real.sqrt_le_sqrt (henergy.trans (mul_le_mul_of_nonneg_left he (sq_nonneg _)))
  rw [Real.sqrt_mul (sq_nonneg _),Real.sqrt_sq (Nat.cast_nonneg _)] at hz
  simp_rw [hb]
  rw [mul_left_comm]
  exact mul_le_mul_of_nonneg_left hz (Real.sqrt_nonneg _)

end Cover.SiteRoutes

end BorderVNP
end Computability
end OAI
