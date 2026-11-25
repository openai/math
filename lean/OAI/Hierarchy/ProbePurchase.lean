import OAI.Hierarchy.ProbeScore

namespace OAI
/-! # Paying for an entire family of tile-disjoint probe purchases -/

namespace Hierarchy.AdaptiveProbe
open scoped BigOperators
noncomputable section

variable {I G : Type*} [Fintype I] [Fintype G] {H : ℕ}

/-- Only the accurate probe roots are needed for the saving. Their chains
use distinct coordinates in the common price array, and all purchases,
including the inaccurate ones, are charged. -/
theorem purchase_net_gain (slot : G × Fin H ↪ I) (a M s β u δ η fee : ℝ)
    (purchases : ℕ) (b x y : I → ℝ) (z : G → ℕ → ℝ)
    (ha : 0≤a) (hs : 0≤s) (hs₁ : s≤1) (hβ : 0≤β) (hb : ∀ i, 0≤b i)
    (calibrate : 4*δ^2≤u) (resolution : η<δ) (long : 1+η < (H:ℝ)*(δ-η))
    (weight : ∀ g j, β≤b (slot (g,j)))
    (mark : ∀ g j, u ≤ s*(rise M (x (slot (g,j))))^2)
    (read : ∀ g (j : Fin H), |rise M (y (slot (g,j))) -
      max (z g (j.val+1) - z g j.val) 0| ≤ η)
    (ends : ∀ g, z g H - z g 0 ≤ 1+η) :
    (Fintype.card G : ℝ)*(β*u/8) - (purchases : ℝ)*fee ≤
    (s/2)*divergence a M b x y - (purchases : ℝ)*fee := by
  classical
  have large (g : G) (j : Fin H) : 2*δ ≤ rise M (x (slot (g,j))) := by
    let t := rise M (x (slot (g,j)))
    have h₁ : s*t^2 ≤ t^2 := by simpa using mul_le_mul_of_nonneg_right hs₁ (sq_nonneg t)
    have h₂ := calibrate.trans ((mark g j).trans h₁)
    have ht : 0 ≤ t := rise_nonneg _ _
    change 2*δ ≤ t
    by_contra! lt
    nlinarith only [h₂, mul_pos (sub_pos.mpr lt) (by linarith : 0<2*δ+t)]
  choose drop hd using fun g => chain_drop H resolution long (z g)
    (fun j => rise M (x (slot (g,j)))) (fun j => rise M (y (slot (g,j))))
    (large g) (read g) (ends g)
  let name : G ↪ I := ⟨fun g => slot (g,drop g), fun _ _ h => congrArg Prod.fst (slot.injective h)⟩
  let picks := Finset.univ.map name
  have hit {i} (hi : i ∈ picks) : ∃ g, name g=i := by simpa [picks] using hi
  have gained := purchased_divergence a M s β u b x y ha hs hβ hb picks
    (fun i hi => by obtain ⟨g,rfl⟩ := hit hi; exact weight g _)
    (fun i hi => by obtain ⟨g,rfl⟩ := hit hi; exact mark g _)
    (fun i hi => by obtain ⟨g,rfl⟩ := hit hi; exact hd g)
  apply sub_le_sub_right _ _
  simpa [picks] using gained

/-- With one unit `C/n` of saving on every accurate chain and a fee of
at most half a unit on every purchase, a positive density gives uniform
strict surplus after discarding a sufficiently small exceptional set. -/
theorem positive_purchase_surplus {n chains bad reward fee ρ realized : ℝ}
    (hn : 0<n) (hρ : 0<ρ) (hr : 0<reward) (many : ρ*n ≤ chains)
    (few : bad ≤ ρ*n/4) (cheap : fee ≤ reward/(2*n))
    (account : (chains-bad)*(reward/n)-chains*fee ≤ realized) :
    0 < ρ*reward/4 ∧ ρ*reward/4 ≤ realized := by
  refine ⟨by positivity, le_trans ?_ account⟩
  have hchains : 0 ≤ chains := (mul_nonneg hρ.le hn.le).trans many
  have fee_le := mul_le_mul_of_nonneg_left cheap hchains
  have count := mul_le_mul_of_nonneg_right many (div_nonneg hr.le hn.le)
  have exc := mul_le_mul_of_nonneg_right few (div_nonneg hr.le hn.le)
  field_simp [hn.ne'] at fee_le count exc ⊢
  nlinarith only [fee_le,mul_le_mul_of_nonneg_right count hr.le,
    mul_le_mul_of_nonneg_right exc hr.le]

end
end Hierarchy.AdaptiveProbe

end OAI
