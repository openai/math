import OAI.Computability.BorderVNP.CoverProductSamplesCount
import OAI.Computability.BorderVNP.ShortenPackHeckeLaw

/-!
# Spatial norm of the mean of whole-pack samples

On p. 20 the post-translation makes the tile marginal exactly uniform. Summing over
the relative bins therefore gives the same mean width in every tile, independently
of the pre-translation addresses or coincidences between the moving segments.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Hecke

open MeasureTheory Set Finset BorderVNP.Cover
open scoped Classical

variable {G I W B : Type*} [Group G] (Γ : Subgroup G) (z : G)
    [Fintype (Cosets (intersection Γ z))] [MeasurableSpace (Cosets Γ)]
    [Fintype I] [Fintype B] {d n : ℕ}

/-- Sum the exact finite-motion bin means over the fibers of a measurable relative
bin classifier. Every wire record contributes one bit divided by the number of tiles. -/
theorem sum_packBinCount_mean_bins (wire : Finset W) (x : W → Equiv.Perm I → I → G)
    (a : W → Equiv.Perm I → ProductSample Γ z I n → I → Deck d) (tile : I → Deck d)
    (code : W → Equiv.Perm I → (I → Cosets Γ) → B)
    (hc : ∀ e π b, MeasurableSet (code e π ⁻¹' {b})) :
    (∑ b, ∑ s : PackSample Γ z I d n, (packWeight Γ z s : ℝ) *
      (packBinCount Γ z wire x a tile (fun e π => code e π ⁻¹' {b}) s : ℝ)) =
      wire.card / Fintype.card (I → Deck d) := by
  have hb (b : B) := packBinCount_mean Γ z wire x a tile
    (fun e π => code e π ⁻¹' {b}) (fun e π => hc e π b)
  push_cast at hb
  simp_rw [hb, ← mul_sum]
  rw [sum_comm]
  have hwire (e : W) :
      (∑ b, ∑ π, (productLaw Γ z n (x e π)).toMeasure.real (code e π ⁻¹' {b})) =
        Fintype.card (Equiv.Perm I) := by
    rw [sum_comm]
    have hπ (π : Equiv.Perm I) :
        (∑ b, (productLaw Γ z n (x e π)).toMeasure.real (code e π ⁻¹' {b})) = 1 := by
      simpa using sum_measureReal_preimage_singleton (μ := (productLaw Γ z n (x e π)).toMeasure)
        univ (f := code e π) (fun b _ => hc e π b)
    simp_rw [hπ]
    simp
  simp_rw [hwire]
  simp only [sum_const, nsmul_eq_mul]
  have hp : (Fintype.card (Equiv.Perm I) : ℝ) ≠ 0 := by positivity
  have ht : (Fintype.card (I → Deck d) : ℝ) ≠ 0 := by positivity
  field_simp

/-- For any finite candidate distribution, a uniform independent post-translation
gives exactly `1 / card T` mass in each tile. The carry and the relative bin may
both depend on the candidate. -/
theorem candidate_tile_marginal {M T : Type*} [Fintype M] [Group T] [Fintype T]
    (prob : M → ℝ) (hp : ∑ c, prob c = 1) (carry : M → T) (relative : M → B) (tile : T) :
    (∑ b : B, ∑ c, ∑ h : T, if (h * carry c, relative c) = (tile,b)
      then prob c / Fintype.card T else 0) = 1 / Fintype.card T := by
  rw [sum_comm]
  have hc (c : M) :
      (∑ b : B, ∑ h : T, if (h * carry c, relative c) = (tile,b)
        then prob c / Fintype.card T else 0) = prob c / Fintype.card T := by
    rw [sum_comm]
    have hh (h : T) :
        (∑ b : B, if (h * carry c, relative c) = (tile,b) then prob c / Fintype.card T else 0) =
          if h * carry c = tile then prob c / Fintype.card T else 0 := by
      by_cases he : h * carry c = tile <;> simp [Prod.mk.injEq, he]
    simp_rw [hh]
    calc
      _ = ∑ h : T, if h = tile then prob c / Fintype.card T else 0 :=
        Equiv.sum_comp (Equiv.mulRight (carry c)) _
      _ = _ := by simp
  simp_rw [hc]
  rw [← sum_div, hp]

end Hecke

namespace Shortening.PackMotions

open Cover Cover.Frame Hecke Epoch Crossing Packing MeasureTheory Set Finset
open scoped Classical BigOperators

variable {D copies : ℕ} {P : Type} {bits : P → ℕ} {K : Type*} {B I : Type} [Fintype I] [Fintype B]
variable (input : Fin copies → Pack D P bits K) (charged : ∀ i, (input i).layout.Edge → Bool)
section Candidates

variable {M T : Type} [Fintype M] [Group T] [Fintype T]
variable (tag : ∀ i, M × T → (input i).layout.Edge → Option (T × B))
variable (prob : Fin copies → M → ℝ) (carry : Active input charged → M → T)
variable (relative : Active input charged → M → B)

/-- Arbitrary pack-specific candidate distributions with uniform post-translation
give the same exact spatial mean of the actual charged-width tables. -/
theorem candidateBinMean_tile_mass (t : T) (hp : ∀ i, ∑ c, prob i c = 1)
    (hmask : ∀ i s e, (tag i s e).isSome = charged i e)
    (htag : ∀ (w : Active input charged) c h,
      tag w.1 (c,h) w.2.val = some (h * carry w c, relative w c)) :
    (∑ b, binMean input tag (fun i s => prob i s.1 / Fintype.card T) (t,b)) =
      (∑ w : Active input charged, normalizedWidth input charged w) / Fintype.card T := by
  rw [binMean_eq_binCounts input charged _ _ hmask]
  simp only [binCounts]
  rw [sum_comm]
  have hm (w : Active input charged) :
      (∑ b, finiteWireLaw input charged tag (fun i s => prob i s.1 / Fintype.card T) w (t,b)) =
        1 / Fintype.card T := by
    simp only [finiteWireLaw, Fintype.sum_prod_type, htag, Option.some.injEq]
    exact candidate_tile_marginal (prob w.1) (hp w.1) (carry w) (relative w) t
  simp_rw [← mul_sum, hm]
  rw [← sum_mul]
  ring

/-- Uniform post-translation bounds the normalized spatial norm for any finite
candidate distribution, allowing distinct distributions for different packs. -/
theorem candidateBinMean_norm_le_width (hpos : ∀ i c, 0 ≤ prob i c) (hp : ∀ i, ∑ c, prob i c = 1)
    (hmask : ∀ i s e, (tag i s e).isSome = charged i e)
    (htag : ∀ (w : Active input charged) c h,
      tag w.1 (c,h) w.2.val = some (h * carry w c, relative w c)) :
    Real.sqrt (Fintype.card T) *
      Real.sqrt (binEnergy (binMean input tag (fun i s => prob i s.1 / Fintype.card T))) ≤
      ∑ w : Active input charged, normalizedWidth input charged w := by
  apply uniform_tile_mean_norm
  · intro t b
    unfold binMean motionMean
    exact div_nonneg (sum_nonneg fun i _ => sum_nonneg fun s _ => mul_nonneg
      (div_nonneg (hpos i s.1) (Nat.cast_nonneg _)) (Nat.cast_nonneg _)) (Nat.cast_nonneg _)
  · exact sum_nonneg fun w _ => by unfold normalizedWidth; positivity
  · intro t
    exact (candidateBinMean_tile_mass input charged tag prob carry relative t hp hmask htag).le

end Candidates

variable {depth n : ℕ} (speed : Active input charged → I → ℝ)
variable (code : Active input charged → HyperbolicHost I × PiLp 2 (fun _ : I => ℂ) → B)
variable (frame : Active input charged → Equiv.Perm I → I → SL)
variable (carry : Active input charged → Equiv.Perm I → ProductSample (lattice 1) elliptic I n → I → Deck depth)
variable (hc : ∀ w b, MeasurableSet (code w ⁻¹' {b}))
include hc

/-- The actual finite sample's relative-bin masses sum to one tile's share of the
single-wire distribution. This applies `packBinCount_mean` to the one-wire record. -/
theorem sampledWire_tile_mass (w : Active input charged) (t : I → Deck depth) :
    (∑ b : B, finiteWireLaw input charged (sampledBin input charged speed code frame carry)
      (sampleProb depth n) w (t,b)) = 1 / Fintype.card (I → Deck depth) := by
  let f := fun (_ : Unit) π y => code w (segmentChart (speed w) π y)
  have hm (e : Unit) π b : MeasurableSet (f e π ⁻¹' {b}) :=
    (hc w b).preimage (segmentChart_preserving (speed w) π).measurable
  have h := sum_packBinCount_mean_bins (lattice 1) elliptic ({()} : Finset Unit)
    (fun _ => frame w) (fun _ => carry w) t f hm
  simp only [Finset.card_singleton, Nat.cast_one] at h
  rw [← h]
  apply sum_congr rfl
  intro b _
  rw [finiteWireLaw_eq_actualBinMass, actualBinMass]
  apply sum_congr rfl
  intro s _
  congr 1
  simp only [packBinCount, natCast_card_filter, sum_singleton, Set.indicator_apply,
    Set.mem_preimage, Set.mem_singleton_iff, Pi.one_apply, f]
  split_ifs <;> simp_all

/-- The exact tile marginal of the mean in (6.2), including the widths of every
active cable in each input and the normalization by the number of inputs. -/
theorem sampledBinMean_tile_mass (t : I → Deck depth) :
    (∑ b, binMean input (sampledBin input charged speed code frame carry) (sampleProb depth n) (t,b)) =
      (∑ w : Active input charged, normalizedWidth input charged w) / Fintype.card (I → Deck depth) := by
  rw [binMean_eq_binCounts input charged _ _ (sampledBin_mask input charged speed code frame carry)]
  simp only [binCounts]
  rw [sum_comm]
  simp_rw [← mul_sum, sampledWire_tile_mass input charged speed code frame carry hc]
  rw [← sum_mul]
  ring

/-- The true `binMean` satisfies the tile-normalized Euclidean bound used in (6.3). -/
theorem sampledBinMean_norm_le_width :
    Real.sqrt (Fintype.card (I → Deck depth)) * Real.sqrt
      (binEnergy (binMean input (sampledBin input charged speed code frame carry) (sampleProb depth n))) ≤
      ∑ w : Active input charged, normalizedWidth input charged w := by
  apply uniform_tile_mean_norm
  · intro t b
    unfold binMean motionMean
    exact div_nonneg (sum_nonneg fun i _ => sum_nonneg fun s _ => mul_nonneg
      ((sampleProb_probability (I := I) depth n i).1 s).le (Nat.cast_nonneg _)) (Nat.cast_nonneg _)
  · exact sum_nonneg fun w _ => by unfold normalizedWidth; positivity
  · intro t
    exact (sampledBinMean_tile_mass input charged speed code frame carry hc t).le

/-- A positive minimum segment length turns the total width bound into the
normalized charged-length estimate on p. 20. -/
theorem sampledBinMean_norm_le_length (wireLength : Active input charged → ℝ)
    {ellMin : ℝ} (hmin : 0 < ellMin) (hl : ∀ w, ellMin ≤ wireLength w) :
    Real.sqrt (Fintype.card (I → Deck depth)) * Real.sqrt
      (binEnergy (binMean input (sampledBin input charged speed code frame carry) (sampleProb depth n))) ≤
      (∑ w : Active input charged, normalizedWidth input charged w * wireLength w) / ellMin := by
  apply (sampledBinMean_norm_le_width input charged speed code frame carry hc).trans
  rw [le_div_iff₀ hmin, sum_mul]
  exact sum_le_sum fun w _ => mul_le_mul_of_nonneg_left (hl w) (by unfold normalizedWidth; positivity)

/-- The actual mean estimate with the charged length of the moved disjoint union
itself on the right, for every simultaneous choice of the pack motions. -/
theorem sampledBinMean_norm_le_chargedLength {Q : Type*} [PseudoMetricSpace Q]
    (place : ∀ i, PackSample (lattice 1) elliptic I depth n → (input i).layout.Site → Q)
    (ω : Fin copies → PackSample (lattice 1) elliptic I depth n)
    (wireLength : Active input charged → ℝ) {ellMin : ℝ} (hmin : 0 < ellMin)
    (hl : ∀ w, ellMin ≤ wireLength w)
    (hmove : ∀ (w : Active input charged) m, dist (place w.1 m ((input w.1).layout.src w.2.val))
      (place w.1 m ((input w.1).layout.dst w.2.val)) = wireLength w) :
    Real.sqrt (Fintype.card (I → Deck depth)) * Real.sqrt
      (binEnergy (binMean input (sampledBin input charged speed code frame carry) (sampleProb depth n))) ≤
      chargedLength (parallelPacks input).layout (fun v => place v.1 (ω v.1) v.2)
        (fun e => (jointBin input (sampledBin input charged speed code frame carry) ω e).isSome) /
          copies / ellMin := by
  rw [normalized_joint_length input charged _ place ω wireLength
    (sampledBin_mask input charged speed code frame carry) hmove]
  exact sampledBinMean_norm_le_length input charged speed code frame carry hc wireLength hmin hl

end Shortening.PackMotions

end BorderVNP
end Computability
end OAI
