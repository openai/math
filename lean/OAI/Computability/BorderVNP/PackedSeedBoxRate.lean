import OAI.Computability.BorderVNP.PackedSeedTapeRate
import OAI.Computability.BorderVNP.PackedBottomBoxBits
import OAI.Computability.BorderVNP.CellVisitWidth

/-! # Fixed common header and immutable body lengths for the original private tapes

The scalar field count of the body is linear in the initial fine-site and channel capacities.
Every wire operand is relative to this site. Its binary length therefore fits the ordinary
machine width uniformly in the number of processors.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.DeckGrid

open Cover CoverScale TeamScales Filter Diagonal.ExternalSew
open private batch_mono from OAI.Computability.BorderVNP.PackedSeedTapeRate

/-- Capacity of the private one-copy tape's relative addresses and its stored fine factors.
The incoming bank counts both ends of each possible directed channel and the single grouped port. -/
noncomputable def seedBoxCapacity (n r q depth degree : ℕ) :=
  5*seedSiteCapacity n r q depth + GridHosts.inputBlockWidth r n q depth +
    2*degree*seedChannelWidth n r q depth

/-- The actual padded route budget controls all relative indices in the one-copy body. -/
theorem seedBoxCapacity_le (n r q depth degree : ℕ) :
    seedBoxCapacity n r q depth degree ≤ (11+2*degree)*seedChannelWidth n r q depth := by
  have h := seed_capacity_le n r q depth
  unfold seedBoxCapacity
  nlinarith only [Nat.mul_le_mul_left 5 h.2,h.1]

private theorem box_bounds {n r q depth degree : ℕ} (hn : 8 ≤ n) (hr : 1 ≤ r)
    (cap : seedBoxCapacity n r q depth degree ≤ n) :
    BottomGridBank.bodyBudget (seedBoxCapacity n r q depth degree) ≤
      (4*(1+19*(11+2*degree)))*(seedChannelWidth n r q depth+1)*logWidth r n := by
  let C := seedChannelWidth n r q depth
  let K := seedBoxCapacity n r q depth degree
  let L := logWidth r n
  have bits := (Nat.size_le_size (max_le hn cap)).trans (CellMacro.Generator.size_le_logWidth n r hr)
  have length : 1 ≤ L := by
    rw [show L = Nat.clog 2 (2*n*r) from Shortening.PublicCapacity.public_logWidth ..]
    exact (show 1 = Nat.clog 2 2 by decide).le.trans (Nat.clog_mono_right 2 (by nlinarith))
  have hcap := seedBoxCapacity_le n r q depth degree
  change K ≤ (11+2*degree)*C at hcap
  have hbase : 1+19*K ≤ (1+19*(11+2*degree))*(C+1) := by nlinarith only [hcap]
  have hbits : 2*(max 8 K).size+2 ≤ 4*L := by change (max 8 K).size ≤ L at bits; omega
  exact (Nat.mul_le_mul hbase hbits).trans_eq (by ring)

/-- Instantiate the original tape rate with the actual length formula for the stored
one-copy Boolean factors and the three-field weighted-occurrence sidecar. Both the
individual two-processor delivery and the simultaneous storage of every original site
hold for one common width fixed solely by the dimensions. -/
theorem eventually_padded_seed_description {α τ : ℝ} (hα : 0 < α) (hα' : α < 1/1000) (hτ : 0 < τ)
    (hτ' : τ < α/100) (q degree headerFactor : ℕ) [NeZero q] :
    ∃ ω B : ℝ, 0 < ω ∧ 0 ≤ B ∧ ∀ᶠ n : ℕ in atTop, ∀ r : ℕ, 1 ≤ r →
      (r:ℝ) ≤ 2^((n:ℝ)^ω) → ∀ depth : ℕ, depth+1 = initialDepth (Fin q) r n →
      let H := headerFactor*logWidth r n
      let cap := seedBoxCapacity n r q depth degree
      let dB := seedDescriptionWidth n r q depth H (BottomGridBank.bodyBudget cap)
      let V := GridHosts.tileCount q depth
      cap ≤ n ∧ (dB:ℝ) ≤ B*(n:ℝ)^(1/10+τ/20)*(logWidth r n:ℝ)^4 ∧
        ((V*dB : ℕ):ℝ) ≤ B*volume τ r n*(logWidth r n:ℝ)^4 ∧ dB ≤ literal α n/2 ∧
        ∀ K, K^epochs τ n * V * dB ≤ teams α τ K n*r*(literal α n/2) := by
  obtain ⟨u,hu,tapes⟩ := eventually_seed_tapes hα hα' hτ hτ' q 1
  let A := max headerFactor (4*(1+19*(11+2*degree)))
  obtain ⟨B,hB,rates⟩ := tapes A
  obtain ⟨v,hv,seed⟩ := eventually_seed_capacity q hτ
  obtain ⟨w,hw,poly⟩ := exists_polylog_budget 3 (show (0:ℝ)<1/10 by norm_num)
  let ω := min (min u v) w
  let C : ℝ := (11+2*(degree:ℝ))*((96*(4*q+1)+1:ℝ)*factor (Fin q))
  have hg := eventually_rpow_gap (show 1/10+τ/20+1/10 < (1:ℝ) by linarith) C
  refine ⟨ω,B,lt_min (lt_min hu hv) hw,hB,?_⟩
  filter_upwards [rates,seed,poly,hg,eventually_ge_atTop 8] with n rateN seedN polyN absorb hn
  intro r hr rmax depth hd H cap dB V
  have hn1 : 1 ≤ n := by omega
  have hn0 : 0 < (n:ℝ) := by exact_mod_cast (show 0<n by omega)
  have sm := (seedN r hr (batch_mono hn1 ((min_le_left _ _).trans (min_le_right _ _)) rmax) depth hd).1
  have log := polyN r hr (batch_mono hn1 (min_le_right _ _) rmax)
  have capBound : cap ≤ n := by
    apply (Nat.cast_le (α:=ℝ)).mp
    calc
      (cap:ℝ) ≤ (11+2*(degree:ℝ))*seedChannelWidth n r q depth := by exact_mod_cast seedBoxCapacity_le n r q depth degree
      _ ≤ C*(n:ℝ)^(1/10+τ/20)*(n:ℝ)^(1/10:ℝ) := by
        apply (mul_le_mul_of_nonneg_left sm (by positivity : 0 ≤ 11+2*(degree:ℝ))).trans
        dsimp only [C]
        calc
          _ = ((11+2*(degree:ℝ))*((96*(4*q+1)+1:ℝ)*factor (Fin q))*(n:ℝ)^(1/10+τ/20))*(logWidth r n:ℝ)^3 := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_left log (by positivity)
      _ = C*(n:ℝ)^(1/10+τ/20+1/10) := by rw [Real.rpow_add hn0 (1/10+τ/20) (1/10)]; ring
      _ ≤ _ := by simpa only [Real.rpow_one] using absorb
  have head : H ≤ A*(logWidth r n)^1 := by
    rw [pow_one]
    exact Nat.mul_le_mul_right _ (le_max_left ..)
  have body : BottomGridBank.bodyBudget cap ≤ A*(seedChannelWidth n r q depth+1)*(logWidth r n)^1 := by
    rw [pow_one]
    exact (box_bounds hn hr capBound).trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (le_max_right ..)))
  have run := rateN r hr (batch_mono hn1 ((min_le_left _ _).trans (min_le_left _ _)) rmax) depth hd H
    (BottomGridBank.bodyBudget cap)
  have one := run 1 head body
  exact ⟨capBound,one.1,one.2.1,one.2.2.1,fun K => (run K head body).2.2.2⟩

end Packing.DeckGrid

end BorderVNP
end Computability
end OAI
