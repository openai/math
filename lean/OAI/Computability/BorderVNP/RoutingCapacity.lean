import OAI.Computability.BorderVNP.RoutingSchedule
import OAI.Computability.BorderVNP.PackedPotential

/-!
# Capacity of a physical team link

The common broadcast, both uses of the unordered team link, and the unused
zero bits all occupy the same block. The processor width in (7.2) is rounded
down before division among teams. These estimates retain both roundings.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Routing

open Filter TeamScales

private theorem fit_integer {r R t H : ℕ} (hr : 1 ≤ r) (hR : 2 < R)
    (hlink : 8 * R ≤ t / R) (hhead : 4 * H ≤ r * (t / R)) :
    H + 2 * (r * t / (64 * (R - 2)) + R) ≤ r * (t / R) := by
  let k := t / R
  let q := r * t / (64 * (R - 2))
  have hround : t < (k + 1) * R :=
    (Nat.div_lt_iff_lt_mul (by omega : 0 < R)).mp (Nat.lt_succ_self k)
  have hround' : t ≤ (2 * k) * R := by
    apply hround.le.trans (Nat.mul_le_mul_right R ?_)
    change 8 * R ≤ k at hlink
    omega
  have hden : 8 * R ≤ 64 * (R - 2) := by omega
  have hq := (Nat.mul_le_mul_left q hden).trans (Nat.div_mul_le_self (r*t) (64*(R-2)))
  have hq' : (4*q) * (2*R) ≤ (r*k) * (2*R) := by
    calc
      _ = q * (8 * R) := by ring
      _ ≤ r * t := hq
      _ ≤ r * (2 * k * R) := Nat.mul_le_mul_left r hround'
      _ = _ := by ring
  have hquarter : 4 * q ≤ r*k := Nat.le_of_mul_le_mul_right hq' (by omega)
  have hk : k ≤ r*k := Nat.le_mul_of_pos_left k hr
  change 4*H ≤ r*k at hhead
  change 8*R ≤ k at hlink
  change H + 2*(q + R) ≤ r*k
  omega

/-- Under the scale inequalities of §7, every team block has room for the
broadcast and both relay directions. The threshold is independent of the
number of processors per team and the contents of the demand lists. -/
theorem eventually_fit_block {α ξ : ℝ} (hξ : 0 ≤ ξ)
    (hgap : ξ + 2 * α < 1 / 25) :
    ∀ᶠ n : ℕ in atTop, ∀ (r R H : ℕ) (hR : 2 < R), 1 ≤ r →
      (R : ℝ) ≤ (n : ℝ) ^ (2 * α) → (H : ℝ) ≤ r * (n : ℝ) ^ (24 / 25 : ℝ) →
      ∀ width : Fin R → Fin R → ℕ, (∀ u, ∑ w, demand width u w ≤ exterior ξ r n / 64) →
      ∀ u v : Fin R, H + legLoad hR width u v + legLoad hR width v u ≤ r * link ξ R n := by
  have hb : 0 < 1 - ξ - 2 * α := by linarith
  have small := Packing.eventually_le_rounded_width
    (show 2 * α < 1 - ξ - 2 * α by linarith) hb zero_lt_one 8
  have head := Packing.eventually_le_rounded_width
    (show (24 / 25 : ℝ) < 1 - ξ - 2 * α by linarith) hb zero_lt_one 4
  filter_upwards [small, head, eventually_ge_atTop 1] with n hs hh hn
  intro r R H hR hr hteam hheader width budget u v
  have low := link_lower (ξ := ξ) hn (by omega : 0 < R) hteam
  rw [one_mul] at hs hh
  have hs' : 8 * R ≤ link ξ R n := by
    apply le_trans _ low
    exact_mod_cast (calc
      (8 : ℝ) * R ≤ 8 * (n : ℝ) ^ (2 * α) := by gcongr
      _ ≤ _ := hs)
  have hh' : 4 * H ≤ r * link ξ R n := by
    apply le_trans _ (Nat.mul_le_mul_left r low)
    exact_mod_cast (calc
      (4 : ℝ) * H ≤ 4 * (r * (n : ℝ) ^ (24 / 25 : ℝ)) := by gcongr
      _ = (r : ℝ) * (4 * (n : ℝ) ^ (24 / 25 : ℝ)) := by ring
      _ ≤ (r : ℝ) * TeamScales.width n (1 - ξ - 2 * α) := by gcongr)
  rw [Nat.add_assoc]
  exact (Nat.add_le_add_left (blockLoad_le hR width (exterior ξ r n) budget u v) H).trans
    (fit_integer hr hR hs' hh')

/-- An actual injection of used bit positions into the fixed-size processor
block; the complement is the zero padding in the local validators. -/
theorem physical_allocation {R : ℕ} (hR : 2 < R) (width : Fin R → Fin R → ℕ)
    (u v : Fin R) (H capacity : ℕ)
    (h : H + legLoad hR width u v + legLoad hR width v u ≤ capacity) :
    ∃ f : (Fin H ⊕ Hop hR width u v ⊕ Hop hR width v u) ↪ Fin capacity,
      (∀ i : Fin H, (f (.inl i)).val = i.val) ∧
      ∀ j : Hop hR width u v ⊕ Hop hR width v u, H ≤ (f (.inr j)).val := by
  let e := (Equiv.sumCongr (legEquiv hR width u v) (legEquiv hR width v u)).trans finSumFinEquiv
  have fit : H + (legLoad hR width u v + legLoad hR width v u) ≤ capacity := by
    simpa only [← Nat.add_assoc] using h
  let encode := (Equiv.sumCongr (Equiv.refl (Fin H)) e).trans finSumFinEquiv
  refine ⟨encode.toEmbedding.trans (Fin.castLEEmb fit), fun _ ↦ rfl, fun j ↦ ?_⟩
  exact Nat.le_add_right H (e j).val

end Routing

end BorderVNP
end Computability
end OAI
