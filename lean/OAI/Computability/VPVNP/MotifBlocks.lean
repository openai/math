import OAI.Computability.VPVNP.MotifBase

/-!
# Fixed block of wire identities for all demand widths

Theorem 6.1 of *VP and VNP differ over every field* chooses its rational
grids, common denominator multiple, tensor power, selector size and local
maps before seeing the demand widths. Only the rounded grid point, number of
repetitions and payload change with the widths. The energy error is uniform.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace MotifBlocks

open MotifGrid MotifBase WireTensor

universe u v
variable {k : Type u} [Field k] {J : Type v} [Fintype J]
variable {D S : Type} [Fintype D] [Fintype S]

/-- Data fixed before the demand widths are supplied, including the local
base identities and the global additive error in the width energy. -/
structure FixedBlock (k : Type u) [Field k] (a b : D → J) (P : MotifSelector.Supply J S)
    (p : D → ℝ) (q : S → ℝ) (H H' : ℝ) where
  /-- Positive rational radius bounding the supply-width grid. -/
  radius : ℚ
  radius_pos : 0 < radius
  /-- Strict demand and supply grids for the chosen masses, spectral comparison, and radius. -/
  grid : StrictGrids p q H (radius : ℝ)
  /-- Common positive multiplier used with the grid denominator to obtain integer wire widths. -/
  multiple : ℕ
  /-- Positive tensor power used in the fixed base identities. -/
  power : ℕ
  /-- Number of summands indexed by the copy selector in each base identity. -/
  copyCount : ℕ
  multiple_pos : 0 < multiple
  power_pos : 0 < power
  copyCount_pos : 0 < copyCount
  baseIdentity : ∀ z : grid.demands, BaseIdentity k a b P.src P.dst
    (grid.demandWidths multiple z) (grid.supplyWidths multiple) copyCount power
  base_payload_le : ∀ σ : Fin power → grid.supplies,
    widthNorm q (fun i ↦ (payload (grid.supplyWidths multiple) σ i : ℝ)) ≤
      (power * (multiple * grid.denominator) : ℕ) * radius
  select : ∀ w : D → ℕ, ∃ z : grid.demands, ∀ i,
    w i ≤ MotifWidths.copies (widthNorm p (fun j ↦ (w j : ℝ)))
      (power * (multiple * grid.denominator)) *
      (power * grid.demandWidths multiple z i)
  /-- Uniform additive constant in the squared supply-energy bound after selector padding. -/
  energyConstant : ℝ
  padded_energy_le : ∀ (w : D → ℕ) (v : S → ℕ),
    let L := power * (multiple * grid.denominator)
    let s := MotifWidths.selectorBits copyCount grid.supplies.card power
    let N := widthNorm p (fun i ↦ (w i : ℝ))
    let u := MotifWidths.copies N L
    widthNorm q (fun i ↦ (v i : ℝ)) ≤ (u : ℝ) * L * radius →
    widthNorm q (fun i ↦ (v i + u * s : ℕ)) ^ 2 ≤ H' * N ^ 2 + energyConstant

namespace FixedBlock

variable {a b : D → J} {P : MotifSelector.Supply J S} {p : D → ℝ} {q : S → ℝ} {H H' : ℝ}
variable (B : FixedBlock k a b P p q H H')

/-- Width scale of one fixed base identity. -/
def scale : ℕ := B.power * (B.multiple * B.grid.denominator)

/-- Bits used to choose a direct-sum copy and the supply profile in each factor. -/
def selectorBits : ℕ := MotifWidths.selectorBits B.copyCount B.grid.supplies.card B.power

/-- Number of fixed blocks required by the integer demand. -/
noncomputable def repetitions (w : D → ℕ) : ℕ :=
  MotifWidths.copies (widthNorm p (fun i ↦ w i)) B.scale

theorem scale_pos : 0 < B.scale :=
  Nat.mul_pos B.power_pos (Nat.mul_pos B.multiple_pos B.grid.denominator_pos)

/-- Every actual selector sequence is admitted by the numerical payload bound. -/
theorem sequence_payload_le (hq : ∀ i, 0 < q i) (n : ℕ)
    (σ : Fin n → Fin B.power → B.grid.supplies) :
    widthNorm q (fun i ↦ ((∑ j, payload (B.grid.supplyWidths B.multiple) (σ j) i : ℕ) : ℝ)) ≤
      (n : ℝ) * B.scale * B.radius := by
  push_cast
  calc
    _ ≤ ∑ j, widthNorm q (fun i ↦ (payload (B.grid.supplyWidths B.multiple) (σ j) i : ℝ)) :=
      MotifWidths.widthNorm_sum_le q hq _
    _ ≤ ∑ _j : Fin n, (B.scale : ℝ) * (B.radius : ℝ) :=
      Finset.sum_le_sum fun j _ ↦ B.base_payload_le (σ j)
    _ = _ := by simp [mul_assoc]

end FixedBlock

/-- From the paper's spectral inequality obtain one block whose repetitions
cover every nonnegative integer demand and obey the stated energy estimate. -/
theorem exists_fixed_block [Nontrivial J] (a b : D → J) (P : MotifSelector.Supply J S)
    (p : D → ℝ) (q : S → ℝ) (hp : ∀ i, 0 < p i) (hq : ∀ i, 0 < q i) {H H' : ℝ}
    (hH : 0 ≤ H) (hHH' : H < H')
    (hcomp : ∀ F : SpectralPoint k J, distanceEnergy p (fun i ↦ F.wireDistance (a i) (b i)) ≤
      H * distanceEnergy q (fun i ↦ F.wireDistance (P.src i) (P.dst i))) :
    Nonempty (FixedBlock k a b P p q H H') := by
  obtain ⟨R, hR₁, hR₂⟩ := exists_rat_btwn (Real.sqrt_lt_sqrt hH hHH')
  have hR : 0 < (R : ℝ) := (Real.sqrt_nonneg H).trans_lt hR₁
  obtain ⟨G⟩ := exists_strict_grids p q hp hq hH hR₁
  obtain ⟨δ, hδ, htol⟩ := MotifWidths.exists_selector_tolerance (R : ℝ)
    (widthNorm q (fun _ ↦ 1)) H' hR.le (Real.sqrt_nonneg _) hR₂
  obtain ⟨t, h, K, ht, hh, hK, hfrac, hbase, hpayload⟩ :=
    exists_base_block G a b P hq hcomp hδ
  let s := MotifWidths.selectorBits K G.supplies.card h
  let L := h * (t * G.denominator)
  have hL : 0 < L := Nat.mul_pos hh (Nat.mul_pos ht G.denominator_pos)
  have hfrac' : (s : ℝ) / L < δ := by simpa [s, L] using hfrac
  have hbudget := htol ((s : ℝ) / L) (by positivity) hfrac'
  obtain ⟨C, hbound⟩ := MotifWidths.padded_energy_le q hq hL hR.le hbudget
  refine ⟨⟨R, Rat.cast_pos.mp hR, G, t, h, K, ht, hh, hK, hbase, hpayload,
    MotifWidths.exists_padded_grid G hp t h ht hh, C, ?_⟩⟩
  intro w v
  exact hbound (widthNorm p (fun i ↦ (w i : ℝ))) v (Real.sqrt_nonneg _)

end MotifBlocks

end VPVNP
end Computability
end OAI
