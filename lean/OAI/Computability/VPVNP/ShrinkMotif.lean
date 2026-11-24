import OAI.Computability.VPVNP.MotifConversion
import OAI.Computability.VPVNP.ShrinkMotifGraph
import OAI.Computability.VPVNP.WireCATZero

/-!
# Converting the six-party demands over every field

The spectral CAT(0) inequality for this motif gives exact base identities
and the term energy estimate used to shrink a packed graph in Section 7.2.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace Compression.ShrinkMotif

open WireTensor MotifGrid MotifBlocks MotifConversion

variable {k : Type*} [Field k]

/-- Lemma 6.2 as the exact hypothesis (6.1) of the wire conversion. -/
theorem spectral_comparison (F : SpectralPoint k (Fin 6)) :
    distanceEnergy (realWidths demandMass)
      (fun i ↦ F.wireDistance (demandSource i) (demandTarget i)) ≤
      (31 / 16 : ℝ) * distanceEnergy (realWidths supplyMass)
        (fun e ↦ F.wireDistance (supply.src e) (supply.dst e)) := by
  have h := F.sixParty_wire_energy 0 1 2 3 4 5
  norm_num [distanceEnergy, realWidths, Fintype.sum_bool, Fintype.sum_prod_type, Fin.sum_univ_succ,
    supplyMass, demandMass, relativeMass, demandSource, demandTarget, supply,
      supplySource, supplyTarget]
  linarith only [h]

/-- A fixed block for all six-party demands, with its error chosen independently of the widths. -/
theorem exists_block {H' : ℝ} (hH' : 31 / 16 < H') :
    Nonempty (FixedBlock k demandSource demandTarget supply
      (realWidths demandMass) (realWidths supplyMass) (31 / 16) H') :=
  exists_fixed_block _ _ _ _ _ (fun i ↦ Rat.cast_pos.mpr (demandMass_pos i))
    (fun i ↦ Rat.cast_pos.mpr (supplyMass_pos i)) (by norm_num) hH' spectral_comparison

/-- Width profile of a single motif. -/
def demandWidths (ab cd : ℕ) : Bool → ℕ | false => ab | true => cd

variable {H' : ℝ} (B : FixedBlock k demandSource demandTarget supply
  (realWidths demandMass) (realWidths supplyMass) (31 / 16) H')

/-- Per-term energy budget in the indexing used by the packed graph. -/
theorem term_energy_le (ab cd : ℕ) {v : Bool × Fin 4 → ℕ}
    (hv : v ∈ outerIndices B (demandWidths ab cd)) :
    (∑ l : Bool, ∑ e, (supplyWidths B (demandWidths ab cd) v (l,e) : ℝ) ^ 2 /
      (relativeMass e : ℝ)) ≤
      H' * (3 * (ab : ℝ) ^ 2 + (cd : ℝ) ^ 2) + B.energyConstant := by
  have h := energy_le B demandMass_pos supplyMass_pos _ v hv
  rw [norm_sq (realWidths supplyMass) _ (fun e ↦ Rat.cast_pos.mpr (supplyMass_pos e)),
    norm_sq (realWidths demandMass) _ (fun i ↦ Rat.cast_pos.mpr (demandMass_pos i)),
      Fintype.sum_prod_type, Fintype.sum_bool] at h
  simpa [demandWidths, demandMass, realWidths, supplyMass, div_div_eq_mul_div, add_comm, mul_comm]
    using h

end Compression.ShrinkMotif

end VPVNP
end Computability
end OAI
