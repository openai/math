import OAI.Hierarchy.PathForces
import OAI.Hierarchy.ConnectedBlockLoad
import OAI.Hierarchy.FixedCutFamilyForcing
import OAI.Hierarchy.FormulaBlockFactors
import OAI.Hierarchy.FormulaPartitionRank

namespace OAI
/-! # Forcing a lower bound from partitioned sums of a connected graph's wires -/

namespace Hierarchy

open LinearAlgebra.SpectralBooks LinearAlgebra.SpectralBooks.SiteTensor
open FormulaPartitionRank
open scoped Classical BigOperators
noncomputable section

namespace IncidenceGraph

def blockCount (G : IncidenceGraph) : ℕ := Nat.log 2 (Fintype.card G.V) + 1

/-- The selector error constant only depends on the fixed graph, including the
number of surjective partitions of its vertices. -/
def selectorError (G : IncidenceGraph) : ℝ :=
  Real.sqrt (2 * (Fintype.card (G.E × Bool) : ℝ) *
    |1 + Real.sqrt (2*Real.pi) * Real.sqrt (Fintype.card (G.E × Bool)) *
      Real.logb 2 (Fintype.card (Partition G.V G.blockCount))|)

/-- A closure certificate for partitioned tensors forces a lower bound on the prescribed loads. -/
theorem connected_force_of_partition_closure (K : Type*) [Field K] (G : IncidenceGraph) [Nonempty G.E]
    (P : HomogeneousFlat K (Fintype.card G.E))
    (connected : ∀ u v, G.Connected u v) (hd : 2 ≤ Fintype.card G.V)
    {q s : ℕ} (hq : 2 ≤ q)
    (cl : (equalityWireRaw G.E K q).coeff ∈ affineZariskiClosure
      (partitionRankSums (ν := fun _ : G.E × Bool => Fin q)
        (fun (π : Partition G.V G.blockCount) p => π.val (G.portOwner p)) ((s+2)^24))) :
    G.blockCount * Real.logb 2 q ≤
      (24 * Real.sqrt (2*Real.pi)) * Real.sqrt G.blockCount * Real.logb 2 ((s : ℝ)+2) +
        G.selectorError * Real.sqrt (Real.logb 2 q) := by
  classical
  let I := G.E × Bool
  let b := G.blockCount
  let J := Partition G.V b
  let x := G.orthogonalSite
  let w := Real.logb 2 q
  have hb : 2 ≤ b := Nat.succ_le_succ (Nat.log_pos (by decide) hd)
  let : Nontrivial (Fin b) := Fin.nontrivial_iff_two_le.mpr hb
  let σ (π : J) := π.val ∘ G.portOwner
  let R := (s+2)^24
  let S := {Y : J → ((I → Fin q) → K) |
    ∀ π, HasBlockFactors (σ π) R (Y π)}
  have pos : 0 < q := by omega
  have hw : 0 ≤ w := Real.logb_nonneg (by norm_num) (by exact_mod_cast (show 1 ≤ q by omega))
  have price := equalityWireRaw_price_antipodal P.prices x q pos
    G.orthogonalSite_unit G.orthogonalSite_antipodal
  have unit (i : I) : ‖x i‖ = 1 := by
    obtain ⟨e, flag⟩ := i
    cases flag
    · exact G.orthogonalSite_unit e
    · simpa [x, G.orthogonalSite_antipodal] using G.orthogonalSite_unit e
  obtain ⟨_, _, π, _, force⟩ := @HomogeneousFlat.path_force I (Fin b) _ _ _ _
    K _ _ _ (fun _ : I => Fin q) (fun _ => Fin.fintype q) J _
    P x unit S (equalityWireRaw G.E K q).coeff cl
    (equalityWireRaw_coeff_ne_zero G.E _ q pos)
    (by
      exact (congrArg (fun T : Raw.{0} I K => P.prices.price T x)
        (raw_with_finiteLeg (equalityWireRaw G.E K q)
          (fun _ => Fin.fintype q))).trans (by simpa only [Fintype.card_fin] using price))
    1 (by norm_num) σ R (fun _ h π _ => h π)
  have load := G.prescribed_partition_load connected π.val π.property hw
  simp only [Fintype.card_fin] at load force
  apply load.trans (force.trans _)
  apply add_le_add
  · dsimp [R]
    push_cast
    rw [Real.logb_pow]
    apply Eq.le
    ring
  · let l := Fintype.card I
    let a := 1 + Real.sqrt (2*Real.pi) * Real.sqrt l * Real.logb 2 (Fintype.card J)
    have equal : (∑ _i : I, Real.logb 2 q) = l*w := by
      simp only [l,w,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
    rw [equal]
    change Real.sqrt (2*((l : ℝ)*w)*a) ≤ Real.sqrt (2*(l : ℝ)*|a|) * Real.sqrt w
    rw [← Real.sqrt_mul (by positivity : 0 ≤ 2*(l : ℝ)*|a|)]
    apply Real.sqrt_le_sqrt
    calc
      2*(l*w)*a ≤ 2*(l*w)*|a| := mul_le_mul_of_nonneg_left (le_abs_self _) (by positivity)
      _ = _ := by ring


end IncidenceGraph
end
end Hierarchy

end OAI
