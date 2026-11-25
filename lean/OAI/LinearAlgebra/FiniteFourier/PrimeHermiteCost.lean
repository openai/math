import OAI.LinearAlgebra.FiniteFourier.PrimeHermiteRows
import OAI.LinearAlgebra.FiniteFourier.PrimeHermiteTable

/-! # Ordinary circuit cost of the full-rate Hermite repair

The first predictor output is retained across both branches. The check rows
undergo one spectral conversion in each direction. All the remaining mixing
acts independently at each ordinary coordinate.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

noncomputable section

section
open Matrix

variable {K α ν : Type*} [CommRing K] [Fintype α] [Fintype ν]

private theorem realizesRows_repairMixRows {m n : ℕ} (H : Matrix (Fin m) (Fin n) K) :
    RealizesRows (α := α) (repairMixRows (V := α → K) H) (Fintype.card α * n * m) := by
  have h := realizesOp_pointwise_matrix (fun _ : α => H)
  unfold RealizesRows
  simpa [repairMixRows, Finset.sum_apply, Matrix.mulVec, dotProduct] using h

private theorem realizesRows_takeLeft {I J : Type*} [Fintype I] [Fintype J] :
    RealizesRows (fun (x : (I ⊕ J) → α → K) => x ∘ Sum.inl) 0 :=
  RealizesOp.select (fun (p : I × α) => (Sum.inl p.1, p.2))

/-- Work per ordinary coordinate from the two check mixes, two transpose
mixes, the spectral table and the final pointwise linear combination. -/
def hermiteLocalCost (W s : ℕ) : ℕ := 4 * W * s + (2*s)^2 + 4 * W^2

/-- Arithmetic circuit for the repaired predictor. Each stage of the pencil is
charged exactly `(ℓ+2)b` times, and each of the `2s` check rows is converted
once in each direction. The auxiliary local constant is independent of the row length. -/
theorem realizesRows_hermiteRepairProgram {W s ℓ b ps sf si : ℕ} (u : K)
    (P : (Fin W → α → K) → Fin W → α → K) (S : (α → K) ≃ₗ[K] (ν → K))
    (H : Matrix (Fin s) (Fin W) K)
    (T : ν → ((Fin s → K) × (Fin s → K)) →ₗ[K] ((Fin s → K) × (Fin s → K)))
    (hcard : Fintype.card ν = Fintype.card α)
    (hP : RealizesRows P ps) (hf : RealizesOp S sf) (hi : RealizesOp S.symm si) :
    RealizesRows (hermiteRepairProgram ℓ u (P^[b]) S H T)
      (((ℓ+2)*b)*ps + 2*s*(sf+si) + hermiteLocalCost W s * Fintype.card α) := by
  classical
  let pred := P^[b]
  let mix := repairMixRows (V := α → K) H
  let unmix := repairMixRows (V := α → K) Hᵀ
  let table := fun (x : (Fin s ⊕ Fin s) → α → K) =>
    let t := ordinaryRepairTable S T (x ∘ Sum.inl) (x ∘ Sum.inr)
    Sum.elim t.1 t.2
  have hp : RealizesRows pred (b*ps) := hP.iterate b
  have hid := RealizesRows.id (I := Fin W) (α := α) (K := K)
  have hm : RealizesRows mix (Fintype.card α * W * s) := realizesRows_repairMixRows H
  have hu : RealizesRows unmix (Fintype.card α * s * W) := realizesRows_repairMixRows Hᵀ
  have ht : RealizesRows table (2*s*sf + Fintype.card ν * (2*s)^2 + 2*s*si) := by
    exact realizesOp_ordinaryRepairTable S T hf hi
  -- After the check table, transform only the first decoded block by the predictor.
  have hcor := (hp.parallel hid).comp ((hu.parallel hu).comp (ht.comp (hm.parallel hm)))
  -- The higher power uses the retained first predictor output.
  have hpow := ((hp.iterate ℓ).fanout hid).comp
    (realizesRows_takeLeft (I := Fin W) (J := Fin W) (α := α) (K := K))
  have hbranches := (hcor.fanout hpow).comp (hp.fanout hid)
  let finish : (((Fin W ⊕ Fin W) ⊕ (Fin W ⊕ Fin W)) → K) →ₗ[K] (Fin W → K) :=
    LinearMap.pi fun i =>
      let a := LinearMap.proj (Sum.inr (Sum.inr i))
      let a' := LinearMap.proj (Sum.inr (Sum.inl i))
      let c := LinearMap.proj (Sum.inl (Sum.inl i))
      let d := LinearMap.proj (Sum.inl (Sum.inr i))
      a - u • (a' - a) - c + d
  have hfinish : RealizesRows
      (fun (x : ((Fin W ⊕ Fin W) ⊕ (Fin W ⊕ Fin W)) → α → K) i a => finish (fun j => x j a) i) (Fintype.card α * (W+W+(W+W)) * W) := by
    simpa [RealizesRows] using realizesOp_pointwise_linear (fun _ : α => finish)
  have h := hfinish.comp hbranches
  convert h using 1
  · rfl
  · rw [hcard]
    unfold hermiteLocalCost
    ring

end

end

end FiniteFourier
end LinearAlgebra
end OAI
