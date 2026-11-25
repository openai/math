import OAI.Computability.NearSquareRoot.ProductBoxStages
import OAI.Computability.NearSquareRoot.ProductPhaseTable
import OAI.Computability.NearSquareRoot.SynchronizedPhysicalFiber

/-! # Finite-record action of the physical stage shapes -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace ProductRecovery

open Matrix ProductMatrixLayers ShortFourier SynchronizedBlocks FixedPoint SynchronizedPadding
noncomputable section

variable {X Y : Type} [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y] {k : ℕ}

/-- Changing address layout conjugates every local record evaluator. -/
theorem RoundedStage.reindex {M : Square Y} {h : Mᴴ * M = 1}
    (hr : RoundedStage k M h) (e : X ≃ Y) : RoundedStage k (M.submatrix e e) (unitary_reindex e M h) := by
  obtain ⟨step, hs⟩ := hr
  exact ⟨fun r => step (r ∘ e.symm) ∘ e, roundoff_reindex e _ h step hs⟩

theorem rounded_permutation (e : Equiv.Perm X) (h : (e.toPEquiv.toMatrix : Square X)ᴴ * e.toPEquiv.toMatrix = 1) :
    RoundedStage k e.toPEquiv.toMatrix h := by
  refine ⟨fun r => r ∘ e, fun r _ => ?_⟩
  rw [Layers.record_permutation e r h, sub_self, norm_zero]
  positivity

/-- This form accepts the actual table generated for the diagonal. -/
theorem rounded_diagonal_of_table (hk : 1 ≤ k) (hcard : Fintype.card X = 2^k) (d : X → ℂ)
    (hd : ∀ i, ‖d i‖ = 1) (h : (diagonal d)ᴴ * diagonal d = 1) {pc wc : ℕ}
    (table : X → IntegerMultiplication.Dusk.Grain wc)
    (hentry : ∀ i, ‖IntegerMultiplication.Grid.meaning pc wc (table i) - d i‖ ≤ 1/(2:ℝ)^(70*k)) :
    RoundedStage k (diagonal d) h :=
  ⟨fun r i => multiplyCoefficient pc (r i) (table i),
   fun r hr => Layers.record_diagonal_error hk hcard d hd table r hentry hr h⟩

/-- For a fixed box a finite choice of records realizes any unit-modulus phase table. -/
theorem rounded_diagonal (hk : 1 ≤ k) (hcard : Fintype.card X = 2^k) (d : X → ℂ)
    (hd : ∀ i, ‖d i‖ = 1) (h : (diagonal d)ᴴ * diagonal d = 1) :
    RoundedStage k (diagonal d) h := by
  choose c hc using fun i => exists_phase_record k (d i) (hd i)
  exact rounded_diagonal_of_table hk hcard d hd h c hc

theorem unitary_of_reindex (e : X ≃ Y) (M : Square Y)
    (h : (M.submatrix e e)ᴴ * M.submatrix e e = 1) : Mᴴ * M = 1 := by
  have := unitary_reindex e.symm _ h
  simpa [submatrix_submatrix] using this

/-- All synchronized box stages share the original padded layout. A finite
table and fixed-width complex multiplications handle the diagonal, and a slot
permutation is exact. The remaining case is the normalized selected-bit transform. -/
theorem boxStage_of_flatWalsh {L : ℕ} {box : List (ℕ × ℕ)} (hb : BoxShape.Valid k L box)
    [∀ i, NeZero (BoxFin.modulus box i)] (hd : 4 ≤ box.length) (hk : 1 ≤ k)
    (walsh : ∀ (bits : Finset (Fin k)) (h : (BoxFin.flatWalsh bits)ᴴ * BoxFin.flatWalsh bits = 1),
      RoundedStage k (BoxFin.flatWalsh bits) h)
    (N : Square (∀ i, BoxAxis box i)) (hs : BoxStage hd (boxBits hb) N) :
    RoundedStage k N hs.unitary := by
  obtain ⟨M,hm,rfl⟩ := hs
  have hgroup : Fintype.card (∀ j, BlockAddress (BoxAxis box) j) = 2^k :=
    (Fintype.card_congr (regroup hd _)).symm.trans (BoxFin.card_padded hb)
  cases hm with
  | permutation p =>
    exact (rounded_permutation _ (GlobalStage.unitary (GlobalStage.permutation (address := boxBits hb) p))).reindex _
  | diagonal d h =>
    apply RoundedStage.reindex
    apply rounded_diagonal hk hgroup _ _ (GlobalStage.unitary (GlobalStage.diagonal (address := boxBits hb) d h))
    intro x
    simp [h]
  | walsh active =>
    have he := BoxFin.tensorWalsh_physical hb hd active
    have hu := unitary_reindex (regroup hd _) _ (GlobalStage.unitary (GlobalStage.walsh (address := boxBits hb) active))
    rw [he] at hu
    have hflat := unitary_of_reindex (BoxFin.recordIndex hb) _ hu
    convert (walsh _ hflat).reindex (BoxFin.recordIndex hb) using 1

end
end ProductRecovery

end NearSquareRoot
end Computability
end OAI
