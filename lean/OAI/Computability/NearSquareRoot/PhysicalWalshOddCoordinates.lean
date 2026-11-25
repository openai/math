import OAI.Computability.NearSquareRoot.PhysicalWalshSelectedMeaning
import OAI.Computability.NearSquareRoot.PrecisionButterflyArray
import OAI.Computability.NearSquareRoot.PrecisionButterflyStrong

/-! # Ordinal coordinates of the physical odd Walsh pass -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PhysicalWalsh.Odd

open IntegerMultiplication FixedPoint ButterflyTask FlatWalshNode
variable {k : ℕ}

private theorem span (hk : 1 ≤ k) : 2^(k-1)*2 = 2^k := by
  rw [← pow_succ, show k-1+1=k by omega]

/-- Adjacent tape words form a false/true pair in increasing ordinal order. -/
def pack (hk : 1 ≤ k) : Fin (2^(k-1)) × Bool ≃ Fin (2^k) :=
  ((Equiv.prodCongr (Equiv.refl _) finTwoEquiv.symm).trans finProdFinEquiv).trans (finCongr (span hk))

theorem pack_val (hk : 1 ≤ k) (j : Fin (2^(k-1))) (b : Bool) :
    (pack hk (j,b)).val = 2*j.val + (if b then 1 else 0) := by
  change (finTwoEquiv.symm b).val + 2*j.val = _
  cases b <;> simp [finTwoEquiv, Nat.add_comm]

theorem input_words (hk : 1 ≤ k) (x : Fin (2^k) → Record k) :
    arrayWords (x ∘ pack hk) = (List.ofFn x).map Dusk.mark := by
  rw [arrayWords, List.flatMap_def, List.map_ofFn, List.ofFn_congr (span hk).symm, List.ofFn_mul]
  rw [← List.ofFn_id, List.map_ofFn]
  congr 1
  apply congrArg List.ofFn
  funext j
  simp only [Function.comp_apply, id_eq, List.ofFn_succ, List.ofFn_zero]
  congr 2 <;> try apply congrArg Dusk.mark
  all_goals
    apply congrArg x
    apply Fin.ext
    simp [pack_val, Nat.mul_comm]

/-- Return both normalized branches to their original flat slots. -/
def output (hk : 1 ≤ k) (x : Fin (2^k) → Record k) : Fin (2^k) → Record k :=
  arrayOutput (x ∘ pack hk) ∘ (pack hk).symm

theorem output_words (hk : 1 ≤ k) (x : Fin (2^k) → Record k) :
    arrayWords (arrayOutput (x ∘ pack hk)) = (List.ofFn (output hk x)).map Dusk.mark := by
  calc
    _ = arrayWords (output hk x ∘ pack hk) := congrArg arrayWords (by
      funext j
      simp only [output, Function.comp_apply, Equiv.symm_apply_apply])
    _ = _ := input_words hk _

noncomputable section


/-- The exact pair transform, transported back to the packed order. -/
def ideal (hk : 1 ≤ k) : EuclideanSpace ℂ (Fin (2^k)) →ₗᵢ[ℂ] EuclideanSpace ℂ (Fin (2^k)) :=
  ((ProductRecovery.pull (pack hk).symm).toLinearIsometry.comp (directWalsh _)).comp
    (ProductRecovery.pull (pack hk)).toLinearIsometry

theorem ideal_at (hk : 1 ≤ k) (v : ℕ → ℂ) (j : Fin (2^k)) :
    ideal hk (WithLp.toLp 2 (fun i => v i.val)) j = activeRow 1 1 v j.val := by
  obtain ⟨⟨g,b⟩,rfl⟩ := (pack hk).surjective j
  change (SynchronizedPair.w : ℂ) * butterflySum ((pack hk).symm (pack hk (g,b))).2
    (v ((pack hk (((pack hk).symm (pack hk (g,b))).1,false))).val)
    (v ((pack hk (((pack hk).symm (pack hk (g,b))).1,true))).val) = _
  simp only [Equiv.symm_apply_apply, pack_val, Bool.false_eq_true, ite_false, add_zero, ite_true]
  exact (Pieces.odd_butterfly v g b).symm

theorem group_norm (hk : 1 ≤ k) (x : Fin (2^k) → Record k) :
    ‖recordArray (x ∘ pack hk)‖ = ‖recordArray x‖ := (ProductRecovery.pull (pack hk)).norm_map (recordArray x)

/-- A pair-coordinate error certificate with any threshold becomes an
identical error bound on increasing tape ordinals. -/
theorem output_error_of_direct (hk : 1 ≤ k) (x : Fin (2^k) → Record k) {ε : ℝ}
    (he : ‖recordArray (arrayOutput (x ∘ pack hk)) - directWalsh _
      (recordArray (x ∘ pack hk))‖ ≤ ε) :
    ‖recordArray (output hk x) - ideal hk (recordArray x)‖ ≤ ε := by
  rw [← (ProductRecovery.pull (pack hk).symm).norm_map] at he
  rwa [map_sub] at he

theorem output_error (hk : 1 ≤ k) (x : Fin (2^k) → Record k)
    (hx : ‖recordArray x‖ ≤ (2:ℝ)^(13*k)) :
    ‖recordArray (output hk x) - ideal hk (recordArray x)‖ ≤ 1/(2:ℝ)^(50*k) := by
  apply output_error_of_direct
  rw [directWalsh_eq_matrix]
  exact arrayOutput_error _ hk ((Nat.mul_comm ..).trans (span hk)) ((group_norm hk x).trans_le hx)

/-- Headroom for applying the terminal pair pass after an already-rounded
even traversal. -/
theorem output_error55 (hk : 1 ≤ k) (x : Fin (2^k) → Record k)
    (hx : ‖recordArray x‖ ≤ (2:ℝ)^(14*k)) :
    ‖recordArray (output hk x) - ideal hk (recordArray x)‖ ≤ 1/(2:ℝ)^(55*k) := by
  apply output_error_of_direct
  have card : Fintype.card (Fin (2^(k-1)) × Bool) ≤ 2^k := by
    simpa only [Fintype.card_prod, Fintype.card_fin, Fintype.card_bool] using (span hk).le
  exact directWalshLayer_error55 hk card (x ∘ pack hk) _ ((group_norm hk x).trans_le hx)
    (butterflyCoefficient_error k)

end
end PhysicalWalsh.Odd

end NearSquareRoot
end Computability
end OAI
