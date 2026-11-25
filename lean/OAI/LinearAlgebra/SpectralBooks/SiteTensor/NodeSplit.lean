import OAI.LinearAlgebra.SpectralBooks.SiteTensor.EndpointPrices
import OAI.LinearAlgebra.SpectralBooks.Levels
import OAI.LinearAlgebra.SpectralBooks.SiteTensor.NodeChild
import OAI.LinearAlgebra.SpectralBooks.EndpointTable.Recursion
import OAI.LinearAlgebra.SpectralBooks.SiteTensor.Select

/-! # A splitting step for actual spectral prices

A single selected exterior summand works for both placements of the second
mark. At each crossed endpoint its extra cost is bounded by the chosen
threshold. The middle wire's cost is included in the new node offset.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

noncomputable section
open scoped Classical

namespace SiteTensor.Relocation.WireNode

open Exterior

variable {K : Type*} [Field K] {J : Type} [Fintype J] [Nonempty J]

private theorem sub_wire_offset {x y h o : ℝ} (hx : x ≤ y + h) :
    x - (o + h) ≤ y - o := by linarith

/-- The finite branching estimate with a dimension-independent loss, for
every actual spectral point and all placements of the two marked indices. -/
theorem hasSplit (φ : normalizedSpectrum ((· ≤ ·) : TensorClass.{0} J K → _ → Prop))
    (c : ℝ) (hc : 0 ≤ c) (n : ℕ) (hn : 1 ≤ n) (A B : Fin 2 → J) (z w : J) :
    EndpointTable.HasSplit (fun (N : WireNode K J (2^n)) i j => cost φ c N (A i) (B j))
      (fun N => cost φ c N z w) (n * rawWireDistance φ c (A 0) (A 1)) c := by
  intro N s hs
  let t := rawWireDistance φ c (A 0) (A 1)
  have ht : 0 ≤ t := rawLogPrice_nonneg φ hc _
  obtain ⟨b, hb, hplus, hminus⟩ := relocation_level_bounds_for_threshold hn ht hs
  let Q := 2^n
  let σ (v : J) := Function.update N.site N.other v
  let H := Level Q (b + 1)
  have ex (k : ℕ) (hk : k ≤ Q) : Nonempty (Level Q k) := by
    apply Fintype.card_pos_iff.mp
    rw [card_level]
    exact Nat.choose_pos hk
  let : Nonempty (Level Q b) := ex b (by dsimp [Q]; omega)
  let : Nonempty (Level Q (b + 1)) := ex (b+1) (by dsimp [Q]; omega)
  let : Nonempty (Level Q (b + 2)) := ex (b+2) hb
  let loss := t * Real.logb 2 (Fintype.card H)
  have wire_eq : rawLogPrice φ c (wire K H (A 0) (A 1)) = loss :=
    rawLogPrice_group_diagonal φ ![A 0,A 1] c
  let U := plusCoeff N.T (create K) (contract K) (H := H)
  let V := minusCoeff N.T (contract K) (create K) (H := H)
  have up (j : Fin 2) := plus_endpoint_prices φ hc N.T (create (b := b+1) K) (contract K)
    (σ (B j)) (A 0) (A 1)
  have down (j : Fin 2) := minus_endpoint_prices φ hc N.T (contract (b := b) K) (create K)
    (σ (B j)) (A 0) (A 1)
  have hp : t * Real.logb 2 (Fintype.card (Level Q (b+2))) - loss ≤ s := by
    simpa only [loss, H, card_level, ← mul_sub] using hplus
  have hm : t * Real.logb 2 (Fintype.card (Level Q b)) - loss ≤ -s := by
    simpa only [loss, H, card_level, ← mul_sub] using hminus
  have selected := select_split (b := b) φ hc N.T N.nonzero (σ w) z (A 0) (A 1)
  rcases selected with ⟨hne, hcost⟩ | ⟨hne, hcost⟩
  · refine ⟨N.child U hne (A 0) (A 1) loss, ?_, ?_, Or.inl ?_⟩
    · simp only [cost_child]
      change rawLogPrice φ c ((marked N.A (Fin Q) N.T).group (placeMark (σ w) z)) - N.offset ≤ _
      rw [wire_eq] at hcost
      linarith only [hcost]
    · intro i j
      simp only [cost_child]
      fin_cases i
      · have h := (up j).1
        change _ ≤ _ + loss at h
        exact sub_wire_offset h
      · have h := (up j).2.1
        change _ ≤ _ + loss at h
        exact sub_wire_offset h
    · intro j
      simp only [cost_child]
      have h := (up j).2.2
      unfold cost
      linarith only [h, hp, hc]
  · refine ⟨N.child V hne (A 0) (A 1) loss, ?_, ?_, Or.inr ?_⟩
    · simp only [cost_child]
      change rawLogPrice φ c ((marked N.A (Fin Q) N.T).group (placeMark (σ w) z)) - N.offset ≤ _
      rw [wire_eq] at hcost
      linarith only [hcost]
    · intro i j
      simp only [cost_child]
      fin_cases i
      · have h := (down j).1
        change _ ≤ _ + loss at h
        exact sub_wire_offset h
      · have h := (down j).2.1
        change _ ≤ _ + loss at h
        exact sub_wire_offset h
    · intro j
      simp only [cost_child]
      have h := (down j).2.2
      unfold cost
      linarith only [h, hm, hc]

end SiteTensor.Relocation.WireNode

end

end SpectralBooks
end LinearAlgebra
end OAI
