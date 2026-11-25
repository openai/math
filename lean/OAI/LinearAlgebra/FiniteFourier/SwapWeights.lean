import OAI.LinearAlgebra.FiniteFourier.SwapPrice
import OAI.LinearAlgebra.SpectralBooks.MaskDiagonalPrice
import OAI.LinearAlgebra.SpectralBooks.PlacementDiagonal

/-! # Price of the unweighted swap

The swap of two independent registers is the product of identity wires from
the first input to the second output and from the second input to the first
output. Its price therefore counts these two distances with the logarithm of
the register dimension as their common weight.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

noncomputable section

section

open OAI.LinearAlgebra.SpectralBooks OAI.LinearAlgebra.SpectralBooks.SiteTensor
open scoped Classical

variable {K : Type*} [Field K] {G : Type} [Fintype G]

private def leftWireLeg {I : Type} {A B : Finset I} {i : I} (ha : i ∈ A) (hb : i ∉ B) :
    G ≃ MaskLeg A G i × MaskLeg B G i where
  toFun g := (fun _ ↦ g, fun h ↦ (hb h).elim)
  invFun z := z.1 ha
  left_inv _ := rfl
  right_inv _ := Prod.ext rfl (funext fun h ↦ (hb h).elim)

private def rightWireLeg {I : Type} {A B : Finset I} {i : I} (ha : i ∉ A) (hb : i ∈ B) :
    G ≃ MaskLeg A G i × MaskLeg B G i where
  toFun g := (fun h ↦ (ha h).elim, fun _ ↦ g)
  invFun z := z.2 hb
  left_inv _ := rfl
  right_inv _ := Prod.ext (funext fun h ↦ (ha h).elim) rfl

/-- On the four legs `(input row, input column, output row, output column)`
the plain swap is equivalent to the product of the two crossing identity wires. -/
theorem swapRaw_one_equivalent :
    (swapRaw (fun _ : G × G ↦ (1 : K))).Equivalent
      ((Raw.maskDiagonal K ({0,3} : Finset (Fin 4)) G).mul
        (Raw.maskDiagonal K ({1,2} : Finset (Fin 4)) G)) := by
  let A : Finset (Fin 4) := {0,3}
  let B : Finset (Fin 4) := {1,2}
  let four {F : Fin 4 → Type} (a : F 0) (b : F 1) (c : F 2) (d : F 3) : ∀ i, F i :=
    Fin.cases a (Fin.cases b (Fin.cases c (Fin.cases d (fun i ↦ i.elim0))))
  let e := four (F := fun i ↦ phaseLeg G G i ≃ MaskLeg A G i × MaskLeg B G i)
    (leftWireLeg (A := A) (B := B) (i := 0) (by decide) (by decide))
    (rightWireLeg (A := A) (B := B) (i := 1) (by decide) (by decide))
    (rightWireLeg (A := A) (B := B) (i := 2) (by decide) (by decide))
    (leftWireLeg (A := A) (B := B) (i := 3) (by decide) (by decide))
  apply Raw.reindex_equivalent e
  intro z
  change weightedSwapEntry (fun _ : G × G ↦ (1 : K)) (z 0) (z 1) (z 2) (z 3) =
    (Raw.maskDiagonal K A G).coeff (fun i ↦ (e i (z i)).1) *
    (Raw.maskDiagonal K B G).coeff (fun i ↦ (e i (z i)).2)
  rw [Raw.maskDiagonal_coeff_at (K := K) A (i₀ := 0) (by decide),
      Raw.maskDiagonal_coeff_at (K := K) B (i₀ := 1) (by decide)]
  have hA : (∀ i (h : i ∈ A), (e i (z i)).1 h = (e 0 (z 0)).1 (by decide)) ↔ z 0 = z 3 := by
    constructor
    · exact fun h ↦ (h 3 (by decide)).symm
    · intro h i hi
      rcases Finset.mem_insert.mp hi with rfl | hi
      · rfl
      · obtain rfl := Finset.mem_singleton.mp hi
        exact h.symm
  have hB : (∀ i (h : i ∈ B), (e i (z i)).2 h = (e 1 (z 1)).2 (by decide)) ↔ z 1 = z 2 := by
    constructor
    · exact fun h ↦ (h 2 (by decide)).symm
    · intro h i hi
      rcases Finset.mem_insert.mp hi with rfl | hi
      · rfl
      · obtain rfl := Finset.mem_singleton.mp hi
        exact h.symm
  simp [weightedSwapEntry, hA, hB, ite_and]
  change (if (z 0 : G) = z 3 then if (z 1 : G) = z 2 then (1 : K) else 0 else 0) =
    (if (z 1 : G) = z 2 then if (z 0 : G) = z 3 then (1 : K) else 0 else 0)
  split_ifs <;> rfl

variable {X : Type} [MetricSpace X] (P : SpectralPlacementPrices K X)

/-- The arbitrary-dimensional identity wire costs its length times the base-two
logarithm of the label dimension, including coincident endpoints. -/
theorem placed_wire_price [Nonempty G] (x : Fin 2 → X) :
    P.price (Raw.diagonal (Fin 2) K G) x = dist (x 0) (x 1) * Real.logb 2 (Fintype.card G) := by
  rw [← P.wire x]
  rcases placed_price_normalized_or_collapsed P x with hc | ⟨φ,c,_,he⟩
  · simp only [hc, zero_mul]
  · simp only [he, rawLogPrice, ofRaw_diagonal_eq_natCast]
    have hcast (n : ℕ) : φ.val (n : TensorClass.{0} (Fin 2) K) = n := map_natCast (normalizedSpectrum.toRingHom φ) n
    rw [hcast, hcast]
    push_cast
    norm_num [Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2)]

/-- Two-site support in an ambient list, including repeated placement points. -/
theorem placed_pair_mask_price {I : Type} [DecidableEq I] [Fintype I] [Nonempty I] [Nonempty G]
    (x : I → X) {a b : I} (hab : a ≠ b) :
    P.price (Raw.maskDiagonal K {a,b} G) x = dist (x a) (x b) * Real.logb 2 (Fintype.card G) := by
  let σ : Fin 2 ↪ I := ⟨![a,b], by
    intro i j
    fin_cases i <;> fin_cases j <;> simp [hab, hab.symm]⟩
  have hs (i) : i ∈ ({a,b} : Finset I) ↔ ∃ j, σ j = i := by
    rw [Fin.exists_fin_two]
    change i ∈ ({a,b} : Finset I) ↔ a = i ∨ b = i
    simp only [Finset.mem_insert, Finset.mem_singleton, eq_comm]
  rw [← placed_price_class_eq P x (Raw.ofRaw_group_diagonal_eq_mask σ {a,b} hs G), ← P.group,
    placed_wire_price]
  rfl

/-- Exact price of the plain swap on any placement of four sites. -/
theorem swapRaw_one_price [Nonempty G] (x : Fin 4 → X) :
    P.price (swapRaw (fun _ : G × G ↦ (1 : K))) x =
      (dist (x 0) (x 3) + dist (x 1) (x 2)) * Real.logb 2 (Fintype.card G) := by
  rw [placed_price_class_eq P x (ofRaw_eq_iff.mpr swapRaw_one_equivalent),
    placed_price_mul P x _ _ (Raw.maskDiagonal_ne_zero _ (Finset.insert_nonempty ..) G)
      (Raw.maskDiagonal_ne_zero _ (Finset.insert_nonempty ..) G), add_mul]
  exact congrArg₂ (· + ·) (placed_pair_mask_price (G := G) P x (by decide : (0 : Fin 4) ≠ 3))
    (placed_pair_mask_price (G := G) P x (by decide : (1 : Fin 4) ≠ 2))

end

end

end FiniteFourier
end LinearAlgebra
end OAI
