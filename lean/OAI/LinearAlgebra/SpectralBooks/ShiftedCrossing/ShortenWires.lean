import OAI.LinearAlgebra.SpectralBooks.ShiftedCrossing.ShortenTensor

/-! # The price of the two original opposite wires -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

noncomputable section
open scoped Classical

namespace ShiftedCrossing

open SiteTensor

variable {K E : Type*} [Field K] [MetricSpace E]

private abbrev wireX (K : Type*) [Field K] (q : ℕ) : Raw Site K :=
  (Raw.diagonal (Fin 2) K (Fin q)).group Sum.inl

private abbrev wireY (K : Type*) [Field K] (q : ℕ) : Raw Site K :=
  (Raw.diagonal (Fin 2) K (Fin q)).group Sum.inr

private def pairLegEquiv (dX dY : ℕ) : ∀ i : Site,
    Leg dX dY i ≃ ((wireX K dX).mul (wireY K dY)).Leg i
  | .inl j =>
    { toFun := fun x => (fun _ => x, fun h => nomatch h.property)
      invFun := fun w => w.1 ⟨j,rfl⟩
      left_inv := fun _ => rfl
      right_inv := by
        rintro ⟨a,b⟩
        apply Prod.ext
        · funext ⟨i,hi⟩
          cases Sum.inl.inj hi
          rfl
        · funext h
          exact nomatch h.property }
  | .inr j =>
    { toFun := fun x => ((fun h => nomatch h.property), fun _ => x)
      invFun := fun w => w.2 ⟨j,rfl⟩
      left_inv := fun _ => rfl
      right_inv := by
        rintro ⟨a,b⟩
        apply Prod.ext
        · funext h
          exact nomatch h.property
        · funext ⟨i,hi⟩
          cases Sum.inr.inj hi
          rfl }

private theorem wire_coeff {q : ℕ} (v : Fin 2 → Fin q) :
    (Raw.diagonal (Fin 2) K (Fin q)).coeff v = if v 0 = v 1 then 1 else 0 := by
  have h (a : Fin q) : v = (fun _ => a) ↔ v 0 = a ∧ v 1 = a := by
    constructor
    · rintro rfl; simp
    · intro he
      funext i
      fin_cases i <;> simp [he]
  simp only [Raw.diagonal, h, ite_and]
  simp [eq_comm]

private theorem target_product (dX dY : ℕ) : (target K dX dY).Equivalent
    ((wireX K dX).mul (wireY K dY)) := by
  apply Raw.reindex_equivalent (pairLegEquiv dX dY)
  intro a
  change (if a (.inl 0) = a (.inl 1) ∧ a (.inr 0) = a (.inr 1) then (1 : K) else 0) =
    (Raw.diagonal (Fin 2) K (Fin dX)).coeff (fun j => a (.inl j)) *
    (Raw.diagonal (Fin 2) K (Fin dY)).coeff (fun j => a (.inr j))
  erw [wire_coeff (K := K) (fun j => a (.inl j)), wire_coeff (K := K) (fun j => a (.inr j))]
  have h (v : Fin 2 → Fin dX) (w : Fin 2 → Fin dY) :
      (if v 0 = v 1 ∧ w 0 = w 1 then (1 : K) else 0) =
      (if v 0 = v 1 then 1 else 0) * (if w 0 = w 1 then 1 else 0) := by
    split_ifs <;> simp_all
  convert! h (fun j => a (.inl j)) (fun j => a (.inr j))

private theorem wire_ne_zero {q : ℕ} (hq : 0 < q) :
    (Raw.diagonal (Fin 2) K (Fin q)).coeff ≠ 0 := by
  intro h
  have hh := congrFun h (fun _ => (⟨0,hq⟩ : Fin q))
  rw [wire_coeff, ite_eq_left rfl] at hh
  exact one_ne_zero hh

theorem target_price (P : SpectralPlacementPrices K E) (p : Site → E)
    {dX dY : ℕ} (hX : 0 < dX) (hY : 0 < dY) :
    P.price (target K dX dY) p =
      dist (p (.inl 0)) (p (.inl 1)) * Real.logb 2 dX +
      dist (p (.inr 0)) (p (.inr 1)) * Real.logb 2 dY := by
  have eqv := target_product (K := K) dX dY
  rw [le_antisymm (P.placed_mono p eqv.1) (P.placed_mono p eqv.2), P.placed_product p
    ((Raw.group_ne_zero_iff _ _).mpr (wire_ne_zero hX))
    ((Raw.group_ne_zero_iff _ _).mpr (wire_ne_zero hY))]
  rw [← P.group, ← P.group, P.placed_diagonal_pair, P.placed_diagonal_pair]
  rfl

end ShiftedCrossing

end

end SpectralBooks
end LinearAlgebra
end OAI
