import OAI.LinearAlgebra.SpectralBooks.StretchProducts
import OAI.LinearAlgebra.SpectralBooks.DimensionLaw

/-! # Diagonal price as a function of the label count

A label is copied to every occupied site. At the two families of private sites
we allow a family of label coordinates, with one coordinate on an occupied
site and none on an unoccupied site. This treats the full diagonal and both
private diagonals with the same product and restriction argument.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

noncomputable section

open MatrixMultiplication.Foundation
open scoped Classical BigOperators

namespace PermutationStretch

variable {K : Type*} [Field K] {B C : Type} [Fintype B] [Fintype C]

private def copies (B C H J W : Type) : Tensor K W (B → H → W) (C → J → W) :=
  fun w x y => if (∀ b h, x b h = w) ∧ (∀ c j, y c j = w) then 1 else 0

omit [Fintype B] [Fintype C] in
private theorem copies_ne_zero (B C H J W : Type) [Nonempty W] :
    copies (K := K) B C H J W ≠ 0 := by
  obtain ⟨w⟩ := ‹Nonempty W›
  intro he
  simpa [copies] using congrFun (congrFun (congrFun he w) (fun _ _ => w)) (fun _ _ => w)

variable (p : SitePriceEval K B C) (H J : Type) [Fintype H] [DecidableEq H]
  [Fintype J] [DecidableEq J]

private theorem value_copies_mono {V W : Type} [Fintype V] [Fintype W] (e : V ↪ W) :
    p.value (copies (K := K) B C H J V) ≤ p.value (copies (K := K) B C H J W) := by
  apply p.mono
  convert siteRestriction_pullback e (fun _ : B => fun (x : H → V) => e ∘ x)
    (fun _ : C => fun (y : J → V) => e ∘ y) (copies (K := K) B C H J W) using 1
  funext w x y
  simp [copies, Tensor.pullback]

private theorem value_copies_mul (hmul : p.BinaryProductAdditive) (V W : Type)
    [Fintype V] [Nonempty V] [Fintype W] [Nonempty W] :
    p.value (copies (K := K) B C H J (V × W)) =
      p.value (copies (K := K) B C H J V) + p.value (copies (K := K) B C H J W) := by
  rw [← hmul _ _ (copies_ne_zero B C H J V) (copies_ne_zero B C H J W)]
  apply p.value_reindex (Equiv.refl _) (fun _ => Equiv.arrowProdEquivProdArrow H _ _)
    (fun _ => Equiv.arrowProdEquivProdArrow J _ _)
  intro w x y
  have he : ((∀ b h, x b h = w) ∧ (∀ c j, y c j = w)) ↔
      (((∀ b h, (x b h).1 = w.1) ∧ (∀ c j, (y c j).1 = w.1)) ∧
       ((∀ b h, (x b h).2 = w.2) ∧ (∀ c j, (y c j).2 = w.2))) := by
    simp only [Prod.ext_iff, forall_and]
    tauto
  simp only [copies, he, SitePriceEval.splitProduct, Equiv.refl_apply,
    Equiv.arrowProdEquivProdArrow_apply]
  split_ifs <;> simp_all

private theorem value_copies_eq_logb (hmul : p.BinaryProductAdditive) (W : Type)
    [Fintype W] [Nonempty W] :
    p.value (copies (K := K) B C H J W) =
      p.value (copies (K := K) B C H J (Fin 2)) * Real.logb 2 (Fintype.card W) := by
  let f (n : ℕ) := p.value (copies (K := K) B C H J (Fin n))
  have hc {V Z : Type} [Fintype V] [Fintype Z] (e : V ≃ Z) :
      p.value (copies (K := K) B C H J V) = p.value (copies (K := K) B C H J Z) :=
    le_antisymm (value_copies_mono p H J e.toEmbedding) (value_copies_mono p H J e.symm.toEmbedding)
  have hm (i j : ℕ) (hi : 0 < i) (hj : 0 < j) : f (i*j) = f i + f j := by
    have : Nonempty (Fin i) := Fin.pos_iff_nonempty.mp hi
    have : Nonempty (Fin j) := Fin.pos_iff_nonempty.mp hj
    exact (hc (finProdFinEquiv (m := i) (n := j)).symm).trans (value_copies_mul p H J hmul _ _)
  have hone : f 1 = 0 := by have h := hm 1 1 (by decide) (by decide); norm_num at h; exact h
  exact (hc (Fintype.equivFin W)).trans (dimension_price_eq_logb (p := f)
    (fun _ _ _ hij => value_copies_mono p H J (Fin.castLEEmb hij)) hone hm Fintype.card_pos)

private theorem all_unit {P : Unit → Prop} : (∀ u, P u) ↔ P PUnit.unit :=
  ⟨fun h => h (), fun h u => by cases u; exact h⟩

private theorem value_copies_B (W : Type) [Fintype W] :
    p.value (copies (K := K) B C Unit Empty W) = p.value (diagB (K := K) B C W) := by
  apply p.value_reindex (Equiv.refl _) (fun _ => Equiv.funUnique Unit W)
    (fun _ => Equiv.ofUnique _ _)
  intro w x y
  simp [copies, diagB, placeB, diagonalCoeff, Equiv.funUnique, Equiv.piUnique, all_unit]
  split_ifs with h
  · exact (ite_eq_left h).symm
  · exact (ite_eq_right h).symm

private theorem value_copies_C (W : Type) [Fintype W] :
    p.value (copies (K := K) B C Empty Unit W) = p.value (diagC (K := K) B C W) := by
  apply p.value_reindex (Equiv.refl _) (fun _ => Equiv.ofUnique _ _)
    (fun _ => Equiv.funUnique Unit W)
  intro w x y
  simp [copies, diagC, placeC, diagonalCoeff, Equiv.funUnique, Equiv.piUnique, all_unit]
  split_ifs with h
  · exact (ite_eq_left h).symm
  · exact (ite_eq_right h).symm

private theorem value_copies_all (W : Type) [Fintype W] :
    p.value (copies (K := K) B C Unit Unit W) = p.value (diagAll (K := K) B C W) := by
  apply p.value_reindex (Equiv.refl _) (fun _ => Equiv.funUnique Unit W)
    (fun _ => Equiv.funUnique Unit W)
  intro w x y
  simp only [copies, diagAll, diagonalCoeff, Equiv.refl_apply]
  by_cases hx : ∀ b, x b PUnit.unit = w <;> by_cases hy : ∀ c, y c PUnit.unit = w <;>
    simp [Equiv.funUnique, Equiv.piUnique, all_unit, hx, hy]

/-- Every private diagonal on the left has logarithmic price determined by the
two-label diagonal on that side. -/
theorem value_diagB_eq_logb (hmul : p.BinaryProductAdditive) (W : Type) [Fintype W] [Nonempty W] :
    p.value (diagB (K := K) B C W) =
      p.value (diagB (K := K) B C (Fin 2)) * Real.logb 2 (Fintype.card W) := by
  simpa only [value_copies_B] using value_copies_eq_logb p Unit Empty hmul W

/-- The same price formula for a diagonal on the right. -/
theorem value_diagC_eq_logb (hmul : p.BinaryProductAdditive) (W : Type) [Fintype W] [Nonempty W] :
    p.value (diagC (K := K) B C W) =
      p.value (diagC (K := K) B C (Fin 2)) * Real.logb 2 (Fintype.card W) := by
  simpa only [value_copies_C] using value_copies_eq_logb p Empty Unit hmul W

/-- The full shared diagonal is priced by its binary value. -/
theorem value_diagAll_eq_logb (hmul : p.BinaryProductAdditive) (W : Type) [Fintype W] [Nonempty W] :
    p.value (diagAll (K := K) B C W) =
      p.value (diagAll (K := K) B C (Fin 2)) * Real.logb 2 (Fintype.card W) := by
  simpa only [value_copies_all] using value_copies_eq_logb p Unit Unit hmul W

/-- The binary diagonal price on the right is nonnegative, since the
one-label diagonal is its restriction and has zero log price. -/
theorem value_diagC_two_nonneg (hmul : p.BinaryProductAdditive) :
    0 ≤ p.value (diagC (K := K) B C (Fin 2)) := by
  have h1 : p.value (diagC (K := K) B C (Fin 1)) = 0 := by
    simpa only [Fintype.card_fin, Nat.cast_one, Real.logb_one, mul_zero] using
      value_diagC_eq_logb p hmul (Fin 1)
  rw [← h1, ← value_copies_C, ← value_copies_C]
  exact value_copies_mono p Empty Unit (Fin.castLEEmb (by decide))

end PermutationStretch

end

end SpectralBooks
end LinearAlgebra
end OAI
