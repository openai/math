import OAI.LinearAlgebra.SpectralBooks.Fermion.Fermion
import Mathlib.Data.Matrix.Basic

/-!
# Factoring the coefficients of the integral crossing identity

The two orders of the field product factor through different energy cutoffs.
A shared index records the cardinality and doubled energy of the second block,
the multiplier monomial, and the intermediate state. This gives an explicit
cubic polynomial overhead.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

noncomputable section
namespace Fermion

open Finset
open scoped BigOperators Classical

abbrev ModeMatrix := State → ℤ → State → State → ℤ

def order (w v : ℕ) := (w+v)/2 - 1

def multiplier (L a : ℕ) : ℤ := (-1)^a * (L.choose a : ℤ)

abbrev PlusStates (H E : ℕ) (s : ℤ) := ↥(states (E+H+2*s))
abbrev MinusStates (H E : ℕ) (s : ℤ) := ↥(states (E+H-2*s))

/-- The integral coefficient of the field supercommutator, with both sums
over their allowed intermediate energies. The multiplier vanishes for `a>L`. -/
def CoefficientIdentity (C : State → State → ℤ) (Y : ModeMatrix) : Prop :=
  ∀ (H E : ℕ) (s : ℤ) (i j : Label H) (_ : i.val.card = j.val.card)
    (α β : ↥(states (E : ℤ))),
    let L := order (weight i.val) (weight j.val)
    C i.val j.val * (if α = β then 1 else 0) =
      ∑ a : Fin (H+1), multiplier L a *
        ((∑ k : PlusStates H E s,
            Y i.val (-s-1-L+a) α.val k.val * Y j.val (s-a) k.val β.val) -
          (-1)^(i.val.card*j.val.card) * ∑ k : MinusStates H E s,
            Y j.val (s-a) α.val k.val * Y i.val (-s-1-L+a) k.val β.val)

/-- A pair of integral factorizations on the two transverse flattenings. -/
structure Factors (I A P M : Type*) where
  plusLeft : I → A → P → ℤ
  plusRight : I → A → P → ℤ
  minusLeft : I → A → M → ℤ
  minusRight : I → A → M → ℤ

def Factors.entry {I A P M : Type*} [Fintype P] [Fintype M] (F : Factors I A P M)
    (i j : I) (α β : A) : ℤ :=
  (∑ k, F.plusLeft i α k * F.plusRight j β k) +
    ∑ k, F.minusLeft i β k * F.minusRight j α k

abbrev BlockTag (H : ℕ) := Fin (H+1) × Fin (H+1)

private def tag {H : ℕ} (j : Label H) : BlockTag H :=
  (⟨j.val.card, Nat.lt_succ_of_le ((card_le_weight j.val).trans (label_weight_le j))⟩,
   ⟨weight j.val, Nat.lt_succ_of_le (label_weight_le j)⟩)

abbrev Channel (H : ℕ) (K : Type*) := BlockTag H × (Fin (H+1) × K)

theorem card_channel (H : ℕ) (K : Type*) [Fintype K] :
    Fintype.card (Channel H K) = (H+1)^3 * Fintype.card K := by
  simp only [Channel, BlockTag, Fintype.card_prod, Fintype.card_fin]
  ring

private def split (Y : ModeMatrix) (H E : ℕ) (s : ℤ) :
    Factors (Label H) ↥(states (E : ℤ))
      (Channel H (PlusStates H E s)) (Channel H (MinusStates H E s)) where
  plusLeft i α k :=
    let L := order (weight i.val) k.1.2.val
    if i.val.card = k.1.1.val then
      multiplier L k.2.1 * Y i.val (-s-1-L+k.2.1) α.val k.2.2.val else 0
  plusRight j β k :=
    if k.1 = tag j then Y j.val (s-k.2.1) k.2.2.val β.val else 0
  minusLeft i β k :=
    let L := order (weight i.val) k.1.2.val
    if i.val.card = k.1.1.val then
      -multiplier L k.2.1 * (-1)^(i.val.card*k.1.1.val) *
        Y i.val (-s-1-L+k.2.1) k.2.2.val β.val else 0
  minusRight j α k :=
    if k.1 = tag j then Y j.val (s-k.2.1) α.val k.2.2.val else 0

private theorem split_entry {C : State → State → ℤ} {Y : ModeMatrix}
    (h : CoefficientIdentity C Y)
    (hzero : ∀ i j : State, i.card ≠ j.card → C i j = 0)
    {H E : ℕ} {s : ℤ} (i j : Label H) (α β : ↥(states (E : ℤ))) :
    (split Y H E s).entry i j α β = C i.val j.val * (if α = β then 1 else 0) := by
  unfold Factors.entry split
  dsimp only
  conv_lhs => simp only [Channel, mul_ite, mul_zero, Fintype.sum_prod_type, Prod.ext_iff, ite_and,
    Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true, tag]
  by_cases he : i.val.card = j.val.card
  · simp only [ite_eq_left he]
    rw [h H E s i j he α β, ← sum_add_distrib]
    refine sum_congr rfl (fun a _ ↦ ?_)
    simp only [mul_sub, mul_sum]
    congr 1
    · exact sum_congr rfl (fun _ _ ↦ by ring)
    · rw [← Finset.sum_neg_distrib]
      exact sum_congr rfl (fun _ _ ↦ by ring)
  · simp [he, hzero i.val j.val he]

/-- Multiplying in the first label removes the unimodular pairing without
altering the size of either channel. -/
def Factors.rowMap {I A P M : Type*} [Fintype I] (F : Factors I A P M) (B : Matrix I I ℤ) :
    Factors I A P M where
  plusLeft i α k := ∑ l, B i l * F.plusLeft l α k
  plusRight := F.plusRight
  minusLeft i β k := ∑ l, B i l * F.minusLeft l β k
  minusRight := F.minusRight

theorem Factors.rowMap_entry {I A P M : Type*} [Fintype I] [Fintype P] [Fintype M]
    (F : Factors I A P M) (B : Matrix I I ℤ) (i j : I) (α β : A) :
    (F.rowMap B).entry i j α β = ∑ l, B i l * F.entry l j α β := by
  simp only [Factors.rowMap, Factors.entry, sum_mul, mul_add, mul_sum, mul_assoc, sum_add_distrib]
  congr 1 <;> rw [sum_comm]

/-- Inverting the state pairing on the first leg produces the desired tensor
of two independent identities. Both shift signs use the same integer matrices. -/
theorem exists_integral_factors {C : State → State → ℤ} {Y : ModeMatrix}
    (h : CoefficientIdentity C Y)
    (hzero : ∀ i j : State, i.card ≠ j.card → C i j = 0)
    (H E : ℕ) (s : ℤ) (B : Matrix (Label H) (Label H) ℤ)
    (hB : B * (Matrix.of fun i j : Label H ↦ C i.val j.val) = 1) :
    ∃ F : Factors (Label H) ↥(states (E : ℤ)) (Channel H (PlusStates H E s))
      (Channel H (MinusStates H E s)),
      ∀ i j α β, F.entry i j α β = if i=j ∧ α=β then 1 else 0 := by
  refine ⟨(split Y H E s).rowMap B, fun i j α β ↦ ?_⟩
  rw [Factors.rowMap_entry]
  simp_rw [split_entry h hzero, ← mul_assoc]
  rw [← sum_mul]
  change ((B * (Matrix.of fun i j : Label H ↦ C i.val j.val)) i j) * _ = _
  rw [hB, Matrix.one_apply]
  split_ifs <;> simp_all

end Fermion

end

end SpectralBooks
end LinearAlgebra
end OAI
