import OAI.LinearAlgebra.SpectralBooks.Increment
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Algebra.Group.Pointwise.Finset.Basic
import Mathlib.Tactic

/-! # Adding a segment to a polytope

The homogeneous-flat part of the flat diagonal law glues together translated
vertex lists along the direction of a segment. Intersecting submodularity
controls the price of every successive translate.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open scoped Pointwise

variable {E : Type*} [NormedAddCommGroup E] [DecidableEq E]

private def translates (S : Finset E) (v : E) : ℕ → Finset E
  | 0 => S
  | n + 1 => S ∪ (translates S v n + {v})

private theorem subset_translates (S : Finset E) (v : E) (n : ℕ) :
    S ⊆ translates S v n := by
  cases n with
  | zero => rfl
  | succ n => exact Finset.subset_union_left

private theorem mem_lastTranslate {S : Finset E} {x : E} (hx : x ∈ S) (v : E) (n : ℕ) :
    x + n • v ∈ translates S v n := by
  induction n with
  | zero => simpa [translates] using hx
  | succ n ih =>
    apply Finset.mem_union_right
    rw [succ_nsmul, ← add_assoc]
    exact Finset.add_mem_add ih (Finset.mem_singleton_self _)

private theorem price_translates_le (δ : Finset E → ℝ)
    (hmono : ∀ ⦃S T : Finset E⦄, S.Nonempty → S ⊆ T → δ S ≤ δ T)
    (htrans : ∀ (S : Finset E), S.Nonempty → ∀ v : E, δ (S + {v}) = δ S)
    (hsubmod : IntersectingSubmodular δ) (S : Finset E) (hS : S.Nonempty) (v : E) (n : ℕ) :
    δ (translates S v n) ≤ δ S + n * (δ (S ∪ (S + {v})) - δ S) := by
  induction n with
  | zero => simp [translates]
  | succ n ih =>
    let P := translates S v n
    have hSP : S ⊆ P := subset_translates S v n
    have hP := hS.mono hSP
    let X := P + {v}
    let B := S ∪ (S + {v})
    have hSX : S + {v} ⊆ X := Finset.add_subset_add_right hSP
    have hSB : S + {v} ⊆ B := Finset.subset_union_right
    have hSI : S + {v} ⊆ X ∩ B := Finset.subset_inter hSX hSB
    have hS' : (S + {v}).Nonempty := hS.add (Finset.singleton_nonempty _)
    have hU : X ∪ B = translates S v (n+1) := by
      change X ∪ (S ∪ (S + {v})) = S ∪ X
      ext x
      simp only [Finset.mem_union]
      grind
    have hstep := hsubmod (A := X) (B := B) (hS'.mono hSI)
    have hinter := hmono hS' hSI
    have hX : δ X = δ P := htrans P hP v
    rw [hU, hX] at hstep
    rw [htrans S hS v] at hinter
    dsimp [B, P] at hstep
    push_cast
    linarith

variable [NormedSpace ℝ E]

/-- For a translation-invariant, monotone, intersecting-submodular price which is
subadditive for Minkowski addition and agrees with distance on pairs, adding
a segment of displacement `v` increases the price by exactly `‖v‖`. -/
theorem price_add_segment (δ : Finset E → ℝ)
    (hmono : ∀ ⦃S T : Finset E⦄, S.Nonempty → S ⊆ T → δ S ≤ δ T)
    (htrans : ∀ (S : Finset E), S.Nonempty → ∀ v : E, δ (S + {v}) = δ S)
    (hsubmod : IntersectingSubmodular δ)
    (hsubadd : ∀ (S T : Finset E), S.Nonempty → T.Nonempty → δ (S + T) ≤ δ S + δ T)
    (hpair : ∀ x y : E, δ {x, y} = dist x y)
    (S : Finset E) (hS : S.Nonempty) (v : E) :
    δ (S + {0, v}) = δ S + ‖v‖ := by
  have hseg : S + {0, v} = S ∪ (S + {v}) := by
    rw [show ({0, v} : Finset E) = {0} ∪ {v} by simp, Finset.add_union]
    change S + 0 ∪ (S + {v}) = _
    rw [add_zero]
  apply le_antisymm
  · simpa [hpair] using hsubadd S {0, v} hS (Finset.insert_nonempty _ _)
  rw [hseg]
  obtain ⟨x, hx⟩ := hS
  by_contra! hlt
  have hgap : 0 < ‖v‖ - (δ (S ∪ (S + {v})) - δ S) := by linarith
  obtain ⟨n, hn⟩ := exists_nat_gt (δ S / (‖v‖ - (δ (S ∪ (S + {v})) - δ S)))
  have hlarge := (div_lt_iff₀ hgap).mp hn
  have hupper := price_translates_le δ hmono htrans hsubmod S ⟨x, hx⟩ v n
  have hmem : ({x, x + n • v} : Finset E) ⊆ translates S v n := by
    simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
    exact ⟨subset_translates S v n hx, mem_lastTranslate hx v n⟩
  have hlower := hmono (Finset.insert_nonempty _ _) hmem
  rw [hpair, dist_eq_norm', add_sub_cancel_left, ← Nat.cast_smul_eq_nsmul ℝ, norm_smul,
    Real.norm_natCast] at hlower
  linarith

end SpectralBooks
end LinearAlgebra
end OAI
