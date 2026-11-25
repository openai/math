import OAI.Computability.BorderVNP.ShortenSeedIntervals
import Mathlib.Order.Interval.Finset.Fin

/-!
# Computing a bin ordinal from public cable names and widths

The order is exactly the allocator's lexicographic order. A segmented prefix
sum over the cable descriptors therefore supplies the ordinal of every bit
of a cable, without enumerating its bit positions.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Shortening.SeedIntervals

open Crossing
open scoped Classical BigOperators

variable {D : ℕ} {P : Type*} {bits : P → ℕ} (N : Network D P bits)
variable {A : Type} (bin : N.Edge → Option A)

/-- Public finite name used in the allocator's cable sort. -/
noncomputable def cableName (e : N.Edge) : ℕ := (Fintype.equivFin N.Edge e).val

/-- Prefix sum of all earlier cable widths in the same bin. -/
noncomputable def cableOffset (a : A) (e : N.Edge) : ℕ :=
  ∑ c : {c : N.Edge // bin c = some a},
    if cableName N c.val < cableName N e then N.width c.val else 0

private theorem count_below {n : ℕ} (k : Fin n) : (∑ i : Fin n, if i < k then 1 else 0) = k.val := by
  rw [← Finset.sum_filter]
  have h : (Finset.univ.filter fun i => i < k) = Finset.Iio k := by ext; simp
  rw [h]
  simp [Fin.card_Iio]

private theorem rank_lt_iff (a : A) (u v : BinBits N bin a) :
    rank N bin a u < rank N bin a v ↔ cableName N u.1.val < cableName N v.1.val ∨
      ∃ h : u.1 = v.1, h ▸ u.2 < v.2 := by
  let : LinearOrder N.Edge := LinearOrder.lift' (Fintype.equivFin N.Edge) (Fintype.equivFin N.Edge).injective
  let iso := (Fintype.orderIsoFinOfCardEq (Lex (BinBits N bin a)) rfl).symm
  exact iso.lt_iff_lt.trans Sigma.Lex.lt_def

/-- The sorted global ordinal equals the segmented prefix sum plus the original local ordinal. -/
theorem rank_eq_offset (a : A) (e : {e : N.Edge // bin e = some a}) (k : Fin (N.width e.val)) :
    (rank N bin a ⟨e,k⟩).val = cableOffset N bin a e.val + k.val := by
  let r := rank N bin a
  let x : BinBits N bin a := ⟨e,k⟩
  rw [← count_below (r x), ← r.sum_comp (fun i => if i < r x then 1 else 0), Fintype.sum_sigma]
  have hf (c : {c : N.Edge // bin c = some a}) :
      (∑ t : Fin (N.width c.val), if r ⟨c,t⟩ < r x then 1 else 0) =
        (if cableName N c.val < cableName N e.val then N.width c.val else 0) +
          (if c = e then k.val else 0) := by
    by_cases he : c = e
    · subst c
      simp only [lt_irrefl, ite_false, ite_true, zero_add]
      have h (t : Fin (N.width e.val)) : r ⟨e,t⟩ < r x ↔ t < k := by
        rw [rank_lt_iff]
        simp [x]
      simp_rw [h]
      exact count_below k
    · have h (t : Fin (N.width c.val)) :
          r ⟨c,t⟩ < r x ↔ cableName N c.val < cableName N e.val := by
        rw [rank_lt_iff]
        simp [x, he]
      simp_rw [h]
      by_cases hl : cableName N c.val < cableName N e.val <;> simp [hl, he]
  simp_rw [hf]
  rw [Finset.sum_add_distrib]
  simp [cableOffset]

/-- Equivalent formula on the complete descriptor list, masking other bins. -/
theorem cableOffset_eq_sum (a : A) (e : N.Edge) :
    cableOffset N bin a e = ∑ c, if bin c = some a ∧ cableName N c < cableName N e
      then N.width c else 0 := by
  unfold cableOffset
  rw [← Finset.sum_subtype (p := fun c => bin c = some a) (Finset.univ.filter (fun c => bin c = some a)) (fun c => by simp)
    (fun c => if cableName N c < cableName N e then N.width c else 0), Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro c _
  split_ifs <;> grind

end Shortening.SeedIntervals

end BorderVNP
end Computability
end OAI
