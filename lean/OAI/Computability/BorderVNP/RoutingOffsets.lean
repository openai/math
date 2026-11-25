import OAI.Computability.BorderVNP.RoutingSchedule

/-!
# Constant-cost queries of the public routing schedule

A relay number is obtained by skipping the two ordered endpoints. Its rank is
obtained by undoing those skips. These formulas use comparisons and unit
increments in place of a search through the relay pool. Prefix sums can be
tabulated in public work; accessing an individual routed bit then needs one
table lookup, one quotient and one addition.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Routing

open Finset

variable {R : ℕ}

/-- Insert one missing team number in an increasing enumeration. -/
def skip (missing i : ℕ) : ℕ := if i < missing then i else i + 1

/-- Inverse ordinal on all teams other than the missing one. -/
def unskip (missing i : ℕ) : ℕ := if i ≤ missing then i else i - 1

private theorem unskip_skip (m i : ℕ) : unskip m (skip m i) = i := by
  unfold skip unskip
  split_ifs <;> omega

private theorem skip_strictMono (m : ℕ) : StrictMono (skip m) := by
  intro a b hab
  unfold skip
  split_ifs <;> omega

/-- Evaluate a relay ordinal without constructing the pool as a list. -/
def skipEnds (u w : Fin R) (i : Fin (R - 2)) : Fin R :=
  ⟨skip (max u w).val (skip (min u w).val i.val), by
    have hi := i.isLt
    unfold skip
    split_ifs <;> omega⟩

private theorem skipEnds_eq {u w : Fin R} (h : u ≠ w) :
    skipEnds u w = (pool u w).orderEmbOfFin (pool_card h) := by
  apply orderEmbOfFin_unique
  · intro i
    have avoid {a b : ℕ} (hab : a < b) (j : ℕ) :
        skip b (skip a j) ≠ a ∧ skip b (skip a j) ≠ b := by
      unfold skip
      split_ifs <;> omega
    have tofin (v : Fin R) : skipEnds u w i ≠ v ↔ (skipEnds u w i).val ≠ v.val :=
      not_congr Fin.ext_iff
    simp only [pool, mem_erase, mem_univ, and_true]
    rw [tofin w, tofin u]
    change skip _ (skip _ _) ≠ w.val ∧ skip _ (skip _ _) ≠ u.val
    rcases lt_or_gt_of_ne h with hlt | hgt
    · rw [min_eq_left hlt.le, max_eq_right hlt.le]
      exact (avoid hlt i.val).symm
    · rw [min_eq_right hgt.le, max_eq_left hgt.le]
      exact avoid hgt i.val
  · intro i j hij
    exact skip_strictMono _ (skip_strictMono _ hij)

/-- Only one modulo and two comparisons with the endpoints are needed to
choose the intermediate team of a particular wire bit. -/
theorem relay_formula (hR : 2 < R) {u w : Fin R} (h : u ≠ w) (j : ℕ) :
    (relay hR h j).val = skip (max u w).val (skip (min u w).val (j % (R-2))) := by
  unfold relay
  rw [← skipEnds_eq h]
  rfl

/-- The opposite direction for the public schedule uses two comparisons and
at most two subtractions to find the ordinal of a particular relay. -/
theorem relayRank_formula {u w v : Fin R} (h : u ≠ w) (hv : v ∈ pool u w) :
    (relayRank h hv).val = unskip (min u w).val (unskip (max u w).val v.val) := by
  have hx : (pool u w).orderEmbOfFin (pool_card h) (relayRank h hv) = v := by
    change (((pool u w).orderIsoOfFin (pool_card h)) (((pool u w).orderIsoOfFin (pool_card h)).symm
      ⟨v, hv⟩)).val = v
    rw [OrderIso.apply_symm_apply]
  rw [← skipEnds_eq h] at hx
  have he := congrArg Fin.val hx
  change skip _ (skip _ (relayRank h hv).val) = v.val at he
  rw [← he, unskip_skip, unskip_skip]

/-- The public interval length uses a constant number of word operations,
regardless of the number of wires in this pair. -/
theorem scheduledLength_formula (u w v : Fin R) (width : ℕ) :
    scheduledLength u w v width =
      if u ≠ w ∧ v ≠ u ∧ v ≠ w then
        strideCount (R - 2) (unskip (min u w).val (unskip (max u w).val v.val)) width
      else 0 := by
  by_cases h : u ≠ w
  · by_cases hv : v ∈ pool u w
    · have ends : v ≠ u ∧ v ≠ w := by simpa [pool, and_comm] using hv
      rw [scheduledLength, dite_eq_left h, dite_eq_left hv, relayRank_formula h hv,
        ite_eq_left ⟨h, ends⟩]
    · have ends : ¬ (u ≠ w ∧ v ≠ u ∧ v ≠ w) := fun x ↦ hv (by simpa [pool, and_comm] using x.2)
      rw [scheduledLength, dite_eq_left h, dite_eq_right hv, ite_eq_right ends]
  · simp [scheduledLength, h]

/-- The tabulated base of the demand interval for `w` in one direction of a
physical block. There is one table entry per ordered triple of teams. -/
def baseOffset (width : Fin R → Fin R → ℕ) (u v w : Fin R) : ℕ :=
  ∑ i : Fin w.val, let y := Fin.castLE w.isLt.le i
    scheduledLength u y v (demand width u y)

/-- The table is computed successively in partner order. One new length and
one addition produce each next entry; previous entries are reused. -/
theorem baseOffset_next (width : Fin R → Fin R → ℕ) (u v : Fin R) (j : ℕ) (hj : j+1 < R) :
    let w : Fin R := ⟨j, by omega⟩
    baseOffset width u v ⟨j + 1, hj⟩ =
      baseOffset width u v w + scheduledLength u w v (demand width u w) := by
  dsimp only [baseOffset]
  rw [Fin.sum_univ_castSucc]
  rfl

/-- Once the base table is stored, an individual wire does not scan other
wires or other teams to obtain its position. -/
theorem lookup_address (hR : 2 < R) (width : Fin R → Fin R → ℕ) (u v : Fin R)
    (p : Hop hR width u v) :
    (legEquiv hR width u v p).val = baseOffset width u v p.1 + p.2.val / (R - 2) :=
  legEquiv_address hR width u v p

/-- A public table with all directions and partners has exactly cubic size. -/
theorem baseTable_size (R : ℕ) : Fintype.card (Fin R × Fin R × Fin R) = R ^ 3 := by
  simp [pow_succ, mul_assoc]

end Routing

end BorderVNP
end Computability
end OAI
