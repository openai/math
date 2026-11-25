import OAI.Computability.BorderVNP.PackedSewnFragmentPair
import OAI.Computability.BorderVNP.PackedSewnFragmentCanonical
import OAI.Computability.BorderVNP.PackedSewnFragmentScanImage
import OAI.Computability.BorderVNP.PackedSewnFragmentSortCover

/-! # Public sparse circuit for the maximal exterior sewing intervals

Starting with unordered physical fragments, the circuit removes empty rows,
sorts by site and old start, combines every continuing translation or zero
clamp, and canonicalizes the absent-source word. All fields of a maximal row
are carried in its first physical slot in the sorted order.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.SewnField.Fragment

open VPVNP.VerifierNetwork

variable {n w old next : ℕ}

/-- Complete sparse maximal-run compiler, including physical sorting and clamp formatting. -/
noncomputable def maximal (n w : ℕ) : Frame (Pin n w) (Pin n w) :=
  ((canonical n w).subst (scan (pair w) n)).subst (sortedFrame n w)

/-- The raw gate count is linear in the number of physical fragment slots and cubic
in the public word width plus the logarithm of the sparse rectangle. -/
theorem maximal_size (n w : ℕ) : (maximal n w).size ≤
    3000*(n+1)*(w + Nat.clog 2 n + 1)^3 := by
  let W := w + Nat.clog 2 n + 1
  have pos : 1 ≤ W := by dsimp [W]; omega
  have hw : w+1 ≤ W := by dsimp [W]; omega
  have hlog : Nat.clog 2 n ≤ W := by dsimp [W]; omega
  have q : W^2 ≤ W^3 := Nat.pow_le_pow_right pos (by decide)
  have l : W ≤ W^3 := by simpa using Nat.pow_le_pow_right pos (by decide : 1≤3)
  have a : n*(2+4*w)*(30*w+6) ≤ 120*(n+1)*W^3 := by
    have row : 2+4*w ≤ 4*W := by omega
    have flag : 30*w+6 ≤ 30*W := by omega
    exact (Nat.mul_le_mul (Nat.mul_le_mul (Nat.le_succ _) row) flag).trans
      ((by ring : (n+1)*(4*W)*(30*W) = 120*(n+1)*W^2).trans_le (Nat.mul_le_mul_left _ q))
  have b : 2*(n+1)*(6*w+4)*2 ≤ 24*(n+1)*W^3 := by
    have row : 6*w+4 ≤ 6*W := by omega
    exact (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left (2*(n+1)) row)).trans
      ((by ring : 2*(n+1)*(6*W)*2 = 24*(n+1)*W).trans_le (Nat.mul_le_mul_left _ l))
  have c : (Nat.clog 2 n)^2 * (2*(n+1)*(24*(6*w+4)+1)) ≤ 290*(n+1)*W^3 := by
    have row : 24*(6*w+4)+1 ≤ 145*W := by omega
    exact (Nat.mul_le_mul (Nat.pow_le_pow_left hlog 2) (Nat.mul_le_mul_left _ row)).trans_eq (by ring)
  have d : n*(pair w).size ≤ 2000*(n+1)*W^3 := by
    exact (Nat.mul_le_mul (Nat.le_succ _) ((pair_size_quadratic w).trans (Nat.mul_le_mul_left _
      ((Nat.pow_le_pow_left hw 2).trans q)))).trans_eq (by simp only [Nat.succ_eq_add_one]; ring)
  have f : n*(2+4*w)*3 ≤ 12*(n+1)*W^3 := by
    have row : 2+4*w ≤ 4*W := by omega
    exact (Nat.mul_le_mul_right _ (Nat.mul_le_mul (Nat.le_succ _) row)).trans
      ((by ring : (n+1)*(4*W)*3 = 12*(n+1)*W).trans_le (Nat.mul_le_mul_left _ l))
  unfold maximal
  rw [Frame.subst_size,Frame.subst_size]
  apply (Nat.add_le_add (sortedFrame_size n w) (Nat.add_le_add (scan_size _ n) canonical_size)).trans
  change _ ≤ 3000*(n+1)*W^3
  calc _ ≤ 120*(n+1)*W^3 + 24*(n+1)*W^3 + 290*(n+1)*W^3 + (2000*(n+1)*W^3 + 12*(n+1)*W^3) :=
             Nat.add_le_add (Nat.add_le_add (Nat.add_le_add a b) c) (Nat.add_le_add d f)
       _ ≤ _ := by rw [show 3000*(n+1)*W^3 = 3000*((n+1)*W^3) by ring]; simp only [Nat.mul_assoc]; omega

/-- A clamped row has a zero source word on its actual public output wires. -/
theorem maximal_clamp (x : Pin n w → Bool) (i : Fin n) (off : (maximal n w).eval x (i,.inl true)=false) :
    word (fun j => (maximal n w).eval x (i,j)) 3 = 0 := by
  simp only [maximal,Frame.subst_eval] at off ⊢
  exact canonical_clamp _ i off

/-- The physical output has exactly the sparse, chronologically coalesced list. -/
theorem maximal_list (x : Pin n w → Bool) (fit : ∀ a ∈ list x, 0 < a.run.width → a.Fits w) :
    list ((maximal n w).eval x) = coalesce (list ((sortedFrame n w).eval x)) := by
  let y := (sortedFrame n w).eval x
  have correct := sortedFrame_values x
  have compact : Compact y := fun i j hij live => (correct.compact i).mpr (Nat.lt_of_le_of_lt hij ((correct.compact j).mp live))
  have hfit (a) (ha : a ∈ list y) := List.mem_filter.mp (correct.perm.subset ha)
  have allFit (a) (ha : a ∈ list y) := fit a (hfit a ha).1 (of_decide_eq_true (hfit a ha).2)
  have output : (maximal n w).eval x = (canonical n w).eval ((scan (pair w) n).eval y) := by
    funext i
    simp [maximal,Frame.subst_eval,y]
  rw [output,canonical_list]
  exact (scan_state _ (pair_spec w) n y compact allFit).1

/-- Each actual site sees precisely its mathematical maximal partial translations.
The raw rectangle may interleave arbitrary owners, and empty fragments are ignored. -/
theorem maximal_siteRuns (x : Pin n w → Bool) (fit : ∀ a ∈ list x, 0 < a.run.width → a.Fits w)
    (v : ℕ) (read : Fin old → Option (Fin next)) (roster : List Interval)
    (rows : (siteRuns v (list x)).Perm roster) (tiles : Partition old 0 roster)
    (good : ∀ p ∈ roster, Good read p) :
    siteRuns v (list ((maximal n w).eval x)) = intervals read := by
  rw [maximal_list x fit]
  exact (sortedFrame_values x).coalesced_siteRuns v read roster rows tiles good

/-- The true input may be supplied solely as an unordered, uniquely covering physical
roster. No predecessor bit is an input pin to the coalescing circuit. -/
theorem maximal_siteRuns_of_cover (x : Pin n w → Bool) (fit : ∀ a ∈ list x, 0 < a.run.width → a.Fits w)
    (v : ℕ) (read : Fin old → Option (Fin next)) (cover : Covers (siteRuns v (list x)) read)
    (one : UniqueCover old (siteRuns v (list x))) :
    siteRuns v (list ((maximal n w).eval x)) = intervals read := by
  rw [maximal_list x fit]
  exact (sortedFrame_values x).coalesced_siteRuns_of_cover v read cover.oldFit one
    (fun p hp j hj k hk => cover.agrees p hp j hj k hk)

end Packing.SewnField.Fragment

end BorderVNP
end Computability
end OAI
