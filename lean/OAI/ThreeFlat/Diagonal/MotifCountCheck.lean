import OAI.ThreeFlat.Diagonal.MotifHistogram
import OAI.ThreeFlat.Routing.StableCompactionRank
import OAI.ThreeFlat.BitNetwork

namespace OAI
/-! # Checking private selector multiplicities by compacting constant ones

A stable compactor on a mask and all-one data emits exactly a unary encoding
of the population of the mask. One such check for each base tile establishes
the public histogram of the privately determined selector sequence.
-/

namespace ThreeFlat.Diagonal.MotifOuterTerms

open Routing.StableCompaction
open scoped BigOperators Classical

variable {r : ℕ} {F H : Type*} [CommSemiring F] [Fintype H] [DecidableEq H]

def unary (n : ℕ) (i : Fin r) : Bool := decide (i.val < n)

theorem compact_ones (m : Fin r → Bool) : compact m (fun _ => true) = unary (active m).card := by
  funext i
  simp [compact,unary]

private theorem unary_inj {a b : ℕ} (ha : a ≤ r) (hb : b ≤ r)
    (eq : unary (r := r) a = unary b) : a = b := by
  by_contra h
  rcases lt_or_gt_of_ne h with l|g
  · have u := congrFun eq ⟨a,l.trans_le hb⟩
    simp [unary,l] at u
  · have u := congrFun eq ⟨b,g.trans_le ha⟩
    simp [unary,g] at u

def symbolMask (s : Fin r → H) (h : H) (i : Fin r) := decide (s i = h)

private theorem symbol_count (s : Fin r → H) (h : H) :
    (active (symbolMask s h)).card = ((histogram s).val h).val := by
  simp [histogram,occurrence,active,symbolMask]

theorem count_check (N : BitNetwork F (r+(r+r)))
    (realizes : ∀ M X Y, N.eval (Fin.append M (Fin.append X Y)) = if Y = compact M X then 1 else 0)
    (s : Fin r → H) (v : Histogram H r) (h : H) :
    N.eval (Fin.append (symbolMask s h) (Fin.append (fun _ => true) (unary (v.val h).val))) =
      if v.val h = (histogram s).val h then 1 else 0 := by
  rw [realizes,compact_ones,symbol_count]
  congr 1
  apply propext
  exact ⟨fun e => Fin.ext (unary_inj (Nat.le_of_lt_succ (v.val h).isLt)
    (Nat.le_of_lt_succ ((histogram s).val h).isLt) e),fun e => by rw [e]⟩

/-- The coefficient of all the count checks is zero on every incorrect
histogram and one on the unique correct histogram. -/
theorem histogram_check (N : BitNetwork F (r+(r+r)))
    (realizes : ∀ M X Y, N.eval (Fin.append M (Fin.append X Y)) = if Y = compact M X then 1 else 0)
    (s : Fin r → H) (v : Histogram H r) :
    (∏ h, N.eval (Fin.append (symbolMask s h) (Fin.append (fun _ => true) (unary (v.val h).val)))) =
      if v = histogram s then 1 else 0 := by
  simp only [count_check N realizes]
  by_cases eq : v = histogram s
  · simp [eq]
  · obtain ⟨h,hh⟩ : ∃ h, v.val h ≠ (histogram s).val h :=
      not_forall.mp (fun he => eq (Subtype.ext (funext he)))
    rw [ite_eq_right eq]
    exact Finset.prod_eq_zero (Finset.mem_univ h) (ite_eq_right hh)

end ThreeFlat.Diagonal.MotifOuterTerms

end OAI
