import OAI.ThreeFlat.Routing.SpillBankAssembly
import OAI.ThreeFlat.Routing.SpillGreedySpec

namespace OAI
/-! # Semantics of the two-pass bank selector

The primary and reserve slots are disjoint under the public address equivalence.
The selected links therefore describe one embedding of all active requests.
-/

noncomputable section
open scoped Classical

namespace ThreeFlat.Routing.Spill
open Concentrator

variable {C q D R : ℕ} (B : TwoPassBank C q D R)

/-- On a legal mask the sparse-mixing estimate clears the remaining requests by the public deadline. -/
theorem bank_live_empty_of_legal (A : Finset (Fin (C*R))) (P : Candidate (primaryBoard B) → Bool)
    (valid : PrimaryValid (primaryBoard B) (fun i => decide (i ∈ A)) P)
    (legal : q*A.card+R ≤ q*R) :
    B.G.live B.slots (missedPrimary A (primaryBoard B) P) (Nat.log 2 (C*R)+1) = ∅ := by
  have hmiss := missedPrimary_eq_run (A := A) (fun _ => decide_eq_true_iff) valid
  have sorted : (fun i => ((primaryBoard B) i).sort (· ≤ ·)) = B.N := funext B.sorted
  rw [sorted] at hmiss
  have small := B.missed (A.sort (· ≤ ·)) (by simpa using legal)
  apply B.G.finished_of_sparse_mixing (all := Finset.univ) (Finset.subset_univ _) B.slots
  · intro H hh
    rw [hmiss] at hh
    exact B.sparse H (hh.trans (Nat.mul_le_mul_left 2 small.le))
  · rw [hmiss]
    exact small.trans_le (B.thresholdBound.trans (Nat.lt_pow_succ_log_self (by decide : 1 < 2) _).le)

/-- The selected primary and reserve bits are precisely the public edges of one injection. -/
theorem boardPick_eq_injectionPins (A : Finset (Fin (C*R))) (cap : ℕ)
    (P : Candidate (primaryBoard B) → Bool)
    (valid : PrimaryValid (primaryBoard B) (fun i => decide (i ∈ A)) P)
    (done : B.G.live B.slots (missedPrimary A (primaryBoard B) P) cap = ∅) :
    ∃ f : A ↪ Fin R, (∀ a, f a ∈ fullBoard B a.val) ∧
      boardPick B P (reservePick B.G (reserveReports B.G B.slots cap
        (missedPrimary A (primaryBoard B) P))) = injectionPins A f := by
  apply assemble_bank_injection B A _ cap P _ _ (selected_primary_injective valid)
    (fun _ => Finset.mem_filter) done
  · intro i r hp
    by_contra hin
    rw [valid i r] at hp
    simp [winner,hin] at hp
  · intro i r s hr hs
    exact Option.some.inj ((of_decide_eq_true ((valid i r).symm.trans hr)).symm.trans
      (of_decide_eq_true ((valid i s).symm.trans hs)))

end ThreeFlat.Routing.Spill

end
end OAI
