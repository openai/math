import OAI.Computability.BorderVNP.PackedLookup
import OAI.Computability.BorderVNP.CoverDeck

/-! # Circuit realizations of the deck fiber histograms

One hardwired query per residue reads its entire dynamic bin. Signed entries
are represented as the difference of two nonnegative channels.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistogram

open ParseBatchSort VPVNP.VerifierNetwork

variable {G H P σ : Type*} [Fintype G] [Fintype H] [Fintype P] [Fintype σ] [DecidableEq H]
variable {b k w : ℕ}

/-- Hardwire one marker per residue and sum every source row in its bucket. -/
noncomputable def deck (e : Fin (2^b) ≃ Rows G H P) (index : H ↪ Fin (2^k))
    (keys : G → Fin k → Expr σ) (entries : G → Fin w → Expr σ) : Frame σ (H × Fin w) :=
  queries e keys entries (fun c => fixed (index c))

/-- Per-residue integer bounds suffice for the bit circuit, including dynamically computed bins. -/
theorem deck_value (e : Fin (2^b) ≃ Rows G H P) (index : H ↪ Fin (2^k))
    (keys : G → Fin k → Expr σ) (entries : G → Fin w → Expr σ) (x : σ → Bool) (π : G → H)
    (hkey : ∀ u, wordValue x (keys u) = (index (π u)).val)
    (fits : ∀ h, CoverDeck.histogram π (fun u => wordValue x (entries u)) h < 2^w) (c : H) :
    value (fun j => (deck e index keys entries).eval x (c,j)) =
      CoverDeck.histogram π (fun u => wordValue x (entries u)) c := by
  classical
  have eq (h : H) : (∑ u, if wordValue x (keys u) = (index h).val then wordValue x (entries u) else 0) =
      CoverDeck.histogram π (fun u => wordValue x (entries u)) h := by
    simp [CoverDeck.histogram, CoverDeck.fiber, Finset.sum_filter, hkey, Fin.val_inj, index.injective.eq_iff]
  have hf (a : ℕ) : (∑ u, if wordValue x (keys u) = a then wordValue x (entries u) else 0) < 2^w := by
    by_cases ha : ∃ h, (index h).val = a
    · obtain ⟨h,rfl⟩ := ha
      exact (eq h).trans_lt (fits h)
    · have hn (u) : wordValue x (keys u) ≠ a := fun he => ha ⟨π u, (hkey u).symm.trans he⟩
      simp [hn]
  rw [deck, queries_value _ _ _ _ _ hf, fixed_value, eq]

/-- The difference of the two computed channels gives the signed integer histogram in §5.3. -/
theorem deck_signed (e : Fin (2^b) ≃ Rows G H P) (index : H ↪ Fin (2^k))
    (keys : G → Fin k → Expr σ) (positive negative : G → Fin w → Expr σ) (x : σ → Bool)
    (π : G → H) (entry : G → ℤ) (hkey : ∀ u, wordValue x (keys u) = (index (π u)).val)
    (hentry : ∀ u, (wordValue x (positive u) : ℤ) - wordValue x (negative u) = entry u)
    (hp : ∀ h, CoverDeck.histogram π (fun u => wordValue x (positive u)) h < 2^w)
    (hn : ∀ h, CoverDeck.histogram π (fun u => wordValue x (negative u)) h < 2^w) (c : H) :
    (value (fun j => (deck e index keys positive).eval x (c,j)) : ℤ) -
      value (fun j => (deck e index keys negative).eval x (c,j)) = CoverDeck.histogram π entry c := by
  rw [deck_value e index keys positive x π hkey hp, deck_value e index keys negative x π hkey hn]
  simp only [CoverDeck.histogram, Nat.cast_sum, ← Finset.sum_sub_distrib, hentry]

end PackedHistogram

end BorderVNP
end Computability
end OAI
