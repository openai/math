import OAI.Computability.BorderVNP.RoutingISATableBounds

/-! # The scheduler's word image gives the abstract routing address tables -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA

open Finset

/-- The unordered pair-width array as the matrix required by the round-robin layout. -/
def TableLayout.widthMatrix (l : TableLayout) (row : ℕ → TableRow) (u v : Fin l.teams) : ℕ :=
  l.pairWidth row l.count (u.val*l.teams+v.val)

/-- The word-level partner length equals the public schedule's list length. -/
theorem TableLayout.partnerLength_eq (l : TableLayout) (row : ℕ → TableRow) (u v j : Fin l.teams) :
    l.partnerLength row u v j = Routing.scheduledLength u j v (Routing.demand (l.widthMatrix row) u j) := by
  simp only [TableLayout.partnerLength, u.isLt, v.isLt, j.isLt, and_self, dite_true]
  by_cases h : u = j
  · subst j
    simp [Routing.scheduledLength]
  · rw [Routing.demand, ite_eq_right h]
    rfl

/-- Every word of the cubic prefix array equals its corresponding abstract base offset. -/
theorem TableLayout.legPrefix_eq_baseOffset (l : TableLayout) (row : ℕ → TableRow) (u v j : Fin l.teams) :
    l.legPrefix row u v j = Routing.baseOffset (l.widthMatrix row) u v j := by
  rw [TableLayout.legPrefix, ← Fin.sum_univ_eq_sum_range]
  exact Finset.sum_congr rfl fun i _ => l.partnerLength_eq row u v (Fin.castLE j.isLt.le i)

/-- The square array of used lengths agrees with the oriented load computed from actual
cyclic relay assignment. -/
theorem TableLayout.legPrefix_eq_legLoad (l : TableLayout) (row : ℕ → TableRow) (hR : 2 < l.teams)
    (u v : Fin l.teams) : l.legPrefix row u v l.teams = Routing.legLoad hR (l.widthMatrix row) u v := by
  rw [TableLayout.legPrefix, ← Fin.sum_univ_eq_sum_range]
  exact Finset.sum_congr rfl fun j _ => (l.partnerLength_eq row u v j).trans (Routing.scheduledLength_eq ..)

/-- The four constructed arrays and the complement of their allocated workspace. -/
structure TableLayout.Image (l : TableLayout) (row : ℕ → TableRow) (before after : ℕ → ℕ) : Prop where
  /-- The square width table includes the unused lower triangle. -/
  widths : ∀ k < l.teams^2, after (l.widths+k) = l.pairWidth row l.count k
  /-- Record ordinals agree with the prefix before that record. -/
  ordinals : ∀ i < l.count, after (l.ordinals+i) = l.ordinal row i
  /-- Every oriented partner prefix is present. -/
  offsets : ∀ u < l.teams, ∀ v < l.teams, ∀ j < l.teams,
    after (tripleIndex l.offsets l.teams u v j) = l.legPrefix row u v j
  /-- All oriented totals are present. -/
  totals : ∀ u < l.teams, ∀ v < l.teams,
    after (pairIndex l.used l.teams u v) = l.legPrefix row u v l.teams
  /-- No memory outside the four output arrays was written. -/
  outside : ∀ x, ¬ l.contains .widths x → ¬ l.contains .ordinals x →
    ¬ l.contains .offsets x → ¬ l.contains .used x → after x = before x

/-- The constructed physical arrays satisfy the frame-addressed `AddressTables`
predicate consumed by the endpoint and relay code. -/
theorem TableLayout.Image.addressTables {l : TableLayout} {row : ℕ → TableRow} {w : ℕ}
    {before after : ℕ → ℕ} (image : l.Image row before after) (al : l.Allocated w)
    (pub : Arg → ℕ) (hf : pub 0 = l.frame) (loaded : l.frameFields before) :
    AddressTables al.teamCount (l.widthMatrix row) pub after := by
  have frame (i : ℕ) (hi : i < 21) : frameField pub after i = before (l.frame+i) := by
    rw [frameField, hf]
    have inside := l.contains_offset (a := .frame) hi
    exact image.outside _ (al.separate .frame .widths _ (by decide) inside)
      (al.separate .frame .ordinals _ (by decide) inside)
      (al.separate .frame .offsets _ (by decide) inside)
      (al.separate .frame .used _ (by decide) inside)
  obtain ⟨ht,_,_,_,ho,hu,_⟩ := loaded
  refine ⟨(frame 1 (by decide)).trans ht, fun u v j => ?_, fun u v => ?_⟩
  · rw [frame 17 (by decide), ho, image.offsets _ u.isLt _ v.isLt _ j.isLt]
    exact l.legPrefix_eq_baseOffset row u v j
  · rw [frame 18 (by decide), hu, image.totals _ u.isLt _ v.isLt]
    exact l.legPrefix_eq_legLoad row al.teamCount u v

end RoutingISA

end BorderVNP
end Computability
end OAI
