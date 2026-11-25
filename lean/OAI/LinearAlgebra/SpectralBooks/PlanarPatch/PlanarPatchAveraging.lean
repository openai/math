import OAI.LinearAlgebra.SpectralBooks.PlanarPatch.PlanarPatchPartition
import OAI.LinearAlgebra.SpectralBooks.PortNetwork
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! # Boundary averaging after planar separator deletions

In the proof of the map-labels lemma, the components left after deleting
vertices have total edge boundary at most four times the number of deletions.
Each boundary edge joins a unique surviving component to a deleted vertex.
Parallel edges are counted separately through their identifiers.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

namespace PlanarPatch

open Finset
open scoped BigOperators

variable {V E : Type*} [DecidableEq V] [Fintype E]

/-- The edge identifiers incident to a vertex, ignoring their orientation. -/
def incidentEdges (tail head : E → V) (v : V) : Finset E :=
  univ.filter fun e => tail e = v ∨ head e = v

/-- The edge count is bounded by the port degree used in the manuscript:
a loop contributes two ports but only one edge identifier. -/
theorem card_incidentEdges_le_ports (G : PortGraph V E) (v : V) :
    (incidentEdges G.tail G.head v).card ≤ Fintype.card (G.Port v) := by
  let port (e : incidentEdges G.tail G.head v) : G.Port v :=
    if h : G.tail e = v then ⟨(e, false), h⟩
    else ⟨(e, true), ((mem_filter.mp e.property).2).resolve_left h⟩
  have hport (e : incidentEdges G.tail G.head v) : (port e).val.1 = e.val := by
    dsimp [port]
    split <;> rfl
  simpa using Fintype.card_le_of_injective port (fun e f hef =>
    Subtype.ext ((hport e).symm.trans ((congrArg (fun p : G.Port v => p.val.1) hef).trans (hport f))))

/-- Membership of a surviving block is constant across every surviving edge. -/
def EdgeClosed (tail head : E → V) (S P : Finset V) : Prop :=
  ∀ e, tail e ∈ S → head e ∈ S → (tail e ∈ P ↔ head e ∈ P)

omit [Fintype E] in
/-- A union of components of the induced simple graph is closed across the
original edges, including loops. -/
theorem edgeClosed_of_adj (tail head : E → V) (S P : Finset V)
    (hclosed : ∀ x ∈ P, ∀ y ∈ S, (underlying tail head).Adj x y → y ∈ P) :
    EdgeClosed tail head S P := by
  intro e ht hh
  by_cases he : tail e = head e
  · rw [he]
  have hadj : (underlying tail head).Adj (tail e) (head e) :=
    ⟨he, e, Or.inl ⟨rfl, rfl⟩⟩
  exact ⟨fun h => hclosed _ h _ hh hadj, fun h => hclosed _ h _ ht hadj.symm⟩

/-- The total boundary of separated blocks is charged to edges incident to
deleted vertices. The parameter `Δ` bounds their number at each such vertex. -/
theorem sum_boundary_le_deleted (tail head : E → V) (R D : Finset V)
    (blocks : Finset (Finset V)) (Δ : ℕ)
    (hcover : blocks.biUnion id = R \ D)
    (hdisj : (blocks : Set (Finset V)).PairwiseDisjoint id)
    (hclosed : ∀ P ∈ blocks, EdgeClosed tail head (R \ D) P)
    (hdeg : ∀ v ∈ D, (incidentEdges tail head v).card ≤ Δ) :
    ∑ P ∈ blocks, (boundary tail head R P).card ≤ Δ * D.card := by
  classical
  have hsurv {P : Finset V} (hP : P ∈ blocks) : P ⊆ R \ D := by
    rw [← hcover]
    exact fun _ hv => mem_biUnion.mpr ⟨P, hP, hv⟩
  have hcross {P : Finset V} (hP : P ∈ blocks) {e : E} (he : e ∈ boundary tail head R P) :
      (tail e ∈ P ∧ head e ∈ D) ∨ (head e ∈ P ∧ tail e ∈ D) := by
    simp only [boundary, mem_filter, mem_univ, true_and, mem_sdiff] at he
    obtain ⟨ht, hr, hn⟩ | ⟨hh, hr, hn⟩ := he
    · refine Or.inl ⟨ht, by_contra fun hd => hn ?_⟩
      exact (hclosed P hP e (hsurv hP ht) (mem_sdiff.mpr ⟨hr, hd⟩)).mp ht
    · refine Or.inr ⟨hh, by_contra fun hd => hn ?_⟩
      exact (hclosed P hP e (mem_sdiff.mpr ⟨hr, hd⟩) (hsurv hP hh)).mpr hh
  have hdist : (blocks : Set (Finset V)).PairwiseDisjoint (boundary tail head R) := by
    intro P hP Q hQ hne
    have hpq := disjoint_left.mp (hdisj hP hQ hne)
    apply disjoint_left.mpr
    intro e he he'
    rcases hcross hP he with ⟨ht, hd⟩ | ⟨hh, hd⟩ <;>
      rcases hcross hQ he' with ⟨ht', hd'⟩ | ⟨hh', hd'⟩
    · exact hpq ht ht'
    · exact (mem_sdiff.mp (hsurv hQ hh')).2 hd
    · exact (mem_sdiff.mp (hsurv hQ ht')).2 hd
    · exact hpq hh hh'
  have hsub : blocks.biUnion (boundary tail head R) ⊆ D.biUnion (incidentEdges tail head) := by
    intro e he
    obtain ⟨P, hP, he'⟩ := mem_biUnion.mp he
    rcases hcross hP he' with ⟨_, hd⟩ | ⟨_, hd⟩
    · exact mem_biUnion.mpr ⟨head e, hd, by simp [incidentEdges]⟩
    · exact mem_biUnion.mpr ⟨tail e, hd, by simp [incidentEdges]⟩
  rw [← card_biUnion hdist, Nat.mul_comm]
  exact (card_le_card hsub).trans (card_biUnion_le_card_mul _ _ _ hdeg)

/-- If the deletion charge fits the boundary budget of the surviving vertices,
one of the nonempty connected blocks is a candidate. -/
theorem exists_candidate_of_deletions (tail head : E → V) (R D : Finset V)
    (blocks : Finset (Finset V)) (K : ℕ) (ε : ℝ) (hsurv : (R \ D).Nonempty)
    (hcover : blocks.biUnion id = R \ D)
    (hdisj : (blocks : Set (Finset V)).PairwiseDisjoint id)
    (hclosed : ∀ P ∈ blocks, EdgeClosed tail head (R \ D) P)
    (hblock : ∀ P ∈ blocks, P.Nonempty ∧ Connected tail head P ∧ P.card ≤ K)
    (hdeg : ∀ v ∈ D, (incidentEdges tail head v).card ≤ 4)
    (hbudget : 4 * (D.card : ℝ) ≤ ε * (R \ D).card) :
    ∃ P ∈ blocks, Candidate tail head K ε R P := by
  classical
  have hbound := sum_boundary_le_deleted tail head R D blocks 4 hcover hdisj hclosed hdeg
  have hsum : ∑ P ∈ blocks, P.card = (R \ D).card := by
    simpa only [id_eq, ← hcover] using (card_biUnion hdisj).symm
  have hb : blocks.Nonempty := by
    obtain ⟨v, hv⟩ := hsurv
    rw [← hcover] at hv
    obtain ⟨P, hP, _⟩ := mem_biUnion.mp hv
    exact ⟨P, hP⟩
  by_contra! hbad
  have hlarge (P : Finset V) (hP : P ∈ blocks) : ε * P.card < (boundary tail head R P).card := by
    have hsub : P ⊆ R \ D := by
      rw [← hcover]
      exact fun _ hv => mem_biUnion.mpr ⟨P, hP, hv⟩
    obtain ⟨hne, hconn, hsize⟩ := hblock P hP
    exact lt_of_not_ge fun h => hbad P hP ⟨hne, hsub.trans sdiff_subset, hconn, hsize, h⟩
  have ht := sum_lt_sum_of_nonempty hb hlarge
  rw [← mul_sum, ← Nat.cast_sum, hsum, ← Nat.cast_sum] at ht
  have hn : ((∑ P ∈ blocks, (boundary tail head R P).card : ℕ) : ℝ) ≤ 4 * D.card := by
    exact_mod_cast hbound
  exact (not_lt_of_ge (hn.trans hbudget)) ht

/-- The deletion fraction `ε / (4 + ε)` leaves at least one vertex and pays
for every component boundary at degree four. -/
theorem budget_of_deletion_fraction {R D : Finset V} {ε : ℝ}
    (hR : R.Nonempty) (hD : D ⊆ R) (hε : 0 ≤ ε)
    (hsmall : (D.card : ℝ) ≤ ε / (4 + ε) * R.card) :
    (R \ D).Nonempty ∧ 4 * (D.card : ℝ) ≤ ε * (R \ D).card := by
  have hden : 0 < 4 + ε := by linarith
  rw [div_mul_eq_mul_div, le_div_iff₀ hden] at hsmall
  have hcard : ((R \ D).card : ℝ) + D.card = R.card := by
    exact_mod_cast card_sdiff_add_card_eq_card hD
  have hbudget : 4 * (D.card : ℝ) ≤ ε * (R \ D).card := by
    rw [← hcard, mul_add] at hsmall
    linarith only [hsmall]
  refine ⟨?_, hbudget⟩
  by_contra he
  have hz := card_eq_zero.mpr (not_nonempty_iff_eq_empty.mp he)
  rw [hz, Nat.cast_zero, mul_zero] at hbudget
  have hpos : 0 < (R.card : ℝ) := by exact_mod_cast card_pos.mpr hR
  rw [hz, Nat.cast_zero, zero_add] at hcard
  linarith

end PlanarPatch

end SpectralBooks
end LinearAlgebra
end OAI
