import OAI.Computability.BorderVNP.CubeHostScatterProgram
import OAI.Computability.BorderVNP.CubeSharedRowsPhysical

/-! # The native host bit clock is controlled by the physical team's raw group load

Every real copied endpoint belongs to its team's coordinate group. The two
endpoints of a cable can belong to the same group, which accounts for the
factor two when passing from endpoint incidences to the manuscript's raw load.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.HostScatter

open Physical Finset

private def twoEnds {n d : ℕ} (i : Fin (n+1)) (u : Fin d) (p : Label (n+1) d × Label (n+1) d) : ℕ :=
  (if p.1 i = u then 1 else 0) + (if p.2 i = u then 1 else 0)

private theorem sum_by_bin {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    (bin : α → β) (w : α → ℕ) (cost : β → ℕ) :
    (∑ a, w a*cost (bin a)) = ∑ p, (∑ a, if bin a = p then w a else 0)*cost p := by
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  simp [ite_mul]

private theorem ends_le_raw {n d r : ℕ} (i : Fin (n+1)) (u : Fin d)
    (bin : Fin r → Label (n+1) d × Label (n+1) d) (w : Fin r → ℕ) (S : ℕ)
    (cap : ∀ p, Physical.load bin w p ≤ S) :
    (∑ e, w e*twoEnds i u (bin e)) ≤ 2*groupRaw S i u := by
  rw [sum_by_bin,Fintype.sum_prod_type]
  simp only [groupRaw,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro s _
  apply Finset.sum_le_sum
  intro t _
  have h : (∑ e, if bin e = (s,t) then w e else 0) ≤ S := cap (s,t)
  by_cases hs : s i = u <;> by_cases ht : t i = u <;>
    simp [twoEnds,hs,ht] <;> omega

/-- Width of a row that actually crosses cells; padding and already absorbed rows
can be retained in the public numbering without consuming any group capacity. -/
def Layout.liveWidth (l : Layout) (before : ℕ → ℕ) (j : Fin l.count) :=
  if l.cell before j false = l.cell before j true then 0 else l.width before j

/-- Compute the native endpoint count from the physical group owners and padded capacity.
The owner agreement is required only on live crossing cables with positive width. -/
theorem Layout.incident_le_raw {n d S : ℕ} (l : Layout) (before : ℕ → ℕ) (i : Fin (n+1))
    (pair : Fin l.count → Label (n+1) d × Label (n+1) d) (owner : Fin d → ℕ)
    (cap : ∀ p, Physical.load pair (l.liveWidth before) p ≤ S)
    (owners : ∀ j : Fin l.count, l.width before j ≠ 0 → l.cell before j false ≠ l.cell before j true →
      l.owner before j false = owner ((pair j).1 i) ∧ l.owner before j true = owner ((pair j).2 i)) :
    l.incident before ≤ 2 * ∑ u : Fin d, if owner u = l.team then groupRaw S i u else 0 := by
  have bit (j : Fin l.count) (s : Bool) :
      l.bits before j s = if owner ((if s then (pair j).2 else (pair j).1) i) = l.team then
          l.liveWidth before j else 0 := by
    by_cases zero : l.width before j = 0
    · simp [Layout.bits,Layout.Owned,Layout.liveWidth,zero]
    by_cases same : l.cell before j false = l.cell before j true
    · simp [Layout.bits,Layout.Owned,Layout.liveWidth,same]
    · obtain ⟨hs,ht⟩ := owners j zero same
      cases s <;> simp [Layout.bits,Layout.Owned,Layout.liveWidth,zero,same,hs,ht]
  have per (j : Fin l.count) :
      l.bits before j false+l.bits before j true =
        ∑ u : Fin d, if owner u = l.team then l.liveWidth before j*twoEnds i u (pair j) else 0 := by
    simp_rw [twoEnds,mul_add,ite_add_zero]
    rw [Finset.sum_add_distrib,bit j false,bit j true]
    have once (x : Fin d) : (∑ u : Fin d, if owner u = l.team then
        if x = u then l.liveWidth before j else 0 else 0) = if owner x = l.team then l.liveWidth before j else 0 := by
      rw [Finset.sum_eq_single x]
      · simp
      · intro u _ h
        simp [Ne.symm h]
      · simp
    simp [mul_ite,once]
  rw [Layout.incident,← Fin.sum_univ_eq_sum_range]
  calc
    _ = ∑ j : Fin l.count, ∑ u : Fin d,
        if owner u = l.team then l.liveWidth before j*twoEnds i u (pair j) else 0 := Finset.sum_congr rfl fun j _ => per j
    _ = ∑ u : Fin d, if owner u = l.team then (∑ j, l.liveWidth before j*twoEnds i u (pair j)) else 0 := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro u _
      split <;> simp_all
    _ ≤ _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro u _
      split_ifs
      · exact ends_le_raw i u pair _ S cap
      · simp

end Cube.HostScatter

end BorderVNP
end Computability
end OAI
