import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Nat.Find

/-! # Intervals of ordered slots

Ordering a finite collection by distinct natural-number slots, and assigning a
length to each slot, partitions the positions strictly below the total length.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

namespace PlanarPatch

/-- Each position in the concatenation lies in the interval of a slot. -/
theorem exists_slot_interval {V : Type*} (s : Finset V) (slot size : V → ℕ)
    (hinj : Set.InjOn slot ↑s) {k : ℕ} (hk : k < ∑ w ∈ s, size w) :
    ∃ w ∈ s, (∑ u ∈ s.filter (fun u => slot u < slot w), size u) ≤ k ∧
      k < (∑ u ∈ s.filter (fun u => slot u < slot w), size u) + size w := by
  classical
  let before (n : ℕ) := ∑ u ∈ s.filter (fun u => slot u < n), size u
  have hbound : ∃ n, k < before n := by
    refine ⟨s.sup slot + 1, ?_⟩
    simpa [before, Finset.filter_true_of_mem (fun u hu => Nat.lt_succ_of_le
      (Finset.le_sup (f := slot) hu))] using hk
  have hlast := Nat.find_spec hbound
  cases hcut : Nat.find hbound with
  | zero =>
    simp [hcut, before] at hlast
  | succ i =>
    rw [hcut] at hlast
    have hfirst : before i ≤ k := Nat.le_of_not_lt
      (Nat.find_min hbound (show i < Nat.find hbound by omega))
    have hex : ∃ w ∈ s, slot w = i := by
      by_contra! hn
      have hsame : s.filter (fun u => slot u < i + 1) = s.filter (fun u => slot u < i) := by
        ext u
        simp only [Finset.mem_filter]
        exact and_congr_right fun hu => by
          have := hn u hu
          omega
      exact (Nat.not_lt_of_ge hfirst) (by simpa [before, hsame] using hlast)
    obtain ⟨w, hw, hslot⟩ := hex
    refine ⟨w, hw, hslot ▸ hfirst, ?_⟩
    have hsplit : s.filter (fun u => slot u < i + 1) =
        insert w (s.filter (fun u => slot u < i)) := by
      ext u
      simp only [Finset.mem_filter, Finset.mem_insert]
      constructor
      · rintro ⟨hu, hle⟩
        by_cases heq : slot u = i
        · exact Or.inl (hinj hu hw (heq.trans hslot.symm))
        · exact Or.inr ⟨hu, by omega⟩
      · rintro (rfl | ⟨hu, hlt⟩)
        · exact ⟨hw, by omega⟩
        · exact ⟨hu, by omega⟩
    simpa [before, hsplit, Finset.sum_insert, hslot, Nat.add_comm] using hlast

end PlanarPatch

end SpectralBooks
end LinearAlgebra
end OAI
