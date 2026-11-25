import OAI.Computability.BorderVNP.RoutingMessages
import Mathlib.Algebra.BigOperators.Fin

/-!
# Public offsets for the physical round-robin links

The public work in §8.3 must compute the layout from cable lengths without
iterating through all padded wires. A length and a relay's rank determine a
list length by one division. The offset of an individual bit is the sum of
those lengths for earlier partners plus its own quotient.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Routing

open Finset

variable {R : ℕ}

/-- Number of positions of the form `q * period + start` in `[0, width)`. -/
def strideCount (period start width : ℕ) : ℕ :=
  if width ≤ start then 0 else (width - 1 - start) / period + 1

private theorem lt_strideCount_iff {period start width q : ℕ} (hp : 0 < period) :
    q < strideCount period start width ↔ q * period + start < width := by
  unfold strideCount
  split
  · omega
  · rw [Nat.lt_succ_iff, Nat.le_div_iff_mul_le hp]
    omega

/-- Increasing index of the intermediate team among the permitted relays. -/
def relayRank {u w v : Fin R} (h : u ≠ w) (hv : v ∈ pool u w) : Fin (R - 2) :=
  ((pool u w).orderIsoOfFin (pool_card h)).symm ⟨v, hv⟩

private theorem relay_eq_iff_rank (hR : 2 < R) {u w v : Fin R} (h : u ≠ w)
    (hv : v ∈ pool u w) (j : ℕ) :
    relay hR h j = v ↔ j % (R - 2) = (relayRank h hv).val := by
  let f := (pool u w).orderIsoOfFin (pool_card h)
  let i : Fin (R - 2) := ⟨j % (R-2), Nat.mod_lt _ (by omega)⟩
  change (f i).val = v ↔ i.val = (f.symm ⟨v,hv⟩).val
  rw [← Fin.ext_iff, OrderIso.eq_symm_apply, Subtype.ext_iff]

/-- Public count of positions, computed from the width, independent of how many
actual bits the list contains. -/
def scheduledLength (u w v : Fin R) (width : ℕ) : ℕ :=
  if h : u ≠ w then
    if hv : v ∈ pool u w then strideCount (R - 2) (relayRank h hv).val width else 0
  else 0

/-- Length of a pair's list and the exact rank of each bit on its assigned
physical leg, both obtained by quotient arithmetic. -/
def ordinalEquiv (hR : 2 < R) (u w v : Fin R) (width : ℕ) :
    ↥(pairBits hR u w v width) ≃ Fin (scheduledLength u w v width) := by
  by_cases h : u ≠ w
  · by_cases hv : v ∈ pool u w
    · let t := relayRank h hv
      have hp : 0 < R - 2 := by omega
      have mem (j : ℕ) : j ∈ pairBits hR u w v width ↔ j < width ∧ j % (R-2) = t.val := by
        rw [pairBits, dite_eq_left h, mem_filter, mem_range, relay_eq_iff_rank hR h hv]
      have len : scheduledLength u w v width = strideCount (R-2) t.val width := by
        rw [scheduledLength, dite_eq_left h, dite_eq_left hv]
      refine ⟨fun j ↦ ⟨j.val / (R-2), ?_⟩, fun q ↦ ⟨q.val * (R-2) + t.val, ?_⟩, ?_, ?_⟩
      · obtain ⟨hw, ht⟩ := (mem j.val).1 j.2
        rw [len, lt_strideCount_iff hp, ← ht, Nat.div_add_mod']
        exact hw
      · apply (mem _).2
        refine ⟨(lt_strideCount_iff hp).1 (len ▸ q.isLt), ?_⟩
        simp [Nat.mod_eq_of_lt t.isLt]
      · intro j
        apply Subtype.ext
        change j.val / (R-2) * (R-2) + t.val = j.val
        rw [← ((mem j.val).1 j.2).2, Nat.div_add_mod']
      · intro q
        apply Fin.ext
        change (q.val * (R-2) + t.val) / (R-2) = q.val
        rw [Nat.mul_comm q.val, Nat.mul_add_div hp, Nat.div_eq_of_lt t.isLt, Nat.add_zero]
    · have hempty : pairBits hR u w v width = ∅ := by
        rw [pairBits, dite_eq_left h, filter_eq_empty_iff]
        intro j _ he
        exact hv (he ▸ (pool u w).orderEmbOfFin_mem _ _)
      rw [hempty, scheduledLength, dite_eq_left h, dite_eq_right hv]
      exact Equiv.equivOfIsEmpty _ _
  · rw [pairBits, dite_eq_right h, scheduledLength, dite_eq_right h]
    exact Equiv.equivOfIsEmpty _ _

/-- The scheduled ordinal of a transmitted bit is its quotient by the relay period. -/
theorem ordinalEquiv_val (hR : 2 < R) (u w v : Fin R) (width : ℕ)
    (j : ↥(pairBits hR u w v width)) :
    (ordinalEquiv hR u w v width j).val = j.val / (R - 2) := by
  by_cases h : u ≠ w
  · have he : j.val ∈ pairBits hR u w v width := j.property
    have result (j' : ℕ) (mem : j' ∈ pairBits hR u w v width) : v ∈ pool u w := by
      rw [pairBits, dite_eq_left h] at mem
      exact (mem_filter.mp mem).2 ▸ (pool u w).orderEmbOfFin_mem _ _
    have hm := result j.val he
    simp [ordinalEquiv, h, hm]
  · have he : j.val ∈ pairBits hR u w v width := j.property
    simp [pairBits, h] at he

/-- The width-only public count equals the cardinality of the actual routed bits. -/
theorem scheduledLength_eq (hR : 2 < R) (u w v : Fin R) (width : ℕ) :
    scheduledLength u w v width = pairLoad hR u w v width := by
  simpa [pairLoad] using (Fintype.card_congr (ordinalEquiv hR u w v width)).symm

/-- A whole physical leg is indexed by partner prefix sums. The table of list
lengths has just one entry per team. -/
def legEquiv (hR : 2 < R) (width : Fin R → Fin R → ℕ) (u v : Fin R) :
    Hop hR width u v ≃ Fin (legLoad hR width u v) :=
  ((Equiv.sigmaCongrRight fun w ↦ ordinalEquiv hR u w v (demand width u w)).trans
    finSigmaFinEquiv).trans (finCongr (Finset.sum_congr rfl fun w _ ↦ scheduledLength_eq hR u w v _))

/-- The team's address calculation scans partner lengths, then adds the bit's
local ordinal. It can compute these lengths without visiting any individual wires. -/
theorem legEquiv_address (hR : 2 < R) (width : Fin R → Fin R → ℕ) (u v : Fin R)
    (p : Hop hR width u v) :
    (legEquiv hR width u v p).val =
      (∑ i : Fin p.1.val,
        let w := Fin.castLE p.1.isLt.le i
        scheduledLength u w v (demand width u w)) +
      p.2.val / (R - 2) := by
  rw [← ordinalEquiv_val hR u p.1 v (demand width u p.1) p.2]
  exact finSigmaFinEquiv_apply (n := fun w ↦ scheduledLength u w v (demand width u w))
    ⟨p.1, ordinalEquiv hR u p.1 v _ p.2⟩

end Routing

end BorderVNP
end Computability
end OAI
