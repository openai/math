import OAI.Computability.VPVNP.IncidenceControl

/-!
# Reading a column of the exact-one incidence matrix

On a pass for row `r`, the column parser increases its capped tally precisely when
the column is selected and its incidence bit for row `r` is set. The scan consumes
one tick per encoded bit and leaves the head at the following tag.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace IncidenceMachine

open UniversalMachine TableCompiler QueryTape

/-- The count after reading the first `j` row bits of one column. -/
private def partialCount {m : ℕ} (c : Column m) (r : Fin m) (n j : ℕ) : ℕ :=
  if r.val < j then n + (c.1 && c.2 r).toNat else n

private theorem readBit {m : ℕ} (c : Column m) (r j : Fin m) (n : ℕ) :
    (if j = r ∧ c.1 = true ∧ (if c.2 j then (2 : Symbol) else 1) = 2 then
      tally ((tally (partialCount c r n j.val)).val + 1)
    else tally (partialCount c r n j.val)) = tally (partialCount c r n (j.val + 1)) := by
  by_cases hj : j = r
  · subst j
    cases hs : c.1 <;> cases hb : c.2 r <;> simp [partialCount, hs, hb, tally_succ]
  · have hne : j.val ≠ r.val := fun h => hj (Fin.ext h)
    have hlt : r.val < j.val + 1 ↔ r.val < j.val := by omega
    simp [partialCount, hj, hlt]

private theorem bitHead {m : ℕ} (input : Word) (base : ℕ) (c : Column m)
    (h : ReadsLeft input base (columnBits c)) (j : Fin m) :
    (atPosition input (base + (m - j.val))).head = if c.2 j then 2 else 1 := by
  have hi : j.val + 2 < (columnBits c).length := by simp [columnBits]
  have hj := h (j.val + 2) hi
  simp [columnBits] at hj
  simpa [show base + (m + 1 + 1) - (j.val + 2) = base + (m - j.val) by omega] using hj

/-- Starting at row bit `j`, read the rest of the column and return to the tag state. -/
private theorem scanColumnBits {m : ℕ} (input : Word) (base : ℕ) (c : Column m)
    (r j : Fin m) (n fuel : ℕ) (h : ReadsLeft input base (columnBits c)) :
    countAt m input (base + (m - j.val))
        (.bit r j c.1 (tally (partialCount c r n j.val))) ((m - j.val) + fuel) =
      countAt m input base (.tag r (tally (n + (c.1 && c.2 r).toNat))) fuel := by
  let rem := m - (j.val + 1)
  have hpos : base + (m - j.val) = (base + rem) + 1 := by dsimp [rem]; omega
  have htime : (m - j.val) + fuel = (rem + fuel) + 1 := by dsimp [rem]; omega
  have hs := bitHead input base c h j
  rw [hpos] at hs
  rw [hpos, htime]
  by_cases hj : j.val + 1 < m
  · let next : Fin m := ⟨j.val + 1, hj⟩
    refine (countAt_left (next := .bit r next c.1 (tally (partialCount c r n next.val))) ?_).trans
      (scanColumnBits input base c r next n fuel h)
    rw [hs]
    simp only [command, hj, dite_true, readBit, next]
  · have hm : j.val + 1 = m := by omega
    have hz : rem = 0 := by simp [rem, hm]
    simp only [hz, Nat.add_zero, Nat.zero_add] at hs ⊢
    apply countAt_left
    rw [hs]
    simp only [command, hj, dite_false, readBit]
    simp [hm, partialCount]
termination_by m - j.val
decreasing_by omega

/-- Reading a column adds its selected incidence bit to the capped row count. -/
theorem runColumn {m : ℕ} (input : Word) (base : ℕ) (c : Column m) (r : Fin m)
    (n fuel : ℕ) (h : ReadsLeft input base (columnBits c)) :
    countAt m input (base + (columnBits c).length) (.tag r (tally n))
        ((columnBits c).length + fuel) =
      countAt m input base (.tag r (tally (n + (c.1 && c.2 r).toNat))) fuel := by
  have hlen : (columnBits c).length = m + 1 + 1 := by simp [columnBits]
  have htag := h 0 (by rw [hlen]; omega)
  have hflag := h 1 (by rw [hlen]; omega)
  have ht : (atPosition input (base + m + 1 + 1)).head = 2 := by
    simpa [columnBits, Nat.add_assoc] using htag
  have hf : (atPosition input (base + m + 1)).head = if c.1 then 2 else 1 := by
    cases hc : c.1 <;> simpa [columnBits, Nat.add_assoc, hc] using hflag
  let first : Fin m := ⟨0, Nat.zero_lt_of_lt r.isLt⟩
  rw [hlen, show base + (m + 1 + 1) = base + m + 1 + 1 by omega,
    show m + 1 + 1 + fuel = ((m + fuel) + 1) + 1 by omega]
  refine (countAt_left (next := .flag r (tally n)) ?_).trans ?_
  · simp [command, ht]
  refine (countAt_left (next := .bit r first c.1 (tally n)) ?_).trans ?_
  · rw [hf]
    cases hc : c.1 <;> simp [command, first]
  simpa [first, partialCount] using scanColumnBits input base c r first n fuel h

end IncidenceMachine

end VPVNP
end Computability
end OAI
