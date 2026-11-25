import OAI.Hierarchy.DescentResetSlotIndex
import OAI.Hierarchy.DescentCapacityCalendar

namespace OAI
/-! The public capacity digit and host degree at each position in one reset period. -/
namespace Hierarchy.DescentSixParty.Chronology
open DescentCompiler DescentHostDegree

private theorem factor_length (radix length start : ℕ) :
    (ordinaryCapFactors radix start length).length = length := by
  induction length generalizing start with
  | zero => rfl
  | succ n ih => simp [ordinaryCapFactors, ih]

private theorem factor_at (radix length start i : ℕ) (inside : i < length) :
    (ordinaryCapFactors radix start length)[i]? =
      some (2^(gainExponent 20 (atRound (start+i))) * radix) := by
  induction length generalizing start i with
  | zero => omega
  | succ n ih =>
    cases i with
    | zero => simp [ordinaryCapFactors]
    | succ i =>
      simpa only [ordinaryCapFactors, List.getElem?_cons_succ, Nat.succ_add, Nat.add_succ] using
        ih (start+1) i (by omega)

theorem ordinary_slot_factor (radix rounds gain epochs i : ℕ)
    (hit : ((kindCalendar rounds epochs).drop i).head? = some false) :
    i % (rounds+1) < rounds ∧
    ((capCalendar radix rounds gain epochs).drop i).head? =
      some (2^(gainExponent 20 (atRound (i % (rounds+1)))) * radix) := by
  rw [List.head?_drop] at hit ⊢
  induction epochs generalizing i with
  | zero => simp [kindCalendar] at hit
  | succ n ih =>
    rw [kindCalendar, List.replicate_succ, List.flatten_cons] at hit
    rw [capCalendar]
    have nk : (kindPeriod rounds).length = rounds+1 := by simp [kindPeriod]
    have nf : (capPeriod radix rounds gain).length = rounds+1 := by
      simp [capPeriod, factor_length]
    by_cases first : i < rounds+1
    · rw [List.getElem?_append_left (by simpa only [nk] using first)] at hit
      have real : i < rounds := by
        by_contra later
        have same : i = rounds := by omega
        subst i
        rw [kindPeriod, List.getElem?_append_right (by simp), List.length_replicate, Nat.sub_self] at hit
        cases hit
      rw [Nat.mod_eq_of_lt first]
      refine ⟨real, ?_⟩
      rw [List.getElem?_append_left (by simpa only [nf] using first), capPeriod,
        List.getElem?_append_left (by simpa only [factor_length] using real)]
      simpa only [Nat.zero_add] using factor_at radix rounds 0 i real
    · have past : rounds+1 ≤ i := Nat.le_of_not_gt first
      rw [List.getElem?_append_right (by simpa only [nk] using past), nk] at hit
      rw [List.getElem?_append_right (by simpa only [nf] using past), nf]
      have reduced : (i-(rounds+1)) % (rounds+1) = i % (rounds+1) := by
        calc
          _ = ((i-(rounds+1))+(rounds+1)) % (rounds+1) := by simp
          _ = _ := by rw [Nat.sub_add_cancel past]
      simpa only [reduced] using ih (i-(rounds+1)) hit

theorem ordinary_slot_degree (radix rounds gain epochs i : ℕ) (positive : 0 < radix)
    (hit : ((kindCalendar rounds epochs).drop i).head? = some false) :
    OrdinaryLink.publicDegree rounds radix (((capCalendar radix rounds gain epochs).drop i).head?.getD 0) =
      atRound (i % (rounds+1)) ∧ (i+1) % (rounds+1) = i % (rounds+1)+1 := by
  obtain ⟨inside, slot⟩ := ordinary_slot_factor radix rounds gain epochs i hit
  have classAt (j : ℕ) : degreeClass radix (2^(gainExponent 20 (atRound j)) * radix) =
      logDegree (atRound j) := by
    unfold degreeClass
    rw [Nat.mul_div_cancel _ positive, Nat.log2_two_pow]
    unfold gainExponent packExponent
    omega
  constructor
  · rw [slot, Option.getD_some, OrdinaryLink.publicDegree, classAt, OrdinaryLink.roundFor_exact inside]; rfl
  · rw [← Nat.mod_add_mod i (rounds+1) 1, Nat.mod_eq_of_lt (by omega : i % (rounds+1)+1 < rounds+1)]

theorem reset_slot_successor (rounds epochs i : ℕ)
    (hit : ((kindCalendar rounds epochs).drop i).head? = some true) :
    (i+1) % (rounds+1) = 0 := by
  rw [← Nat.mod_add_mod i (rounds+1) 1, reset_slot_index rounds epochs i hit, Nat.mod_self]

end Hierarchy.DescentSixParty.Chronology

end OAI
