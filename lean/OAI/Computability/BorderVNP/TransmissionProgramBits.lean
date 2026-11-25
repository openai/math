import OAI.Computability.BorderVNP.TransmissionInverseRow

/-! # A physical transmission run with its exact chronological choices -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Transmission

open VPVNP.BurstRAM

variable {w : ℕ}

/-- The transmission program realizes each allowed row assignment. Its only binary
choices are the local shared-wire bits, in row and slot order. The cost charges payload
work to the executing team. -/
theorem table_runs_bits (rows : ℕ → Range w) (pub : Arg → Word w) (macros : TeamOpcode.Macros w 8)
    (m : Memory w) (s : Bank w) (bits : ℕ → ℕ → Bool)
    (table : ∀ i < (directoryFrame pub m 13).val,
      rangeAt (tableMemory rows (directoryFrame pub m 0) pub m bits i)
        (cursorAt (directoryFrame pub m 12) 7 i) (cursorAt (directoryFrame pub m 20) 1 i) = rows i)
    (allowed : ∀ i < (directoryFrame pub m 13).val,
      (rows i).allowed (directoryFrame pub m 0) pub
        (tableMemory rows (directoryFrame pub m 0) pub m bits i) (bits i)) :
    ∃ es t, Runs pub macros transmitRanges s m es t
        (tableMemory rows (directoryFrame pub m 0) pub m bits (directoryFrame pub m 13).val) ∧
      es.flatMap TeamRAM.Event.choices =
        tableChoiceBits rows (directoryFrame pub m 0) bits (directoryFrame pub m 13).val ∧
      traceCost es ≤ setup.slots + (20 + decision.depth) * (directoryFrame pub m 13).val +
        (∑ i ∈ Finset.range (directoryFrame pub m 13).val, (rows i).teamCost (directoryFrame pub m 0)) + 1 := by
  let team := directoryFrame pub m 0
  let base := directoryFrame pub m 12
  let count := directoryFrame pub m 13
  let ord := directoryFrame pub m 20
  let M := tableMemory rows team pub m bits
  let B := tableChoiceBits rows team bits
  let cost (i : ℕ) := 20 + decision.depth + (rows i).teamCost team
  have loop (k i : ℕ) (remains : i+k=count.val) (u : Bank w) (hu : AtRow team base count ord i u) :
      ∃ es t, Runs pub macros (.whileLt 5 4 step) u (M i) es t (M count.val) ∧
        B i ++ es.flatMap TeamRAM.Event.choices = B count.val ∧
        traceCost es ≤ (∑ j ∈ Finset.Ico i count.val, cost j) + 1 := by
    induction k generalizing i u with
    | zero =>
      have h : i = count.val := by omega
      subst i
      have guard : ¬u 5 < u 4 := by
        change ¬(u 5).val < (u 4).val
        simp only [hu.index, hu.bound, lt_self_iff_false, not_false_eq_true]
      exact ⟨_,u,Runs.whileDone guard,by simp [tick],by simp; exact le_rfl⟩
    | succ k ih =>
      have hi : i < count.val := by omega
      have guard : u 5 < u 4 := by
        change (u 5).val < (u 4).val
        simpa only [hu.index, hu.bound] using hi
      obtain ⟨es,t,r,hb,ht,hc⟩ := directory_step_bits (macros := macros) hu hi
        (table i hi) (bits i) (allowed i hi)
      obtain ⟨fs,v,rr,hb',hc'⟩ := ih (i+1) (by omega) t ht
      refine ⟨_,v,Runs.whileStep guard r rr,?_,?_⟩
      · simp only [tick,List.flatMap_cons,List.nil_append,List.flatMap_append,hb]
        simpa only [B,tableChoiceBits,List.append_assoc] using hb'
      · change 1 + traceCost (es ++ fs) ≤ _
        rw [cost_append, Finset.sum_eq_sum_Ico_succ_bot hi]
        dsimp only [cost] at *
        omega
  obtain ⟨es,u,setupRun,hs,hteam,h1,h0,h5,hbase,hcount,hord⟩ := setup_runs pub macros s m
  have start : AtRow team base count ord 0 u :=
    ⟨hteam,h1,h0,by simpa [cursorAt,base] using hbase,hcount,by simp [h5],by simpa [cursorAt,ord] using hord⟩
  obtain ⟨fs,t,r,hb,hc⟩ := loop count.val 0 (Nat.zero_add _) u start
  refine ⟨_,t,setupRun.seq r,?_,?_⟩
  · rw [List.flatMap_append, Pins.noChoices setupRun (by decide), List.nil_append]
    exact hb
  · rw [cost_append]
    rw [Nat.Ico_zero_eq_range] at hc
    simp only [cost, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_id] at hc
    exact (Nat.add_le_add hs hc).trans_eq (by dsimp [team,count]; ring)

end RoutingISA.Transmission

end BorderVNP
end Computability
end OAI
