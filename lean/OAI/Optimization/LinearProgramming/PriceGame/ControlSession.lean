import OAI.Optimization.LinearProgramming.PriceGame.ControlEncodingPad
import OAI.Optimization.LinearProgramming.PriceGame.ControlExchanges
import OAI.Optimization.LinearProgramming.PriceGame.StatesCommunication
import OAI.Optimization.LinearProgramming.OracleSpec.DialogueProof

/-! Transfer actual exchanges of the first-order price dispatcher to the bounded
dialogue of the frozen bit machine, including its final dispatch and its actual wire prices. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Control

open OracleSpec

def packetBudget (N width : ℕ) : ℕ := 2*N+1 + N*(2*width+1)

theorem signed_word_length (q : ℚ) : (encodeRat q).length ≤ 2*RAM.ratBits q+1 := by
  simp only [encodeRat,List.length_cons,List.length_append,encodeNat_length,RAM.ratBits]
  have hn : q.num.natAbs.size ≤ q.num.natAbs.log2+1 := Nat.size_le.mpr Nat.lt_log2_self
  have hd : q.den.size ≤ q.den.log2+1 := Nat.size_le.mpr Nat.lt_log2_self
  omega

theorem price_word_length {N W : ℕ} (q : Query N) (hw : PricesBounded W q) :
    (priceQuery q.index q.prices).length ≤ packetBudget N W := by
  have aux (xs : List ℚ) (h : ∀ x ∈ xs, RAM.ratBits x ≤ W) :
      (xs.flatMap encodeRat).length ≤ xs.length*(2*W+1) := by
    induction xs with
    | nil => simp
    | cons x xs ih =>
      have h₁ := signed_word_length x
      have h₂ := h x (by simp)
      have h₃ := ih (fun z hz => h z (by simp [hz]))
      rw [List.flatMap_cons,List.length_append,List.length_cons,Nat.add_mul xs.length 1 (2*W+1),Nat.one_mul]
      omega
  have ha := aux (List.ofFn q.prices) (by
    intro x hx
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hx
    exact hw _)
  rw [List.length_ofFn] at ha
  have hi : q.index.val.size ≤ N := (Nat.size_le.mpr q.index.val.lt_two_pow_self).trans q.index.isLt.le
  simp only [priceQuery,List.length_append,encodeNat_length,packetBudget]
  omega

private theorem allQueries_of_observation {N : ℕ} {α : Type*} {P : Query N → Prop}
    (p : Computation N α) (bs : List Bool) {q : Query N} (all : p.AllQueries P)
    (observed : observe p bs = .inr q) : P q := by
  induction p generalizing bs with
  | pure => contradiction
  | ask q' next ih =>
    cases bs with
    | nil => cases observed; exact all.1
    | cons b bs => exact ih b bs (all.2 b) observed

private def carryWith (header : PublicInput → Word) (t : Tape) : Word :=
  frame t.reverseReplies ++ header t.input

/-- The same exchange count and transcript satisfy the machine's full dialogue relation,
provided the real source word and all its actual query packets fit the stated limit. -/
theorem Exchanges.toSession {solver : PublicSolver} {reply : Transcript → Word → Bool}
    {event past value seen rounds} (run : Exchanges solver reply event past value seen rounds)
    (header : PublicInput → Word) (i : PublicInput) (L : ℕ)
    (headroom : 2*(solver i).height + (header i).length + 1 ≤ L)
    (packets : (solver i).AllQueries (fun q => (priceQuery q.index q.prices).length ≤ L))
    (input : (startTape event).input = i)
    (initial : (Dialogue.inputCode header (carryWith header) event).length ≤ L) :
    Dialogue.Session header (carryWith header) (dispatch solver) reply L event past value seen rounds := by
  induction run with
  | done stopped => exact .done stopped initial
  | @query s old w t answer out n pending rest ih =>
    obtain ⟨ht,q,obs,rfl⟩ := (dispatch_query_iff solver s w t).mp pending
    have hi : t.input = i := (congrArg Tape.input ht).trans input
    have all : (solver t.input).AllQueries (fun u => (priceQuery u.index u.prices).length ≤ L) := by
      exact (congrArg (fun j : PublicInput => (solver j).AllQueries (fun u => (priceQuery u.index u.prices).length ≤ L)) hi).mpr packets
    refine .query pending initial (allQueries_of_observation _ _ all obs) (ih hi ?_)
    obtain ⟨_,_,hh⟩ := pending_of_observe (solver t.input) t.reverseReplies.reverse obs
    rw [List.length_reverse] at hh
    have hm : 2 * (solver t.input).height + (header t.input).length + 1 ≤ L := (congrArg (fun j : PublicInput => 2*(solver j).height + (header j).length + 1 ≤ L) hi).mpr headroom
    simp only [Dialogue.inputCode,carryWith,List.length_cons,List.length_append,frame_length]
    omega

/-- The external protocol on a padded input, measured in the exact number of rounds of
the actual price campaign. Free or inconsistent replies satisfy the same bounds. -/
theorem campaign_session (trials : ℕ → ℕ → ℕ) (i : PublicInput)
    (reply : Transcript → Word → Bool) (width : ℕ)
    (all : (campaignSolver trials i).AllQueries (PricesBounded width)) :
    let H := trials i.goods i.range * TrialExecution.queryBound i.goods Moment.probes (States.Mass.depth i.goods) 0
    let L := max (2*H + (eiPad i).length + 1) (packetBudget i.goods width)
    ∃ n ≤ H+1, Dialogue.Session eiPad ecPad (dispatch (campaignSolver trials)) reply L (.inl i) []
      (wirePlay reply (campaignSolver trials i) []).1 (wirePlay reply (campaignSolver trials i) []).2 n := by
  dsimp only
  obtain ⟨n,hn,hr⟩ := actual_campaign_dispatch trials i reply
  refine ⟨n,hn,hr.toSession eiPad i _ ?_ ?_ rfl ?_⟩
  · exact (Nat.add_le_add_right (Nat.add_le_add_right (Nat.mul_le_mul_left 2 (campaignSolver_height trials i)) _) _).trans
      (Nat.le_max_left _ _)
  · apply Computation.allQueries_mono _ _ _ _ all
    exact fun q h => (price_word_length q h).trans (Nat.le_max_right _ _)
  · simp only [Dialogue.inputCode,List.length_cons]
    exact (by omega : (eiPad i).length + 1 ≤
      2*(trials i.goods i.range * TrialExecution.queryBound i.goods Moment.probes (States.Mass.depth i.goods) 0) +
        (eiPad i).length + 1).trans (Nat.le_max_left _ _)

end Control
end PriceGame
end LinearProgramming
end Optimization
end OAI
