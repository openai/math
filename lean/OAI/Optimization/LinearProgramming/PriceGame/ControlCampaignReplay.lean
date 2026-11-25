import OAI.Optimization.LinearProgramming.PriceGame.ControlCampaignNative

/-! # Dispatching from an ordinary reply tape using only the concrete program counter -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Control
namespace Driver

/-- Starting or resuming a campaign consumes only the supplied reply bits. A stop
reports the unused suffix; an unanswered query is returned exactly when the tape ends. -/
def replay : ℕ → PC → List Bool → Option ((Bool × List Bool) ⊕ PackedQuery)
  | 0, _, _ => none
  | n+1, s, bits => match step s with
    | .halt b => some (.inl (b,bits))
    | .proceed next => replay n next bits
    | .ask q f t => match bits with
      | [] => some (.inr q)
      | b :: bs => replay n (if b then t else f) bs

theorem replay_some_mono {n m : ℕ} {p bits event} (found : replay n p bits = some event)
    (budget : n ≤ m) : replay m p bits = some event := by
  induction n generalizing m p bits with
  | zero => cases found
  | succ n ih =>
    cases m with
    | zero => omega
    | succ m =>
      cases hs : step p with
      | proceed next =>
        simp only [replay,hs] at found ⊢
        exact ih found (by omega)
      | ask q f t =>
        cases bits with
        | nil => simpa only [replay,hs] using found
        | cons b bs =>
          simp only [replay,hs] at found ⊢
          exact ih found (by omega)
      | halt b => simpa only [replay,hs] using found

theorem Steps.replay_complete {p q tr ticks} (run : Steps p tr ticks q) {bit}
    (done : step q = .halt bit) (tail : List Bool) :
    replay (ticks+1) p (tr.map Prod.snd ++ tail) = some (.inl (bit,tail)) := by
  induction run with
  | refl s => simp [replay,done]
  | silent h _ ih => simpa only [replay,h] using ih done
  | answer b h _ ih => simpa only [List.map_cons,List.cons_append,replay,h] using ih done

theorem Steps.replay_short {p q tr ticks} (run : Steps p tr ticks q) (k : ℕ)
    (hk : k < tr.length) :
    replay (ticks+1) p ((tr.take k).map Prod.snd) = some (.inr tr[k].1) := by
  induction run generalizing k with
  | refl => simp at hk
  | silent h _ ih => simpa only [replay,h] using ih k hk
  | answer b h _ ih =>
    cases k with
    | zero => simp [replay,h]
    | succ k =>
      simpa only [List.take_succ_cons,List.map_cons,List.getElem_cons_succ,replay,h]
        using ih k (by simpa using hk)

theorem source_observe_short {N : ℕ} {α : Type*} {p : Computation N α} {tr a}
    (e : Trial.Emits p tr a) (k : ℕ) (hk : k < tr.length) :
    (observe p ((tr.take k).map Prod.snd)).map id packQuery = .inr tr[k].1 := by
  induction e generalizing k with
  | pure => simp at hk
  | ask b _ ih =>
    cases k with
    | zero => rfl
    | succ k => exact ih k (by simpa using hk)

/-- Any finite answer tape lies on a complete branch, including a tape with a
suffix after termination or with too few answers to finish. -/
theorem fits_source {N : ℕ} {α : Type*} (p : Computation N α) (bits : List Bool) :
    ∃ tr a, Trial.Emits p tr a ∧ ((∃ tail, bits = tr.map Prod.snd ++ tail) ∨
      ∃ k, k < tr.length ∧ bits = (tr.take k).map Prod.snd) := by
  induction p generalizing bits with
  | pure a => exact ⟨[],a,.pure a,Or.inl ⟨bits,rfl⟩⟩
  | ask q next ih =>
    cases bits with
    | nil =>
      obtain ⟨tr,a,emit,_⟩ := ih false []
      exact ⟨(packQuery q,false)::tr,a,.ask false emit,Or.inr ⟨0, by simp, rfl⟩⟩
    | cons b bs =>
      obtain ⟨tr,a,emit,⟨tail,h⟩ | ⟨k,hk,h⟩⟩ := ih b bs
      · exact ⟨(packQuery q,b)::tr,a,.ask b emit,Or.inl ⟨tail,by simp [h]⟩⟩
      · exact ⟨(packQuery q,b)::tr,a,.ask b emit,Or.inr ⟨k+1, by simpa using hk, by simp [h]⟩⟩

/-- Every supplied tape produces exactly the same next price query or final sign
as the original adaptive campaign. Runtime uses only the public dimension clock. -/
theorem replay_agrees {N R T : ℕ} (compiled : RoundCompilation N R) (a : Fin N) (bits : List Bool) :
    replay (controlClock N T) (.campaign (startCampaign N R a.val T)) bits =
      some ((observe (Computation.ofTree (Campaign.strategy R T a (commonMarkets N))) bits).map id packQuery) := by
  obtain ⟨tr,bit,emit,coverage⟩ := fits_source
    (Computation.ofTree (Campaign.strategy R T a (commonMarkets N))) bits
  obtain ⟨last,steps,done⟩ := exact_control_steps compiled a emit
  have hq : tr.length ≤ T * TrialExecution.queryBound N Moment.probes (States.Mass.depth N) 0 := by
    apply (emits_length_public emit).trans
    rw [← Computation.height_toTree, Computation.toTree_ofTree]
    exact Campaign.strategy_height ..
  have large :
      T * (Trial.nodeTicks (2*Moment.probes) (States.Mass.depth N) + 2) + tr.length + 1 ≤ controlClock N T :=
    Nat.succ_le_succ (Nat.add_le_add_left hq _)
  rcases coverage with ⟨tail,rfl⟩ | ⟨k,hk,rfl⟩
  · rw [emit.observe_tape tail]
    exact replay_some_mono (steps.replay_complete done tail) large
  · rw [source_observe_short emit k hk]
    exact replay_some_mono (steps.replay_short k hk) large

end Driver
end Control
end PriceGame
end LinearProgramming
end Optimization
end OAI
