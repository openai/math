import OAI.Optimization.LinearProgramming.PriceGame.ControlCampaignWireBounds
import OAI.Optimization.LinearProgramming.PriceGame.ControlCampaignNative
import OAI.Optimization.LinearProgramming.PriceGame.ControlWireCombined
import OAI.Optimization.LinearProgramming.PriceGame.ControlEncodingState

/-! Byte bounds for the actual outer cursor, including all retained probe histories. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Control
namespace Wire

open Learning Campaign States.Mass TrialExecution ExactQuantumFactoring.BitStackProgram

def probeWidth (N R T : ℕ) :=
  probeBound (depth N) (2*N^2) (2*campaignPriceBits N R T+4)

def priorLogWidth (N R T : ℕ) :=
  listBound (T*Pool.probeBudget N) (probeWidth N R T)

def cursorWidth (N R T : ℕ) :=
  pairBound N (pairBound R.size (pairBound N (pairBound T (pairBound T
    (pairBound (poolWidth N R T) (pairBound (priorLogWidth N R T) T))))))

private theorem probe_fits {N B : ℕ} (a : Fin N) (p : Probe N)
    (h : TrialExecution.ProbeBits B p) (hd : p.level < depth N) :
    (packedProbeCode (packProbe p)).length ≤ probeBound (depth N) (2*N^2) (2*B+4) := by
  apply packProbe_le p hd.le
  · intro j hj
    simpa [card_vertices,Nat.mul_comm] using card_vertices_le N j a.pos (hj.trans hd.le)
  · exact fun i => (rat_le_machine _).trans (by have := h.1 i; omega)
  · exact fun j hj i => (rat_le_machine _).trans (by have := h.2 j hj i; omega)

private theorem seen_mem {N : ℕ} (old : ℕ → RoundResult N) (t : ℕ) (p : Probe N)
    (hp : p ∈ seenProbes old t) : ∃ j < t, p ∈ (old j).observations := by
  induction t with
  | zero => simp [seenProbes] at hp
  | succ t ih =>
    rcases List.mem_append.mp hp with h | h
    · obtain ⟨j,hj,hm⟩ := ih h
      exact ⟨j,by omega,hm⟩
    · exact ⟨t,by omega,h⟩

private theorem seen_size {N : ℕ} (old : ℕ → RoundResult N) (t H : ℕ)
    (hs : ∀ j < t, (old j).observations.length ≤ H) : (seenProbes old t).length ≤ t*H := by
  induction t with
  | zero => simp [seenProbes]
  | succ t ih =>
    simpa only [seenProbes,List.length_append,Nat.succ_mul] using
      Nat.add_le_add (ih (fun j hj => hs j (by omega))) (hs t (by omega))

theorem sourceCursor_length {N : ℕ} (a : Fin N) (R T left positive t : ℕ)
    (old : ℕ → RoundResult N) (hlt : left ≤ T) (hp : positive ≤ T) (ht : t ≤ T)
    (sized : ∀ j < T, PublicRoundBounds (population R old j) (old j))
    (fits : ∀ j < T, RoundFits (campaignPriceBits N R T) (old j)) :
    (campaignCursorCode (Driver.sourceCursor R T left a (population R old t) positive)).length ≤
      cursorWidth N R T := by
  have hseen : (listCode packedProbeCode ((population R old t).probes.map packProbe)).length ≤
      priorLogWidth N R T := by
    rw [show (population R old t).probes = seenProbes old t from replay_probes ..]
    apply list_le
    · rw [List.length_map]
      exact (seen_size old t _ (fun j hj => (sized j (by omega)).observations)).trans
        (Nat.mul_le_mul_right _ ht)
    · intro q hq
      obtain ⟨p,hm,rfl⟩ := List.mem_map.mp hq
      obtain ⟨j,hj,hm⟩ := seen_mem old t p hm
      obtain ⟨bits,hl⟩ := (fits j (by omega)).2 p hm
      exact probe_fits a p bits hl
  have hw := population_wire_length_of_public_bounds a R T old sized t ht
  apply prod_le _ _ _ _ (nat_le_self _)
  apply prod_le _ _ _ _ (show R.bits.length ≤ R.size by rw [Nat.size_eq_bits_len])
  apply prod_le _ _ _ _ ((nat_le_self _).trans a.isLt.le)
  apply prod_le _ _ _ _ (nat_le_self _)
  apply prod_le _ _ _ _ ((nat_le_self _).trans hlt)
  exact prod_le _ _ _ _ hw (prod_le _ _ _ _ hseen ((nat_le_self _).trans hp))

/-- Read the vote accumulator directly from the already completed root rounds. -/
def votesBefore {N : ℕ} (a : Fin N) (out : ℕ → RoundResult N) : ℕ → ℕ
  | 0 => 0
  | t+1 => votesBefore a out t + vote a (out t)

theorem votesBefore_le {N : ℕ} (a : Fin N) (out : ℕ → RoundResult N) (t : ℕ) :
    votesBefore a out t ≤ t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    have h : vote a (out t) ≤ 1 := by unfold vote; split <;> omega
    exact Nat.add_le_add ih h

def replayCursor {N : ℕ} (a : Fin N) (R T : ℕ) (out : ℕ → RoundResult N) (t : ℕ) :=
  Driver.sourceCursor R T (T-t) a (population R out t) (votesBefore a out t)

theorem replayCursor_start {N : ℕ} (a : Fin N) (R T : ℕ) (out : ℕ → RoundResult N) :
    replayCursor a R T out 0 = startCampaign N R a.val T := by
  change Driver.sourceCursor R T T a _ 0 = startCampaign N R a.val T
  exact (congrArg (fun st => CampaignCursor.mk N R a.val T T st) (startCampaign_state N R a.val T)).symm

theorem replayCursor_step {N : ℕ} (a : Fin N) (R T : ℕ) (out : ℕ → RoundResult N)
    (t : ℕ) (ht : t < T) :
    finishRound (replayCursor a R T out t) (packRound (population R out t).experts.length (out t)) =
      replayCursor a R T out (t+1) := by
  unfold replayCursor
  rw [show T-t=(T-(t+1))+1 by omega,Driver.finish_sourceCursor]
  rfl

/-- All fields of the real cursor satisfy the same bound after every prefix, including its
chronologically ordered copy of every probe's earlier price history. -/
theorem run_cursor_length {N : ℕ} (a : Fin N) (R T : ℕ)
    (reply : List (Query N × Bool) → Query N → Bool) (history : List (Query N × Bool))
    (out : ℕ → RoundResult N)
    (hx : ∀ j : Fin T, out j.val =
      ((trialLoop (Pool.batch N R) (runRound R (fun es => marketSolverAtCommonWeightUnit es))
        T (Population.start (Pool.batch N R))).run reply history) j) (t : ℕ) (ht : t ≤ T) :
    (campaignCursorCode (replayCursor a R T out t)).length ≤ cursorWidth N R T := by
  apply sourceCursor_length a R T _ _ t out (Nat.sub_le _ _) ((votesBefore_le a out t).trans ht) ht
    ((all_replay_bounds a R T _).run reply history out hx)
  intro j hj
  rw [hx ⟨j,hj⟩]
  exact (campaignLoop_guarded a R T).run reply history ⟨j,hj⟩

theorem combined_campaign_length (c : CampaignCursor) {L : ℕ}
    (h : (campaignCursorCode c).length ≤ L) : (combinedCode (.campaign c)).length ≤ L+1 :=
  Nat.add_le_add_right h 1

theorem combined_trial_length (c : CampaignCursor) (s : Trial.MachineState) {C E : ℕ}
    (hc : (campaignCursorCode c).length ≤ C) (hs : (stateCode s).length ≤ E) :
    (combinedCode (.trial c s)).length ≤ pairBound C E+1 :=
  Nat.add_le_add_right (prod_le _ _ _ _ hc hs) 1

end Wire
end Control
end PriceGame
end LinearProgramming
end Optimization
end OAI
