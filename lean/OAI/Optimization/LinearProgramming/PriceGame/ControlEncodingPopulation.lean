import OAI.Optimization.LinearProgramming.PriceGame.ControlEncodingBounds
import OAI.Optimization.LinearProgramming.PriceGame.FixedShareActualAllReplies

/-! The serialized root population produced by the public schedule. The score-moment bound
comes from returned recursive certificates, and applies to every choice of oracle replies. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Control
namespace Wire

open ExactQuantumFactoring.BitStackProgram
open Finset States.Mass Learning Campaign

private theorem member_batch {α : Type*} (batch : ℕ → List α) {t : ℕ} {x : α}
    (h : x ∈ Catalog.entries batch t) : ∃ k < t, x ∈ batch k := by
  induction t with
  | zero => simp [Catalog.entries] at h
  | succ t ih =>
    rcases List.mem_append.mp h with old | new
    · obtain ⟨k,hk,hx⟩ := ih old
      exact ⟨k,hk.trans (Nat.lt_succ_self _),hx⟩
    · exact ⟨t,Nat.lt_succ_self _,new⟩

theorem replay_expert_length {N : ℕ} (a : Fin N) (R : ℕ) (out : ℕ → RoundResult N)
    (t : ℕ) {e : Expert N} (he : e ∈ (population R out t).experts) :
    (packedExpertCode (packExpert e)).length ≤ expertBound (depth N) (2*N^2) N (28+2*(R+1).size) := by
  rw [population_entries] at he
  obtain ⟨_,_,hx⟩ := member_batch _ he
  exact batch_expert_length a.pos hx

private theorem size_le_of_le_pow {n k : ℕ} (h : n ≤ 2^k) : n.size ≤ k+1 :=
  Nat.size_le.mpr (h.trans_lt (Nat.pow_lt_pow_right (by decide) (Nat.lt_succ_self _)))

def expertCount (N R T : ℕ) := ((N+R.size+1)*(T+1))^Pool.catalogueExponent

def weightWidth (N R T : ℕ) :=
  let b := catalogueBits N R T
  10 + 2*T + 3*(b + (6+b)*T)

def poolWidth (N R T : ℕ) :=
  populationBound (expertCount N R T) (expertBound (depth N) (2*N^2) N (28+2*(R+1).size))
    (weightWidth N R T)

theorem population_wire_length_of_public_bounds {N : ℕ} (a : Fin N) (R T : ℕ)
    (out : ℕ → RoundResult N) (sized : ∀ k < T, PublicRoundBounds (population R out k) (out k))
    (t : ℕ) (ht : t ≤ T) :
    (packedPopulationCode (packPopulation (population R out t))).length ≤ poolWidth N R T := by
  apply packPopulation_le
  · exact population_length_of_observations a R T out (fun k hk => (sized k hk).observations) t ht
  · intro e he
    exact replay_expert_length a R out t he
  · intro q hq
    obtain ⟨j,hj,hval⟩ := List.mem_iff_getElem.mp hq
    have hj' : j < (population R out t).experts.length := by simpa using hj
    let i : Fin (population R out t).experts.length := ⟨j,hj'⟩
    have hv : populationWeights (population R out t) i = q := by simpa [populationWeights,i] using hval
    obtain ⟨_,_,_,_,_,hd,hn⟩ := population_guard_of_round_bounds a R T out sized t ht i
    rw [hv] at hd hn
    have h₁ := size_le_of_le_pow hd
    have h₂ := size_le_of_le_pow hn
    have h₃ := Nat.mul_le_mul_left (6+catalogueBits N R T) ht
    rw [rat_length,weightWidth]
    omega

/-- The actual serialized public pool, uniformly for every oracle and every trial prefix,
including the final batch. Both cardinality and rational lengths come from the execution. -/
theorem run_population_wire_length {N : ℕ} (a : Fin N) (R T : ℕ) (markets : AvailableMarkets N)
    (reply : List (Query N × Bool) → Query N → Bool) (history : List (Query N × Bool))
    (out : ℕ → RoundResult N)
    (hx : ∀ j : Fin T, out j.val =
      ((trialLoop (Pool.batch N R) (runRound R markets) T (Population.start (Pool.batch N R))).run reply history) j)
    (t : ℕ) (ht : t ≤ T) :
    (packedPopulationCode (packPopulation (population R out t))).length ≤ poolWidth N R T :=
  population_wire_length_of_public_bounds a R T out
    ((all_replay_bounds a R T markets).run reply history out hx) t ht

end Wire
end Control
end PriceGame
end LinearProgramming
end Optimization
end OAI
