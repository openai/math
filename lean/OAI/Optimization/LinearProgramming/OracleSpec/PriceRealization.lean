import OAI.Optimization.LinearProgramming.OracleSpec.PriceGame
import Mathlib.Data.Fintype.Basic
import OAI.Optimization.LinearProgramming.OracleSpec.CompilerProof
import OAI.Optimization.LinearProgramming.PriceGame.Computation

/-! Relate the paper's typed, adaptive PCG strategy to the independent wire specification.
A separate program proof is required to obtain a bit-time bound from a strategy. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace OracleSpec

open PriceGame

variable {N : ℕ} {α : Type*}

def queryWord (q : Query N) : Word := priceQuery q.index q.prices

/-- Replay an arbitrary raw answer strategy on the typed computation, producing both the
result and the actual wire transcript in reverse chronological order. -/
def serializedPlay (reply : Transcript → Word → Bool) :
    Computation N α → Transcript → α × Transcript
  | .pure x, past => (x, past)
  | .ask q next, past =>
    let packet := queryWord q
    let b := reply past packet
    serializedPlay reply (next b) ((packet, [b]) :: past)

theorem serializedPlay_keeps (p : Computation N α) (reply : Transcript → Word → Bool)
    (past : Transcript) : ∀ e ∈ past, e ∈ (serializedPlay reply p past).2 := by
  induction p generalizing past with
  | pure => exact fun _ he => he
  | ask q next ih =>
    intro e he
    exact ih _ _ e (List.mem_cons_of_mem _ he)

private theorem serializedPlay_valid (p : Computation N α) (reply : Transcript → Word → Bool)
    (past : Transcript) (h : ∀ e ∈ past, ∃ i t, e.1 = priceQuery (N := N) i t) :
    ∀ e ∈ (serializedPlay reply p past).2, ∃ i t, e.1 = priceQuery (N := N) i t := by
  induction p generalizing past with
  | pure => exact h
  | ask q next ih =>
    apply ih
    intro e he
    rcases List.mem_cons.mp he with rfl | he
    · exact ⟨q.index, q.prices, rfl⟩
    · exact h _ he

/-- Consistency is required only on observed exchanges, including every tied minimizer.
No off-transcript correctness assumption is needed. -/
theorem serializedPlay_reaches {N R : ℕ} {anchor : Fin N} (h : Hidden N R anchor)
    (p : Computation N α) (reply : Transcript → Word → Bool) (past : Transcript)
    (valid : priceConsistent h.positive h.active (fun i => (h.cost i).val)
      (serializedPlay reply p past).2) :
    Computation.Reaches h p (serializedPlay reply p past).1 := by
  induction p generalizing past with
  | pure x => exact .pure x
  | ask q next ih =>
    let b := reply past (queryWord q)
    let past' := (queryWord q, [b]) :: past
    change Computation.Reaches h (.ask q next) (serializedPlay reply (next b) past').1
    apply Computation.Reaches.ask (reply := b) _ (ih b past' valid)
    intro forced
    have mem : (queryWord q, [b]) ∈ (serializedPlay reply (next b) past').2 :=
      serializedPlay_keeps (next b) reply past' _ List.mem_cons_self
    have bit := valid q.index q.prices [b] mem forced.1 forced.2
    exact (List.cons.inj bit).1

private noncomputable def hiddenWitness {N R : ℕ} {anchor : Fin N} (positive : Bool)
    (active : Set (Fin N)) (costs : Fin N → ℕ) (ha : anchor ∈ active) : Hidden N R anchor := by
  classical
  exact { positive := positive, active := Finset.univ.filter (fun i => i ∈ active), anchor_mem := by simpa using ha,
          cost := fun j => ⟨min (costs j) R, Nat.lt_succ_of_le (min_le_right _ _)⟩ }

private theorem hiddenWitness_consistent {N R : ℕ} {anchor : Fin N} {positive : Bool}
    {active : Set (Fin N)} {costs : Fin N → ℕ} (ha : anchor ∈ active)
    (hw : ∀ j ∈ active, costs j ≤ R) {hist : Transcript}
    (valid : priceConsistent positive active costs hist) :
    let h := hiddenWitness (R := R) positive active costs ha
    priceConsistent h.positive h.active (fun i => (h.cost i).val) hist := by
  classical
  dsimp only
  intro i t answer he hi hmin
  have hi' : i ∈ active := by simpa [hiddenWitness] using hi
  apply valid i t answer he hi'
  intro j hj
  have hj' : j ∈ (hiddenWitness (R := R) positive active costs ha).active := by
    simpa [hiddenWitness] using hj
  have bound := hmin j hj'
  change ((min (costs i) R : ℕ) : ℚ) + (if positive then t i else -t i) ≤
    ((min (costs j) R : ℕ) : ℚ) + (if positive then t j else -t j) at bound
  rw [min_eq_left (hw i hi'), min_eq_left (hw j hj)] at bound
  exact bound

theorem serializedPlay_post {N R : ℕ} {anchor : Fin N} (p : Computation N Bool)
    (correct : ∀ (h : Hidden N R anchor) b, Computation.Reaches h p b → b = h.positive)
    (reply : Transcript → Word → Bool) :
    pricePost R anchor (serializedPlay reply p []).2 [(serializedPlay reply p []).1] := by
  refine ⟨serializedPlay_valid p reply [] (by simp), ⟨_, rfl⟩, ?_⟩
  intro positive active costs ha hw consistent
  let h := hiddenWitness (R := R) positive active costs ha
  have reachable := serializedPlay_reaches h p reply [] (hiddenWitness_consistent ha hw consistent)
  exact congrArg (fun b => [b]) (correct h _ reachable)

/-- The complete link from uniform, charged structured code to the frozen principal
statement. The code must implement each input-dependent strategy on *all* reply histories. -/
theorem extremalSignRecovery_of_code {k : ℕ} (code : BitCode k) (input answer : Fin k)
    (C degree : ℕ) (strategy : ∀ (N _R : ℕ), Fin N → Computation N Bool)
    (correct : ∀ (N R : ℕ), 0 < N → 0 < R → ∀ (anchor : Fin N) (h : Hidden N R anchor) b,
      Computation.Reaches h (strategy N R anchor) b → b = h.positive)
    (implementation : ∀ (N R : ℕ), 0 < N → 0 < R → ∀ (anchor : Fin N) (reply : Transcript → Word → Bool),
      ∃ m n, BitCode.Executes answer (fun hist packet => [reply hist packet]) code
          (BitCode.startMemory input (priceInput R anchor)) m n ∧
        n+1 ≤ C*(N+(R+1).log2+1)^degree ∧ m.transcript = (serializedPlay reply (strategy N R anchor) []).2 ∧
        m.bufferRev.reverse = [(serializedPlay reply (strategy N R anchor) []).1]) : ExtremalSignRecovery := by
  refine ⟨code.compile input answer, C, degree, ?_⟩
  intro N R hN hR anchor reply
  obtain ⟨m,n,hr,hn,hist,out⟩ := implementation N R hN hR anchor reply
  apply BitCode.compile_computes hr hn
  rw [hist, out]
  exact serializedPlay_post _ (correct N R hN hR anchor) reply

end OracleSpec
end LinearProgramming
end Optimization
end OAI
