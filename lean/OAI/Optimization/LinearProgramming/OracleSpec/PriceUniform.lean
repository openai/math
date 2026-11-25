import OAI.Optimization.LinearProgramming.OracleSpec.PaddedDialogue
import OAI.Optimization.LinearProgramming.OracleSpec.PriceRealization

/-! Uniform running-time transfer for the independent principal PCG specification. The
input encodings, terminating interactive session and its mathematical correctness stay
separate from the compiled finite program and its polynomial bounds. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace OracleSpec

open ExactQuantumFactoring.BitStackProgram
open PriceGame

/-- At positive arguments every natural polynomial is dominated by a single monomial. -/
theorem eval_le_monomial (P : Polynomial ℕ) (x : ℕ) (hx : 0 < x) :
    P.eval x ≤ P.eval 1 * x ^ P.natDegree := by
  simp only [Polynomial.eval_eq_sum, Polynomial.sum_def, one_pow, mul_one, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i hi
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hx (P.le_natDegree_of_mem_supp i hi))

/-- The compiled dispatcher, state and interaction polynomials give this one public clock. -/
noncomputable def totalClock (dispatch state rounds : Polynomial ℕ) : Polynomial ℕ :=
  64*(Polynomial.X+1)^2 + rounds*(dispatch.comp state + 10*state+15) + 3

theorem totalClock_eval (dispatch state rounds : Polynomial ℕ) (x : ℕ) :
    (totalClock dispatch state rounds).eval x = 64*(x+1)^2 +
      rounds.eval x * (dispatch.eval (state.eval x) + 10*state.eval x + 15) + 3 := by
  simp [totalClock, Polynomial.eval_comp]

/-- A genuinely compiled dispatcher suffices if the source strategy is correct and its
actual runs have dimension-polynomial state widths and round counts. The single machine,
input encoding, output bit and full adaptive transcript are all those of the reference.
Polynomial parameters and code are fixed before the public or hidden inputs. -/
theorem paddedPriceProgram_correct {I C : Type} {ei : I → Word} {ec : C → Word}
    {dispatch : I ⊕ (Bool × C) → Bool ⊕ (Word × C)} (p : Dialogue.ProcedureOf ei ec dispatch)
    (initial : ∀ (N _R : ℕ), Fin N → I) (width count : Polynomial ℕ)
    (strategy : ∀ (N _R : ℕ), Fin N → Computation N Bool)
    (pad : ∀ (N R : ℕ) (a : Fin N), ei (initial N R a) =
      frame (List.replicate N true) ++ priceInput R a)
    (correct : ∀ (N R : ℕ), 0 < N → 0 < R → ∀ (a : Fin N) (h : Hidden N R a) b,
      Computation.Reaches h (strategy N R a) b → b = h.positive)
    (sessions : ∀ (N R : ℕ), 0 < N → 0 < R → ∀ (a : Fin N) (reply : Transcript → Word → Bool),
      let x := N + (R+1).log2 + 1
      let played := serializedPlay reply (strategy N R a) []
      ∃ l n, l ≤ width.eval x ∧ n ≤ count.eval x ∧ Dialogue.Session ei ec dispatch reply l
        (.inl (initial N R a)) [] played.1 played.2 n) :
    ∀ (N R : ℕ), 0 < N → 0 < R → ∀ (a : Fin N) (reply : Transcript → Word → Bool),
      (Dialogue.paddedMachine p).ComputesWithin (fun history query => [reply history query])
        (priceInput R a) ((totalClock p.shared.bound width count).eval 1 *
          (N+(R+1).log2+1)^(totalClock p.shared.bound width count).natDegree) (pricePost R a) := by
  let poly := totalClock p.shared.bound width count
  intro N R hn hr a reply
  let x := N + (R+1).log2 + 1
  let tail := encodeNat R ++ encodeNat a.val
  obtain ⟨l,n,hl,hround,session⟩ := sessions N R hn hr a reply
  have encoded : ei (initial N R a) = frame (List.replicate N true) ++ (encodeNat N ++ tail) := by
    simpa [priceInput, tail, List.append_assoc] using pad N R a
  obtain ⟨t,s,run,budget,stop,result⟩ := Dialogue.paddedMachine_computes p reply N tail encoded session
  have bound₁ : 64*(N+1)^2 ≤ 64*(x+1)^2 := by
    have h : N+1 ≤ x+1 := by dsimp [x]; omega
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h _)
  have hl' : p.shared.bound.eval l ≤ p.shared.bound.eval (width.eval x) := Procedure.eval_nat_mono _ hl
  have whole := Nat.mul_le_mul hround (show p.shared.bound.eval l + 10*l + 15 ≤
    p.shared.bound.eval (width.eval x)+10*(width.eval x)+15 by dsimp [x] at *; omega)
  have bounded : t ≤ poly.eval x := by
    rw [show poly.eval x = _ from totalClock_eval p.shared.bound width count x]
    exact budget.trans (Nat.add_le_add_right (Nat.add_le_add bound₁ whole) 3)
  refine ⟨t, s, ?_, bounded.trans (eval_le_monomial poly x (by dsimp [x]; omega)), stop, ?_⟩
  · simpa only [priceInput, tail, List.append_assoc] using run
  · rw [result.1, result.2]
    exact serializedPlay_post _ (correct N R hn hr a) reply

/-- The frozen existential statement follows with the same explicit program and clock. -/
theorem extremalSignRecovery_of_dispatch {I C : Type} {ei : I → Word} {ec : C → Word}
    {dispatch : I ⊕ (Bool × C) → Bool ⊕ (Word × C)} (p : Dialogue.ProcedureOf ei ec dispatch)
    (initial : ∀ (N _R : ℕ), Fin N → I) (width count : Polynomial ℕ)
    (strategy : ∀ (N _R : ℕ), Fin N → Computation N Bool)
    (pad : ∀ (N R : ℕ) (a : Fin N), ei (initial N R a) =
      frame (List.replicate N true) ++ priceInput R a)
    (correct : ∀ (N R : ℕ), 0 < N → 0 < R → ∀ (a : Fin N) (h : Hidden N R a) b,
      Computation.Reaches h (strategy N R a) b → b = h.positive)
    (sessions : ∀ (N R : ℕ), 0 < N → 0 < R → ∀ (a : Fin N) (reply : Transcript → Word → Bool),
      let x := N + (R+1).log2 + 1
      let played := serializedPlay reply (strategy N R a) []
      ∃ l n, l ≤ width.eval x ∧ n ≤ count.eval x ∧ Dialogue.Session ei ec dispatch reply l
        (.inl (initial N R a)) [] played.1 played.2 n) : ExtremalSignRecovery := by
  let poly := totalClock p.shared.bound width count
  exact ⟨Dialogue.paddedMachine p, poly.eval 1, poly.natDegree,
    paddedPriceProgram_correct p initial width count strategy pad correct sessions⟩

end OracleSpec
end LinearProgramming
end Optimization
end OAI
