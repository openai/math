import OAI.Computability.NearSquareRoot.InterchangeROMStageExecute
import OAI.Computability.NearSquareRoot.InterchangeROMStageVerifyTrajectory
import OAI.Computability.NearSquareRoot.InterchangeROMStageTableEffective

/-! # Joining the six sparse movements and five matrix scans on one live deck -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace InterchangeROMStage
open IntegerMultiplication IntegerMultiplication.Code Space InterchangeROM
  InterchangeROMStageTable Frame.Realization

private def rate (r : Fin 6 → ℕ) (t : Fin 5 → ℕ) : ℕ → ℕ
  | 0 => r 0 | 1 => r 1 | 2 => t 0 | 3 => r 2 | 4 => t 1 | 5 => r 3
  | 6 => t 2 | 7 => r 4 | 8 => t 3 | 9 => r 5 | 10 => t 4 | _ => 0

private theorem rRate (r : Fin 6 → ℕ) (t : Fin 5 → ℕ) (k : Fin 6) :
    rate r t (routePos k) = r k := by fin_cases k <;> rfl

private theorem tRate (r : Fin 6 → ℕ) (t : Fin 5 → ℕ) (k : Fin 5) :
    rate r t (inputBoundary k) = t k := by fin_cases k <;> rfl

private theorem trace_sum (r : Fin 6 → ℕ) (t : Fin 5 → ℕ) :
    traceClock (rate r t) 0 11 = 23 + (∑ i, r i) + ∑ i, t i := by
  simp [traceClock,rate,Fin.sum_univ_succ]
  omega

/-- The six route clocks include the actual recursive ledgers. Every clock
occurs once. All operators use the same physical return and data ceilings. -/
theorem join_rawStage (c : Parameters) (charts : List Opcode.Word) (wordCmd : Opcode.Word → Cmd)
    (state : ℕ → Tree) (rr : Fin 6 → ℕ) (tt : Fin 5 → ℕ) (cap depth : ℕ) (env : Env)
    (term : (state 11).count ≤ cap)
    (move : ∀ k : Fin 6, ∀ deck b, DeckCap b deck →
      BoundedFits env (routeCommand (fun m => wordCmd (lookup charts m)) (c.1.route c.2.2.1 (routePos k)))
        (pile 0 (state (routePos k)) deck) (pile 0 (state (routePos k+1)) deck)
        (rr k) (b+cap) depth)
    (table : ∀ k : Fin 5, ∀ deck b, DeckCap b deck →
      BoundedFits env (underHeader (command c (c.1.gate k (inputBoundary k))))
        (pile 0 (state (inputBoundary k)) deck) (pile 0 (state (inputBoundary k+1)) deck)
        (tt k) (b+cap) depth)
    (deck : Deck) (b : ℕ) (hb : DeckCap b deck) :
    BoundedFits env (rawStage c.1 c.2.1 c.2.2.1 (gateMatrix c) charts wordCmd)
      (pile 0 (state 0) deck) (pile 0 (state 11) deck) (23+(∑ k,rr k)+∑ k,tt k)
      (b+cap) (depth+1) := by
  let ops := c.1.script c.2.2.1
  let moveWord := fun m => wordCmd (lookup charts m)
  have rt (k : Fin 6) :
      (ops[routePos k]?) = some (.inr (c.1.route c.2.2.1 (routePos k))) := by fin_cases k <;> rfl
  have gt (k : Fin 5) :
      (ops[inputBoundary k]?) = some (.inl (c.1.gate k (inputBoundary k))) := by fin_cases k <;> rfl
  have covering (i : ℕ) (hi : i < ops.length) :
      (∃ k, routePos k = i) ∨ (∃ k, inputBoundary k = i) := by
    change i < 11 at hi
    interval_cases i
    · exact .inl ⟨0,rfl⟩
    · exact .inl ⟨1,rfl⟩
    · exact .inr ⟨0,rfl⟩
    · exact .inl ⟨2,rfl⟩
    · exact .inr ⟨1,rfl⟩
    · exact .inl ⟨3,rfl⟩
    · exact .inr ⟨2,rfl⟩
    · exact .inl ⟨4,rfl⟩
    · exact .inr ⟨3,rfl⟩
    · exact .inl ⟨5,rfl⟩
    · exact .inr ⟨4,rfl⟩
  have step : ∀ i (hi : i < ops.length), ∀ d s, DeckCap s d →
      BoundedFits env (instruction (command c) moveWord ops[i]) (pile 0 (state i) d)
        (pile 0 (state (i+1)) d) (rate rr tt i) (s+cap) depth := by
    intro i hi d s hs
    obtain ⟨k,rfl⟩ | ⟨k,rfl⟩ := covering i hi
    · rw [(List.getElem_of_getElem? (rt k)).choose_spec,rRate]
      exact move k d s hs
    · rw [(List.getElem_of_getElem? (gt k)).choose_spec,tRate]
      exact table k d s hs
  have ran := execute_trace (command c) moveWord env state (rate rr tt) cap depth ops 0 term
    (fun i hi d s hs => by simpa only [Nat.zero_add] using step i hi d s hs) deck b hb
  change BoundedFits env _ _ _ (traceClock (rate rr tt) 0 11) _ _ at ran
  rw [trace_sum] at ran
  have cmd : program (command c) moveWord ops = rawStage c.1 c.2.1 c.2.2.1 (gateMatrix c) charts wordCmd := by
    apply congrArg (fun f => program f moveWord ops)
    funext t
    exact command_eq c t
  rw [cmd] at ran
  exact ran

end InterchangeROMStage

end NearSquareRoot
end Computability
end OAI
