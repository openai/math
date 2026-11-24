import OAI.Computability.VPVNP.VerifierMachineDecodeNetwork
import OAI.Computability.VPVNP.VerifierMachineInitial
import OAI.Computability.VPVNP.VerifierMachineIteration
import OAI.Computability.VPVNP.VerifierMachineSplice
import OAI.Computability.VPVNP.PolynomialBounds

/-!
# Boolean circuits for the coefficient verifier

The input consists of the word and one choice bit per clock tick. The first circuit
decodes the transition table from the word. The next layer initializes the tape windows,
and the simulation applies one transition per choice bit. This gives a polynomial-size
Boolean verifier for the coefficients in equation (1.1).
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace VerifierMachine

open UniversalMachine VerifierMachineDecode VerifierMachineIteration VerifierNetwork
open BinPackingGames.Foundations.Complexity.CookLevin.StatementCircuit (Expr.eval Expr.size)

private abbrev Inputs (n T : ℕ) := Fin n ⊕ Fin T
private abbrev Decoded (n T : ℕ) := Inputs n T ⊕ DecoderWire n

private noncomputable def parseInputs (n T : ℕ) : Frame (Inputs n T) (Decoded n T) :=
  ((decoder n).subst (Frame.initial Sum.inl)).withInput

private def initExpr (n T : ℕ) : Slice n T T → Expr (Decoded n T)
  | .inl i => .input (.inl i)
  | .inr (.inl d) => .input (.inr d)
  | .inr (.inr j) => initialRegisterExpr (fun i => .inl (.inl i)) (.inr .empty) j

private noncomputable def initialFrame (n T : ℕ) : Frame (Inputs n T) (Slice n T T) :=
  (parseInputs n T).step (initExpr n T)

private theorem wordInputs_eval {n T : ℕ} (x : Fin n → Bool) (w : Fin T → Bool) :
    (Frame.initial Sum.inl : Frame (Inputs n T) (Fin n)).eval (Sum.elim x w) = x := by
  funext i
  simp

private theorem initialize_decoder {n T : ℕ} (x : Fin n → Bool) (w : Fin T → Bool)
    (d : DecoderWire n) :
    (initialFrame n T).eval (Sum.elim x w) (.inr (.inl d)) = (decoder n).eval x d := by
  simp [initialFrame, initExpr, Expr.eval, parseInputs, wordInputs_eval]

private theorem initialize_size_le (n T : ℕ) :
    (initialFrame n T).size ≤ (decoder n).size + Fintype.card (Slice n T T) * 2 := by
  have h := Frame.step_size_le (parseInputs n T) (initExpr n T) 2 (by
    rintro (i | d | j)
    · exact Nat.le_succ _
    · exact Nat.le_succ _
    · dsimp only [initExpr]
      exact initialRegisterExpr_size_le _ _ j)
  simpa [initialFrame, parseInputs] using h

/-- The final Boolean circuit checks that the literal program is valid and that its
canonical path choices end in acceptance after the universal clock. -/
noncomputable def verifierFrame (n : ℕ) : Frame (Inputs n (n ^ clockExponent)) Unit :=
  accept (initialFrame n (n ^ clockExponent))

theorem verifierFrame_eval {n : ℕ} (x : Fin n → Bool)
    (w : Fin (n ^ clockExponent) → Bool) :
    (verifierFrame n).eval (Sum.elim x w) () = verifiesInput x w := by
  let T := n ^ clockExponent
  unfold verifierFrame
  simp only [verifiesInput]
  cases hd : decode (List.ofFn x) with
  | none =>
    apply accept_eval_invalid
    rw [initialize_decoder, Bool.eq_false_iff]
    simp [decoder_eval_iff, hd]
  | some p =>
    have hv (q : DecoderWire n) : (decoder n).eval x q = true ↔ wireHolds p q := by
      simp [decoder_eval_iff, hd]
    have hp : p.extra ≤ n := by simpa using decoded_extra_le_length hd
    rw [accept_eval_valid (initialFrame n T) (Sum.elim x w) p hp (windowInitial p T x) w]
    · exact windowRun_acceptsChoices p T T le_rfl x w
    · rw [initialize_decoder, hv]
      trivial
    · intro i b k
      rw [initialize_decoder, hv]
    · intro j
      rw [initialFrame, Frame.step_eval]
      dsimp only [initExpr]
      apply initialRegisterExpr_eval _ _ _ x p
      · intro i
        simp [parseInputs]
      · simp only [parseInputs, Frame.withInput_eval_inr, Frame.subst_eval, wordInputs_eval]
        exact Bool.eq_iff_iff.mpr (by simpa [wireHolds] using hv .empty)
    · intro i
      simp [initialFrame, initExpr, Expr.eval, parseInputs]

/-- Size of the compiled verifier, counting binary AND and unary NOT gates. -/
noncomputable def verifierSize (n : ℕ) := (verifierFrame n).circuitSize ()

/-- The single-output Boolean circuit on the input bits and its canonical path-choice bits. -/
noncomputable def verifierCircuit (n : ℕ) :
    BooleanTranscript.Circuit (Fin n ⊕ Fin (n ^ clockExponent)) (verifierSize n) :=
  (verifierFrame n).circuit ()

theorem verifierCircuit_eval {n : ℕ} (x : Fin n → Bool)
    (w : Fin (n ^ clockExponent) → Bool) :
    (verifierCircuit n).eval (Sum.elim x w) = verifiesInput x w :=
  (Frame.circuit_eval ..).trans (verifierFrame_eval x w)

theorem verifierFrame_polynomiallyBounded : PolynomiallyBounded (fun n => (verifierFrame n).size) := by
  let t (n : ℕ) := n ^ clockExponent
  have ht : PolynomiallyBounded t := PolynomiallyBounded.id.pow _
  have h₂ : PolynomiallyBounded (fun n => n + 2) := PolynomiallyBounded.id.add (.const 2)
  have hcard : PolynomiallyBounded (fun n => Fintype.card (Slice n (t n) (t n))) := by
    simp only [card_slice]
    have table := (PolynomiallyBounded.const 2).add
      (((((PolynomiallyBounded.const 9).mul .id).mul (.const 2)).mul h₂).mul (.const 81))
    have cells := ((PolynomiallyBounded.const 2).mul ht).add (.const 1)
    have tapes := (PolynomiallyBounded.const 2).mul (cells.mul (.const 3))
    exact (PolynomiallyBounded.id.add ht).add (table.add (h₂.add tapes))
  have hdecode := (PolynomiallyBounded.const 6000000000).mul (PolynomiallyBounded.succ.pow 9)
  have hinit : PolynomiallyBounded (fun n => (initialFrame n (t n)).size) :=
    (hdecode.add (hcard.mul (.const 2))).of_le (fun n => (initialize_size_le n (t n)).trans
      (Nat.add_le_add_right (decoder_size_le n) _))
  have hstep := (PolynomiallyBounded.const 1000000).mul (h₂.pow 2)
  exact
    ((hinit.add (ht.mul (hcard.mul hstep))).add (.const 3)).of_le
      (fun n => accept_size_le (initialFrame n (t n)))

theorem verifierSize_polynomiallyBounded : PolynomiallyBounded verifierSize :=
  ((PolynomiallyBounded.const 4).mul verifierFrame_polynomiallyBounded).of_le
    (fun n => (verifierFrame n).circuitSize_le ())

end VerifierMachine

end VPVNP
end Computability
end OAI
