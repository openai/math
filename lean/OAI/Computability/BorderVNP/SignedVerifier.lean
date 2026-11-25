import OAI.Computability.VPVNP.VerifierMachine
import OAI.Computability.BorderVNP.SignedPaths

/-!
# Verifying the sign of a universal path

The decoder and transition layers are shared with the exact-circuit verifier.
At the signed clock we read both the accepting state and the symbol at the work
head. This yields one Boolean output for each of the two possible nonzero signs.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace SignedVerifier

open VPVNP VPVNP.UniversalMachine VPVNP.VerifierMachineDecode
open VPVNP.VerifierMachineIteration VPVNP.VerifierNetwork
open BinPackingGames.Foundations.Complexity.CookLevin.CircuitBatch.Frame (step_gate_count_sum)
open BinPackingGames.Foundations.Complexity.CookLevin.StatementCircuit (Expr.eval Expr.size)

private abbrev Inputs (n T : ℕ) := Fin n ⊕ Fin T
private abbrev Decoded (n T : ℕ) := Inputs n T ⊕ DecoderWire n

private noncomputable def parse (n T : ℕ) : Frame (Inputs n T) (Decoded n T) :=
  ((decoder n).subst (Frame.initial Sum.inl)).withInput

private def initExpr (n T : ℕ) : Slice n T T → Expr (Decoded n T)
  | .inl i => .input (.inl i)
  | .inr (.inl d) => .input (.inr d)
  | .inr (.inr j) => initialRegisterExpr (fun i => .inl (.inl i)) (.inr .empty) j

private noncomputable def start (n T : ℕ) := (parse n T).step (initExpr n T)

private theorem parse_word {n T : ℕ} (x : Fin n → Bool) (w : Fin T → Bool) :
    (Frame.initial Sum.inl : Frame (Inputs n T) (Fin n)).eval (Sum.elim x w) = x := by
  funext i
  simp

private theorem start_decode {n T : ℕ} (x : Fin n → Bool) (w : Fin T → Bool) (d : DecoderWire n) :
    (start n T).eval (Sum.elim x w) (.inr (.inl d)) = (decoder n).eval x d := by
  simp [start, initExpr, Expr.eval, parse, parse_word]

private theorem start_size_le (n T : ℕ) :
    (start n T).size ≤ (decoder n).size + Fintype.card (Slice n T T) * 2 := by
  have h := Frame.step_size_le (parse n T) (initExpr n T) 2 (by
    rintro (i | d | j)
    · exact Nat.le_succ _
    · exact Nat.le_succ _
    · dsimp only [initExpr]
      exact initialRegisterExpr_size_le _ _ j)
  simpa [start, parse] using h

private def workHead (n T : ℕ) : Slice n T T :=
  .inr (.inr (.inr (true, windowCenter T, 2)))

private def readSign (negative : Bool) (n T : ℕ) (_ : Unit) : Expr (Slice n T T) :=
  let accepted : Expr (Slice n T T) := .and (.input (.inr (.inl .valid))) (.input (.inr (.inr (.inl ⟨1, by omega⟩))))
  let minus : Expr (Slice n T T) := .input (workHead n T)
  .and accepted (if negative then minus else .not minus)

private noncomputable def signFrame (negative : Bool) (n T : ℕ) : Frame (Inputs n T) Unit :=
  (simulate (start n T)).step (readSign negative n T)

private theorem signFrame_eval {n T : ℕ} (negative : Bool) (x : Fin n → Bool) (w : Fin T → Bool) :
    (signFrame negative n T).eval (Sum.elim x w) () =
      ((accept (start n T)).eval (Sum.elim x w) () &&
        ((simulate (start n T)).eval (Sum.elim x w) (workHead n T) == negative)) := by
  cases negative <;> cases h : (simulate (start n T)).eval (Sum.elim x w) (workHead n T) <;>
    simp [signFrame, readSign, accept, Expr.eval, h] <;> rfl

private theorem frame_eval_sign {n : ℕ} (negative : Bool) (x : Fin n → Bool)
    (w : Fin (n ^ 100) → Bool) :
    (signFrame negative n (n ^ 100)).eval (Sum.elim x w) () =
      decide (signedWitness x w = if negative then -1 else 1) := by
  let T := n ^ 100
  rw [signFrame_eval]
  cases hd : decode (List.ofFn x) with
  | none =>
    have hv : (start n T).eval (Sum.elim x w) (.inr (.inl .valid)) = false := by
      rw [start_decode, Bool.eq_false_iff]
      simp [decoder_eval_iff, hd]
    rw [accept_eval_invalid _ _ hv, Bool.false_and]
    cases negative <;> simp [signedWitness, hd]
  | some p =>
    have hp : p.extra ≤ n := by simpa using decoded_extra_le_length hd
    have decodeBits (q : DecoderWire n) : (decoder n).eval x q = true ↔ wireHolds p q := by
      simp [decoder_eval_iff, hd]
    have hv : (start n T).eval (Sum.elim x w) (.inr (.inl .valid)) = true := by
      rw [start_decode, decodeBits]; trivial
    have hs (i b k) : (start n T).eval (Sum.elim x w) (.inr (.inl (.slot i b k))) = true ↔
        wireHolds p (.slot i b k) := by rw [start_decode, decodeBits]
    have hr (j : WindowRegister n T) :
        (start n T).eval (Sum.elim x w) (.inr (.inr j)) = registerEncoding (windowInitial p T x) j := by
      rw [start, Frame.step_eval]
      dsimp only [initExpr]
      apply initialRegisterExpr_eval _ _ _ x p
      · intro i; simp [parse]
      · simp only [parse, Frame.withInput_eval_inr, Frame.subst_eval, parse_word]
        exact Bool.eq_iff_iff.mpr (by simpa [wireHolds] using decodeBits .empty)
    have hw (i : Fin T) : (start n T).eval (Sum.elim x w) (.inl (.inr i)) = w i := by
      simp [start, initExpr, Expr.eval, parse]
    let full := (List.ofFn w).foldl (choiceStep p) (initial p (List.ofFn x))
    let win := windowRun p (windowInitial p T x) (List.ofFn w)
    have agrees : WindowAgrees 0 win full := windowRun_agrees p (List.ofFn w) (by simp [T])
      _ _ (windowInitial_agrees p T _ x)
    have headEq : win.secondTape (windowCenter T) = full.secondTape.head := by
      simpa [windowOffset, windowCenter] using agrees.second (windowCenter T)
        (by simp [windowOffset, windowCenter]) (by simp [windowOffset, windowCenter])
    have headBit : (simulate (start n T)).eval (Sum.elim x w) (workHead n T) =
        decide (full.secondTape.head = 2) := by
      rw [workHead, simulate_eval_register _ _ p hp _ w hs hr hw]
      change decide (win.secondTape (windowCenter T) = 2) = _
      rw [headEq]
    rw [accept_eval_valid _ _ p hp _ w hv hs hr hw, headBit]
    change (decide (win.state.val = 1) && (decide (full.secondTape.head = 2) == negative)) = _
    rw [agrees.state]
    simp only [signedWitness, hd, haltOutput]
    change (decide (full.state.val = 1) && (decide (full.secondTape.head = 2) == negative)) =
      decide ((if full.state.val = 1 then if full.secondTape.head = 2 then -1 else 1 else 0 : ℤ) =
        if negative then -1 else 1)
    by_cases ha : full.state.val = 1 <;> by_cases hm : full.secondTape.head = 2 <;>
      cases negative <;> simp [ha, hm]

/-- Gate count of the compiled test for the indicated sign. -/
noncomputable def size (negative : Bool) (n : ℕ) := (signFrame negative n (n ^ 100)).circuitSize ()

/-- The compiled AND/NOT verifier tests for minus when `negative` is true, and plus otherwise. -/
noncomputable def circuit (negative : Bool) (n : ℕ) :
    BooleanTranscript.Circuit (Fin n ⊕ Fin (n ^ 100)) (size negative n) :=
  (signFrame negative n (n ^ 100)).circuit ()

/-- Evaluation of the Boolean gates agrees with the signed outcome on the full, unbounded tapes. -/
theorem circuit_eval {n : ℕ} (negative : Bool) (x : Fin n → Bool) (w : Fin (n ^ 100) → Bool) :
    (circuit negative n).eval (Sum.elim x w) = decide (signedWitness x w = if negative then -1 else 1) :=
  (Frame.circuit_eval ..).trans (frame_eval_sign negative x w)

private theorem size_mono {σ τ ρ : Type*} [Fintype σ] [Fintype τ] [Fintype ρ]
    (f : Frame σ τ) (e : ρ → Expr τ) : f.size ≤ (f.step e).size := by
  unfold Frame.size Frame.step
  rw [step_gate_count_sum]
  exact Nat.le_add_right _ _

private theorem frame_size_le (negative : Bool) (n T : ℕ) :
    (signFrame negative n T).size ≤ (decoder n).size + Fintype.card (Slice n T T) * 2 +
      T * (Fintype.card (Slice n T T) * (1000000 * (n + 2) ^ 2)) + 9 := by
  have ha := accept_size_le (start n T)
  have hm : (simulate (start n T)).size ≤ (accept (start n T)).size := size_mono ..
  have hr := Frame.step_size_le (simulate (start n T)) (readSign negative n T) 6 (fun _ => by
    cases negative <;> simp [readSign, Expr.size])
  simp only [Fintype.card_unit, Nat.one_mul] at hr
  have hi := start_size_le n T
  unfold signFrame
  omega

/-- Both signs have polynomially bounded verifier size, including all decoding and simulation gates. -/
theorem size_polynomiallyBounded (negative : Bool) : PolynomiallyBounded (size negative) := by
  let t (n : ℕ) := n ^ 100
  have ht : PolynomiallyBounded t := PolynomiallyBounded.id.pow _
  have h₂ := PolynomiallyBounded.id.add (.const 2)
  have hcard : PolynomiallyBounded (fun n => Fintype.card (Slice n (t n) (t n))) := by
    simp only [card_slice]
    have table := (PolynomiallyBounded.const 2).add
      (((((PolynomiallyBounded.const 9).mul .id).mul (.const 2)).mul h₂).mul (.const 81))
    have cells := ((PolynomiallyBounded.const 2).mul ht).add (.const 1)
    have tapes := (PolynomiallyBounded.const 2).mul (cells.mul (.const 3))
    exact (PolynomiallyBounded.id.add ht).add (table.add (h₂.add tapes))
  have hdecode := (PolynomiallyBounded.const 6000000000).mul (PolynomiallyBounded.succ.pow 9)
  have hstep := (PolynomiallyBounded.const 1000000).mul (h₂.pow 2)
  have hf : PolynomiallyBounded (fun n => (signFrame negative n (t n)).size) :=
    ((((hdecode.of_le decoder_size_le).add (hcard.mul (.const 2))).add
      (ht.mul (hcard.mul hstep))).add (.const 9)).of_le (fun n => frame_size_le negative n (t n))
  exact ((PolynomiallyBounded.const 4).mul hf).of_le fun n => (signFrame negative n (t n)).circuitSize_le ()

end SignedVerifier

end BorderVNP
end Computability
end OAI
