import OAI.Computability.QuantumFactoring.BooleanNetworkFurther

/-! # Unrolling signed-verifier circuits on shrinking frames

A circuit of radius `r+1` takes the immutable bits, one chronological guess,
and the current frame, and emits the frame of radius `r`. Register selection
carries all immutable bits and future guesses at zero gate cost.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

namespace SignedFrame
open ExactQuantumFactoring
open scoped BigOperators

variable {I W O : ℕ} (F : ℕ → ℕ)

/-- Evaluation of the ticks in decreasing radius and increasing guess position. -/
def run (tick : (r : ℕ) → (Fin I → Bool) → Bool → (Fin (F (r+1)) → Bool) → (Fin (F r) → Bool))
    (imm : Fin I → Bool) :
    (t : ℕ) → (Fin t → Bool) → (Fin (F t) → Bool) → Fin (F 0) → Bool
  | 0, _, frame => frame
  | t+1, bits, frame => run tick imm t (Fin.tail bits) (tick t imm (bits 0) frame)

variable (step : ∀ r, BooleanNetwork ((I+1) + F (r+1)) (F r))

/-- Use external input wires directly for the immutable and guess registers.
The initial frame can itself be computed by an arbitrary circuit on those inputs. -/
def compile : (t : ℕ) → (Fin I → Fin W) → (Fin t → Fin W) →
    BooleanNetwork W (F t) → BooleanNetwork W (F 0)
  | 0, _, _, start => start
  | t+1, imm, bits, start =>
    let immutableBit := BooleanNetwork.select (Fin.append imm (fun _ : Fin 1 => bits 0))
    compile t imm (Fin.tail bits) ((immutableBit.pair start).comp (step t))

def tickEval (r : ℕ) (imm : Fin I → Bool) (bit : Bool) (frame : Fin (F (r+1)) → Bool) :
    Fin (F r) → Bool :=
  (step r).eval (Fin.append (Fin.append imm (fun _ : Fin 1 => bit)) frame)

theorem compile_eval (t : ℕ) (imm : Fin I → Fin W) (bits : Fin t → Fin W)
    (start : BooleanNetwork W (F t)) (x : Fin W → Bool) :
    (compile F step t imm bits start).eval x =
      run F (tickEval F step) (x ∘ imm) t (x ∘ bits) (start.eval x) := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [compile, ih, BooleanNetwork.eval_comp, BooleanNetwork.eval_pair, BooleanNetwork.eval_select]
    have hp : x ∘ Fin.append imm (fun _ : Fin 1 => bits 0) =
        Fin.append (x ∘ imm) (fun _ : Fin 1 => x (bits 0)) := by
      funext i
      induction i using Fin.addCases <;> simp
    rw [hp]
    rfl

theorem compile_count (t : ℕ) (imm : Fin I → Fin W) (bits : Fin t → Fin W)
    (start : BooleanNetwork W (F t)) :
    (compile F step t imm bits start).net.count =
      start.net.count + ∑ r : Fin t, (step r.val).net.count := by
  induction t with
  | zero => simp [compile]
  | succ t ih =>
    rw [compile, ih, BooleanNetwork.count_comp, BooleanNetwork.count_pair, BooleanNetwork.count_select,
      Fin.sum_univ_castSucc]
    simp [Nat.add_assoc, Nat.add_comm]

/-- The complete verifier initializes on the immutable input, consumes its
guess bits, and reads out the last frame together with the immutable input. -/
def verifier (t : ℕ) (start : BooleanNetwork I (F t)) (readout : BooleanNetwork (I+F 0) O) :
    BooleanNetwork (I+t) O :=
  let imm := BooleanNetwork.select (Fin.castAdd t : Fin I → Fin (I+t))
  let c := compile F step t (Fin.castAdd t) (Fin.natAdd I) (imm.comp start)
  (imm.pair c).comp readout

theorem verifier_eval (t : ℕ) (start : BooleanNetwork I (F t)) (readout : BooleanNetwork (I+F 0) O)
    (imm : Fin I → Bool) (bits : Fin t → Bool) :
    (verifier F step t start readout).eval (Fin.append imm bits) =
      readout.eval (Fin.append imm (run F (tickEval F step) imm t bits (start.eval imm))) := by
  have hl : Fin.append imm bits ∘ Fin.castAdd t = imm := by funext i; simp
  have hr : Fin.append imm bits ∘ Fin.natAdd I = bits := by funext i; simp
  simp only [verifier, BooleanNetwork.eval_comp, BooleanNetwork.eval_pair, BooleanNetwork.eval_select,
    compile_eval, hl, hr]

theorem verifier_count (t : ℕ) (start : BooleanNetwork I (F t)) (readout : BooleanNetwork (I+F 0) O) :
    (verifier F step t start readout).net.count =
      start.net.count + (∑ r : Fin t, (step r.val).net.count) + readout.net.count := by
  simp [verifier, BooleanNetwork.count_comp, BooleanNetwork.count_pair, compile_count]

theorem verifier_count_le (t : ℕ) (start : BooleanNetwork I (F t)) (readout : BooleanNetwork (I+F 0) O)
    (B : ℕ) (hb : ∀ r < t, (step r).net.count ≤ B) :
    (verifier F step t start readout).net.count ≤ start.net.count + t*B + readout.net.count := by
  rw [verifier_count]
  have h : (∑ r : Fin t, (step r.val).net.count) ≤ ∑ _ : Fin t, B :=
    Finset.sum_le_sum fun i _ => hb i i.isLt
  exact Nat.add_le_add_right (Nat.add_le_add_left (by simpa using h) start.net.count) readout.net.count

end SignedFrame

end SpectralBooks
end LinearAlgebra
end OAI
