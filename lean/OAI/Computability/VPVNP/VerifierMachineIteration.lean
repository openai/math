import OAI.Computability.VPVNP.VerifierMachineRegisters
import OAI.Computability.VPVNP.VerifierMachineNetwork

/-!
# Iterating the universal verifier on its bounded tape window

One circuit layer consumes the next choice bit and computes the next configuration.
The decoded table and the input and choice bits remain accessible by wire references
at every layer. After exactly `T` layers the circuit tests validity and the accepting state.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace VerifierMachineIteration

open UniversalMachine VerifierMachineDecode
open VerifierNetwork (Frame)
open BinPackingGames.Foundations.Complexity.CookLevin.StatementCircuit

/-- Inputs and choices, decoded table flags, and configuration registers for a radius-`r` window. -/
abbrev Slice (n T r : ℕ) := (Fin n ⊕ Fin T) ⊕ (DecoderWire n ⊕ WindowRegister n r)

theorem card_slice (n T r : ℕ) : Fintype.card (Slice n T r) =
    n + T + (2 + 9 * n * 2 * (n + 2) * 81 + (n + 2 + 2 * ((2 * r + 1) * 3))) := by
  simp [Slice, decoderWire_card, WindowRegister, WindowCell, UniversalMachine.Symbol]

variable {n T r : ℕ} {σ : Type*} [Fintype σ]

private def choiceAt (t : ℕ) : Expr (Slice n T r) :=
  if h : t < T then .input (.inl (.inr ⟨t, h⟩)) else .const false

private def slotWire (i : Fin (9 * n)) (b : Bool) (k : InstructionKey n) : Expr (Slice n T r) :=
  .input (.inr (.inl (.slot i b k)))

private def regWire (j : WindowRegister n r) : Expr (Slice n T r) := .input (.inr (.inr j))

private noncomputable def layer (t : ℕ) : Slice n T r → Expr (Slice n T r)
  | .inl i => .input (.inl i)
  | .inr (.inl d) => .input (.inr (.inl d))
  | .inr (.inr j) => registerStepExpr slotWire regWire (choiceAt t) j

/-- Append exactly one Boolean circuit layer per choice bit, in order. -/
noncomputable def simulate (f : Frame σ (Slice n T r)) : Frame σ (Slice n T r) := f.steps layer T

private theorem steps_eval_input (f : Frame σ (Slice n T r)) (input : σ → Bool)
    (i : Fin n ⊕ Fin T) (t : ℕ) : (f.steps layer t).eval input (.inl i) = f.eval input (.inl i) := by
  induction t with
  | zero => rfl
  | succ t ih => simpa [Frame.steps_succ, layer, Expr.eval] using ih

private theorem steps_eval_decoder (f : Frame σ (Slice n T r)) (input : σ → Bool)
    (d : DecoderWire n) (t : ℕ) :
    (f.steps layer t).eval input (.inr (.inl d)) = f.eval input (.inr (.inl d)) := by
  induction t with
  | zero => rfl
  | succ t ih => simpa [Frame.steps_succ, layer, Expr.eval] using ih

/-- All bounded configuration bits after `T` layers encode the run on the supplied choices. -/
theorem simulate_eval_register (f : Frame σ (Slice n T r)) (input : σ → Bool)
    (p : UniversalMachine.Program) (hp : p.extra ≤ n) (c : WindowConfig p.extra r) (w : Fin T → Bool)
    (hslots : ∀ i b k, f.eval input (.inr (.inl (.slot i b k))) = true ↔
      wireHolds p (.slot i b k))
    (hreg : ∀ j, f.eval input (.inr (.inr j)) = registerEncoding c j)
    (hw : ∀ i, f.eval input (.inl (.inr i)) = w i) (j : WindowRegister n r) :
    (simulate f).eval input (.inr (.inr j)) = registerEncoding (windowRun p c (List.ofFn w)) j := by
  have run (t : ℕ) (ht : t ≤ T) (a : WindowRegister n r) :
      (f.steps layer t).eval input (.inr (.inr a)) =
        registerEncoding (windowRun p c ((List.ofFn w).take t)) a := by
    induction t generalizing a with
    | zero => simpa [windowRun] using hreg a
    | succ t ih =>
      have hlt : t < T := ht
      have hlen : t < (List.ofFn w).length := by simpa using hlt
      rw [Frame.steps_succ, Frame.step_eval, List.take_succ_eq_append_getElem hlen]
      simp only [layer, windowRun, List.foldl_append, List.foldl_cons, List.foldl_nil, List.getElem_ofFn]
      refine registerStepExpr_eval _ _ _ _ p hp _ _ ?_ ?_ ?_ a
      · intro i b k
        simpa only [slotWire, Expr.eval, steps_eval_decoder] using hslots i b k
      · intro i
        exact ih (by omega) i
      · simpa [choiceAt, hlt, Expr.eval, steps_eval_input] using hw ⟨t, hlt⟩
  have hfull : (List.ofFn w).take T = List.ofFn w := List.take_of_length_le (by simp)
  simpa only [simulate, hfull] using run T le_rfl j

private def acceptanceBit : Fin (n + 2) := ⟨1, by omega⟩

private def outputExpr (_ : Unit) : Expr (Slice n T r) :=
  .and (.input (.inr (.inl .valid))) (.input (.inr (.inr (.inl acceptanceBit))))

/-- Circuit output after executing the entire witness and checking that its table was valid. -/
noncomputable def accept (f : Frame σ (Slice n T r)) : Frame σ Unit := (simulate f).step outputExpr

theorem accept_eval_invalid (f : Frame σ (Slice n T r)) (input : σ → Bool)
    (hv : f.eval input (.inr (.inl .valid)) = false) : (accept f).eval input () = false := by
  simp [accept, outputExpr, Expr.eval, simulate, steps_eval_decoder, hv]

theorem accept_eval_valid (f : Frame σ (Slice n T r)) (input : σ → Bool)
    (p : UniversalMachine.Program) (hp : p.extra ≤ n) (c : WindowConfig p.extra r) (w : Fin T → Bool)
    (hv : f.eval input (.inr (.inl .valid)) = true)
    (hslots : ∀ i b k, f.eval input (.inr (.inl (.slot i b k))) = true ↔
      wireHolds p (.slot i b k))
    (hreg : ∀ j, f.eval input (.inr (.inr j)) = registerEncoding c j)
    (hw : ∀ i, f.eval input (.inl (.inr i)) = w i) :
    (accept f).eval input () = decide ((windowRun p c (List.ofFn w)).state.val = 1) := by
  have hv' : (simulate f).eval input (.inr (.inl .valid)) = true :=
    (steps_eval_decoder f input .valid T).trans hv
  simp only [accept, Frame.step_eval, outputExpr, Expr.eval, hv', Bool.true_and]
  exact simulate_eval_register f input p hp c w hslots hreg hw (.inl acceptanceBit)

private theorem layer_size_le (t : ℕ) (a : Slice n T r) :
    (layer t a).size ≤ 1000000 * (n + 2) ^ 2 := by
  rcases a with i | d | j
  · change 1 ≤ 1000000 * (n + 2) ^ 2
    exact Nat.succ_le_of_lt (by positivity)
  · change 1 ≤ 1000000 * (n + 2) ^ 2
    exact Nat.succ_le_of_lt (by positivity)
  · have hc : (choiceAt (n := n) (T := T) (r := r) t).size ≤ 1 := by
      unfold choiceAt
      split <;> rfl
    have h := registerStepExpr_size_le slotWire regWire (choiceAt (T := T) t) 1
      (fun _ _ _ => le_rfl) (fun _ => le_rfl) hc j
    calc
      (layer t (.inr (.inr j))).size ≤ _ := h
      _ = _ := by ring

/-- The simulation has a fixed width, and the output test uses three more circuit nodes. -/
theorem accept_size_le (f : Frame σ (Slice n T r)) :
    (accept f).size ≤ f.size + T * (Fintype.card (Slice n T r) * (1000000 * (n + 2) ^ 2)) + 3 := by
  have hs := Frame.steps_size_le f layer T (1000000 * (n + 2) ^ 2)
    (fun t _ a => layer_size_le t a)
  have ho := Frame.step_size_le (simulate f) outputExpr 3 (fun _ => le_rfl)
  simp only [Fintype.card_unit, Nat.one_mul] at ho
  exact ho.trans (Nat.add_le_add_right hs 3)

end VerifierMachineIteration

end VPVNP
end Computability
end OAI
