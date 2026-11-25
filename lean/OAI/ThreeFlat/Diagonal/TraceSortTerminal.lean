import OAI.ThreeFlat.Diagonal.TraceSortStages
import OAI.ThreeFlat.Diagonal.TraceSlotAdjacent

namespace OAI
/-! # Sorted-memory checks at the end of one two-track site -/

namespace ThreeFlat.Diagonal.TraceSortSite

open Computability.VPVNP.BurstRAM Computability.VPVNP.RAMSerialization Computability.VPVNP.RAMMemory
open Computability.VPVNP.VerifierNetwork (Frame)
open BinPackingGames.Foundations.Complexity.CookLevin.StatementCircuit (Expr)
open TraceAdjacent

variable {w : ℕ} {σ : Type*}

def pairExpr (a b : SlotAddr w σ) : Expr σ :=
  check (addressed (slices a b))

private theorem pairExpr_eval (hw : 2 ≤ w) (x : σ → Bool) (a b : SlotAddr w σ)
    (u v : Narrow w) (ha : ReadSlot hw x a u) (hb : ReadSlot hw x b v) :
    (pairExpr a b).eval x = true ↔ PaddedCheck (u.map WordRecord.record) [v.map WordRecord.record] :=
  check_iff_padded hw _ x u v (represents_slices hw x u v
    (fun f j => .input (a f j)) (fun f j => .input (b f j)) ha hb)

theorem pairExpr_size (a b : SlotAddr w σ) : (pairExpr a b).size ≤ 50*w+11 :=
  check_size _ (fun _ => by rfl) (fun _ => by rfl) (fun _ => by rfl) (fun _ => by rfl)
    (fun _ => by rfl)

def externalPins (p : SlotAddr w σ) : SlotAddr w (σ ⊕ Live w) := fun f j => .inl (p f j)

def finishExpr (previous outgoing : SlotAddr w σ) (hasNext : Bool) : Expr (σ ⊕ Live w) :=
  (.input (.inr (.inr ())) : Expr _).and
    ((pairExpr (externalPins previous) (ownAddr 0)).and
      ((pairExpr (ownAddr 0) (ownAddr 1)).and
        (if hasNext then eqPort (externalPins outgoing) (ownAddr 1) else .const true)))

/-- Finish both sorted wires and check the outgoing copy of the second slot
whenever another site follows. -/
noncomputable def finish [Fintype σ] (frame : Frame σ (Live w))
    (previous outgoing : SlotAddr w σ) (hasNext : Bool) : Frame σ Unit :=
  frame.withInput.step (fun _ => finishExpr previous outgoing hasNext)

theorem finish_eval [Fintype σ] (hw : 2 ≤ w) (frame : Frame σ (Live w))
    (previous outgoing : SlotAddr w σ) (hasNext : Bool) (x : σ → Bool)
    (prev next : Narrow w) (cur : Fin 2 → Narrow w)
    (hc : ReadLive hw (frame.eval x) cur) (hp : ReadSlot hw x previous prev)
    (hn : ReadSlot hw x outgoing next) :
    ((finish frame previous outgoing hasNext).circuit ()).eval x = true ↔
      frame.eval x (.inr ()) = true ∧
      PaddedCheck (prev.map WordRecord.record) (List.ofFn fun i => (cur i).map WordRecord.record) ∧
      (hasNext = true → next = cur 1) := by
  let y := frame.withInput.eval x
  have ho (i : Fin 2) : ReadSlot hw y (ownAddr i) (cur i) := by
    intro f j; simpa [y, ownAddr] using hc i f j
  have ext (q : SlotAddr w σ) (v : Narrow w) (hq : ReadSlot hw x q v) :
      ReadSlot hw y (externalPins q) v := by
    intro f j; simpa [y, externalPins] using hq f j
  have pairs := pairExpr_eval hw y _ _ _ _ (ext _ _ hp) (ho 0)
  have own := pairExpr_eval hw y _ _ _ _ (ho 0) (ho 1)
  have send := eqPort_eval hw y _ _ _ _ (ext _ _ hn) (ho 1)
  have two : (List.ofFn fun i : Fin 2 => (cur i).map WordRecord.record) =
      [(cur 0).map WordRecord.record, (cur 1).map WordRecord.record] := by
    simp [List.ofFn_succ]
  simp only [finish, Frame.circuit_eval, Frame.step_eval, finishExpr, Expr.eval, Bool.and_eq_true,
    Frame.withInput_eval_inr]
  rw [two, paddedCheck_cons]
  cases hasNext <;> simp only [y, pairs, own, send, ite_true, ite_false,
    Bool.false_eq_true, false_implies, true_implies, Expr.eval, and_true, and_assoc]

theorem finish_size [Fintype σ] (frame : Frame σ (Live w)) (previous outgoing : SlotAddr w σ)
    (hasNext : Bool) :
    (finish frame previous outgoing hasNext).size ≤ frame.size + 184*(w+1) := by
  have h₀ := pairExpr_size (externalPins previous) (ownAddr 0)
  have h₁ := pairExpr_size (ownAddr (σ := σ) (w := w) 0) (ownAddr 1)
  have hs := eqPort_size (externalPins outgoing) (ownAddr 1)
  have e : (finishExpr previous outgoing hasNext).size ≤ 184*(w+1) := by
    cases hasNext <;> simp only [finishExpr, ite_true, ite_false, Bool.false_eq_true, Expr.size]
      <;> omega
  simpa [finish] using frame.withInput.step_size_le (fun _ : Unit => finishExpr previous outgoing hasNext)
    (184*(w+1)) (fun _ => e)

theorem finish_circuitSize [Fintype σ] (frame : Frame σ (Live w)) (previous outgoing : SlotAddr w σ)
    (hasNext : Bool) :
    (finish frame previous outgoing hasNext).circuitSize () ≤ 4*(frame.size + 184*(w+1)) :=
  ((finish frame previous outgoing hasNext).circuitSize_le ()).trans
    (Nat.mul_le_mul_left _ (finish_size frame previous outgoing hasNext))

end ThreeFlat.Diagonal.TraceSortSite

end OAI
