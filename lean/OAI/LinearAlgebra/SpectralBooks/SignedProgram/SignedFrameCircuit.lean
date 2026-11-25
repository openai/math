import OAI.LinearAlgebra.SpectralBooks.SignedProgram.SignedFrameEncoding
import OAI.LinearAlgebra.SpectralBooks.SignedProgram.SignedCellCircuit
import OAI.LinearAlgebra.SpectralBooks.SignedProgram.SignedFrameStep
import OAI.LinearAlgebra.SpectralBooks.SignedProgram.SignedProgramActionBits

/-! # Boolean circuit for one complete signed-machine tableau row

The table lookup uses the old control state and tape heads. Each candidate
transition computes one requested bit of the narrower row, and the priority
lookup selects the first matching instruction. An unmatched rule or a one
bit on a forced tick halts the run with zero. A halted run accepts only
subsequent zero padding.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

noncomputable section

namespace SignedProgram

open SignedMachine ExactQuantumFactoring ExactQuantumFactoring.BooleanNetwork
variable {a n r : ℕ}

private def haltBit (o : Output) (w : FrameWire n r) : BooleanNetwork a 1 :=
  constant ((Frame.halted n r o).encode w)

private def moveBit (prev : FrameWire n (r+1) → BooleanNetwork a 1)
    (W : LookupSignals n a) (A : ActionSignals n a) (j : Fin n) (p : Bool)
    (w : FrameWire n r) : BooleanNetwork a 1 :=
  match w with
  | .inl (.inl _) => constant false
  | .inl (.inr state) => A.state j p state
  | .inr (t,i,s) => cellUpdateNet (fun t k s => prev (.inr (t,k,s)))
      (A.inputMove j p) (A.workMove j p) (A.workWrite j p) W.tapeActive t i s

private def rowBit (prev : FrameWire n (r+1) → BooleanNetwork a 1)
    (W : LookupSignals n a) (A : ActionSignals n a) (choice : BooleanNetwork a 1)
    (j : Fin n) (w : FrameWire n r) : BooleanNetwork a 1 :=
  let immediate := mux (A.out j .zero) (haltBit .zero w)
    (mux (A.out j .pos) (haltBit .pos w) (haltBit .neg w))
  let d := moveBit prev W A j false w
  let b := moveBit prev W A j true w
  mux (A.kind j 0) (mux choice (haltBit .zero w) immediate)
    (mux (A.kind j 1) (mux choice (haltBit .zero w) d) (mux choice b d))

/-- A circuit for one requested output bit of a machine tick, including
previously halted configurations and a missing table row. -/
def frameTickBit (prev : FrameWire n (r+1) → BooleanNetwork a 1)
    (W : LookupSignals n a) (A : ActionSignals n a) (choice : BooleanNetwork a 1)
    (w : FrameWire n r) : BooleanNetwork a 1 :=
  mux (prev (.inl (.inl .zero))) (haltBit .zero w) <|
    mux (prev (.inl (.inl .pos))) (mux choice (haltBit .zero w) (haltBit .pos w)) <|
      mux (prev (.inl (.inl .neg))) (mux choice (haltBit .zero w) (haltBit .neg w))
        (lookupBitNet W (fun j => rowBit prev W A choice j w) ((Frame.halted n r .zero).encode w))

/-- The complete new row is collected in the same one-hot wire format as
the preceding configuration. -/
def frameStepNet (prev : FrameWire n (r+1) → BooleanNetwork a 1)
    (W : LookupSignals n a) (A : ActionSignals n a) (choice : BooleanNetwork a 1) :
    BooleanNetwork a (Fintype.card (FrameWire n r)) :=
  framePack (frameTickBit prev W A choice)

/-- Soundness of the state/head key tests is needed only when the old
configuration is running. The encoded program contains bounded states. -/
def Frame.lookupAgrees (f : Frame n (r+1)) (t : Table n) (x : Fin a → Bool)
    (W : LookupSignals n a) : Prop :=
  ∀ q, f.control = .inr q → ∃ hq : q < n+1,
    W.Agrees x t ⟨q,hq⟩ (f.cells none (Cell.center (r+1)))
      (fun j => f.cells (some j) (Cell.center (r+1)))

private theorem moveBit_eval (prev : FrameWire n (r+1) → BooleanNetwork a 1)
    (W : LookupSignals n a) (A : ActionSignals n a) (x : Fin a → Bool) (t : Table n)
    (f : Frame n (r+1)) (ha : A.Agrees x t)
    (hp : ∀ w, (prev w).eval x 0 = f.encode w)
    (ht : ∀ j, (W.tapeActive j).eval x 0 = decide (j.val < t.tapes.val))
    (j : Fin n) (p : Bool) (w : FrameWire n r) :
    (moveBit prev W A j p w).eval x 0 =
      (f.advance (((t.row j).next p).transition t.tapes)).encode w := by
  rcases w with (o | state) | ⟨tape,i,s⟩
  · simp [moveBit, Frame.encode, Frame.advance]
  · simp [moveBit, Frame.encode, Frame.advance, Move.transition, ha.state, Fin.ext_iff]
  · exact eval_cellUpdateNet _ _ _ _ _ x f ((t.row j).next p) t.tapes
      (fun t k s => hp (.inr (t,k,s)))
      (ha.inputMove j p) (ha.workMove j p) (ha.workWrite j p) ht tape i s

private theorem rowBit_eval (prev : FrameWire n (r+1) → BooleanNetwork a 1)
    (W : LookupSignals n a) (A : ActionSignals n a) (choice : BooleanNetwork a 1)
    (x : Fin a → Bool) (t : Table n) (f : Frame n (r+1)) (ha : A.Agrees x t)
    (hp : ∀ w, (prev w).eval x 0 = f.encode w)
    (ht : ∀ j, (W.tapeActive j).eval x 0 = decide (j.val < t.tapes.val))
    (j : Fin n) (w : FrameWire n r) :
    (rowBit prev W A choice j w).eval x 0 =
      (f.applyAction (choice.eval x 0) (some ((t.row j).action t.tapes))).encode w := by
  have hm := moveBit_eval prev W A x t f ha hp ht j
  simp only [rowBit, eval_mux, haltBit, eval_constant, ha.kind, ha.out, hm, Row.action]
  by_cases h₀ : (t.row j).kind = 0
  · cases ho : (t.row j).out <;> cases hc : choice.eval x 0 <;> simp [h₀,Frame.applyAction]
  · by_cases h₁ : (t.row j).kind = 1 <;> cases hc : choice.eval x 0 <;> simp [h₀,h₁,Frame.applyAction]

theorem frameTickBit_eval (prev : FrameWire n (r+1) → BooleanNetwork a 1)
    (W : LookupSignals n a) (A : ActionSignals n a) (choice : BooleanNetwork a 1)
    (x : Fin a → Bool) (t : Table n) (f : Frame n (r+1))
    (ha : A.Agrees x t) (hp : ∀ w, (prev w).eval x 0 = f.encode w)
    (hw : f.lookupAgrees t x W) (w : FrameWire n r) :
    (frameTickBit prev W A choice w).eval x 0 = (f.tick t (choice.eval x 0)).encode w := by
  cases hctrl : f.control with
  | inl o =>
    cases o <;> cases hb : choice.eval x 0 <;>
      simp [frameTickBit, hp, Frame.encode, hctrl, haltBit, Frame.tick, hb]
  | inr q =>
    obtain ⟨hq, hqa⟩ := hw q hctrl
    let q' : Fin (n+1) := ⟨q,hq⟩
    let u := f.cells none (Cell.center (r+1))
    let v := fun j => f.cells (some j) (Cell.center (r+1))
    have key := firstRow_action t q' u v
    change (f.lookup t q).map Rule.action = _ at key
    have hn (o : Output) : (prev (.inl (.inl o))).eval x 0 = false := by
      rw [hp]
      simp [Frame.encode, hctrl]
    simp only [frameTickBit, eval_mux, hn, Bool.false_eq_true, ite_false, Frame.tick, hctrl, key]
    rw [lookupBitNet_eval _ _ _ _ t q' u v hqa]
    cases firstRow t q' u v with
    | none => simp only [Option.map_none, Option.getD_none, Frame.applyAction]
    | some j =>
      simp only [Option.map_some, Option.getD_some]
      exact rowBit_eval prev W A choice x t f ha hp hqa.tape j w

/-- Bitwise correctness for all three symbol codes, every state code and every
halting result of the complete successor row. -/
theorem frameStepNet_eval (prev : FrameWire n (r+1) → BooleanNetwork a 1)
    (W : LookupSignals n a) (A : ActionSignals n a) (choice : BooleanNetwork a 1)
    (x : Fin a → Bool) (t : Table n) (f : Frame n (r+1))
    (ha : A.Agrees x t) (hp : ∀ w, (prev w).eval x 0 = f.encode w)
    (hw : f.lookupAgrees t x W) (w : FrameWire n r) :
    (frameStepNet prev W A choice).eval x ((Fintype.equivFin (FrameWire n r)) w) =
      (f.tick t (choice.eval x 0)).encode w := by
  rw [frameStepNet, framePack_eval]
  exact frameTickBit_eval prev W A choice x t f ha hp hw w

/-- Vector form for composing successive rows of the tableau. -/
theorem frameStepNet_eval_encodeBits (prev : FrameWire n (r+1) → BooleanNetwork a 1)
    (W : LookupSignals n a) (A : ActionSignals n a) (choice : BooleanNetwork a 1)
    (x : Fin a → Bool) (t : Table n) (f : Frame n (r+1))
    (ha : A.Agrees x t) (hp : ∀ w, (prev w).eval x 0 = f.encode w)
    (hw : f.lookupAgrees t x W) :
    (frameStepNet prev W A choice).eval x = (f.tick t (choice.eval x 0)).encodeBits := by
  funext i
  obtain ⟨w, rfl⟩ := (Fintype.equivFin _).surjective i
  rw [Frame.encodeBits_wire]
  exact frameStepNet_eval prev W A choice x t f ha hp hw w

private theorem moveBit_count (prev : FrameWire n (r+1) → BooleanNetwork a 1)
    (W : LookupSignals n a) (A : ActionSignals n a) {C : ℕ}
    (hp : ∀ w, (prev w).net.count ≤ C) (hw : W.Bounded C) (ha : A.Bounded C)
    (j : Fin n) (p : Bool) (w : FrameWire n r) :
    (moveBit prev W A j p w).net.count ≤ 24*(C+1) := by
  rcases w with (o | state) | ⟨tape,i,s⟩
  · simp only [moveBit, count_constant]; omega
  · exact (ha.state j p state).trans (by omega)
  · exact count_cellUpdateNet (fun t k s => prev (.inr (t,k,s)))
      (A.inputMove j p) (A.workMove j p) (A.workWrite j p) W.tapeActive C
      (fun t k s => hp (.inr (t,k,s))) (ha.inputMove j p) (ha.workMove j p)
      (ha.workWrite j p) hw.tape tape i s

private theorem rowBit_count (prev : FrameWire n (r+1) → BooleanNetwork a 1)
    (W : LookupSignals n a) (A : ActionSignals n a) (choice : BooleanNetwork a 1) {C : ℕ}
    (hp : ∀ w, (prev w).net.count ≤ C) (hw : W.Bounded C) (ha : A.Bounded C)
    (hc : choice.net.count ≤ C) (j : Fin n) (w : FrameWire n r) :
    (rowBit prev W A choice j w).net.count ≤ 160*(C+1) := by
  have h0 := moveBit_count prev W A hp hw ha j false w
  have h1 := moveBit_count prev W A hp hw ha j true w
  have hk0 := ha.kind j 0
  have hk1 := ha.kind j 1
  have ho0 := ha.out j .zero
  have hop := ha.out j .pos
  simp only [rowBit, count_mux, haltBit, count_constant]
  omega

/-- Explicit gate cost per output bit, including priority search over the table. -/
def frameTickBitBudget (n C : ℕ) : ℕ := lookupBitBudget n C (160*(C+1)) + 60*(C+1)

theorem frameTickBit_count (prev : FrameWire n (r+1) → BooleanNetwork a 1)
    (W : LookupSignals n a) (A : ActionSignals n a) (choice : BooleanNetwork a 1) {C : ℕ}
    (hp : ∀ w, (prev w).net.count ≤ C) (hw : W.Bounded C) (ha : A.Bounded C)
    (hc : choice.net.count ≤ C) (w : FrameWire n r) :
    (frameTickBit prev W A choice w).net.count ≤ frameTickBitBudget n C := by
  have h := lookupBitNet_count W _ ((Frame.halted n r .zero).encode w) hw
    (fun j => rowBit_count prev W A choice hp hw ha hc j w)
  have h0 := hp (.inl (.inl .zero))
  have hpos := hp (.inl (.inl .pos))
  have hneg := hp (.inl (.inl .neg))
  simp only [frameTickBitBudget, frameTickBit, count_mux, haltBit, count_constant]
  omega

/-- A polynomial number of Boolean gates realizes all the new cells and the
control simultaneously whenever its one-bit input tests have bounded size. -/
theorem frameStepNet_count (prev : FrameWire n (r+1) → BooleanNetwork a 1)
    (W : LookupSignals n a) (A : ActionSignals n a) (choice : BooleanNetwork a 1) {C : ℕ}
    (hp : ∀ w, (prev w).net.count ≤ C) (hw : W.Bounded C) (ha : A.Bounded C)
    (hc : choice.net.count ≤ C) :
    (frameStepNet prev W A choice).net.count ≤
      Fintype.card (FrameWire n r) * frameTickBitBudget n C := by
  apply framePack_count
  exact frameTickBit_count prev W A choice hp hw ha hc

end SignedProgram

end

end SpectralBooks
end LinearAlgebra
end OAI
