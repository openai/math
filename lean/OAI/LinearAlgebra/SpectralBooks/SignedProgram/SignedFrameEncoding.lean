import OAI.LinearAlgebra.SpectralBooks.SignedProgram.SignedTapeWindow
import OAI.Computability.QuantumFactoring.BooleanVector

/-! # Boolean wires for a signed-machine frame

The control has a wire for each halt value and each program state. Each
tape cell has one wire for each of the three possible symbols. The input
tape is indexed by `none` and the work tapes by `some`.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

namespace SignedProgram

open SignedMachine ExactQuantumFactoring

local instance : Fintype Output := ⟨{.zero, .pos, .neg}, by intro o; cases o <;> simp⟩
local instance : Fintype Symbol := ⟨{.blank, .zero, .one}, by intro s; cases s <;> simp⟩

/-- Control and tape-cell indicator wires in a frame of radius `r`. -/
abbrev FrameWire (n r : ℕ) := (Output ⊕ Fin (n+1)) ⊕ (Option (Fin n) × Cell r × Symbol)

instance instFintypeFrameWire (n r : ℕ) : Fintype (FrameWire n r) :=
  inferInstanceAs (Fintype ((Output ⊕ Fin (n+1)) ⊕ (Option (Fin n) × Cell r × Symbol)))

/-- The number of tests stored in the encoded frame. -/
theorem frameWire_card (n r : ℕ) :
    Fintype.card (FrameWire n r) = 3 + (n+1) + (n+1) * ((2*r+1)*3) := by
  have ho : Fintype.card Output = 3 := by decide
  have hs : Fintype.card Symbol = 3 := by decide
  simp [FrameWire, Cell, ho, hs]

/-- Read one control or tape test. A state beyond the bounded program range
has no active state wire. -/
def Frame.encode {n r : ℕ} (f : Frame n r) : FrameWire n r → Bool
  | .inl (.inl o) => decide (f.control = .inl o)
  | .inl (.inr q) => decide (f.control = .inr q.val)
  | .inr (t, i, s) => decide (f.cells t i = s)

/-- The same encoding indexed by the physical wire number. -/
noncomputable def Frame.encodeBits {n r : ℕ} (f : Frame n r) :
    Fin (Fintype.card (FrameWire n r)) → Bool :=
  f.encode ∘ (Fintype.equivFin (FrameWire n r)).symm

@[simp] theorem Frame.encodeBits_wire {n r : ℕ} (f : Frame n r) (w : FrameWire n r) :
    f.encodeBits (Fintype.equivFin _ w) = f.encode w := by simp [Frame.encodeBits]

/-- A static read selects an existing wire in a packed frame. -/
noncomputable def frameRead {n r : ℕ} (w : FrameWire n r) :
    BooleanNetwork (Fintype.card (FrameWire n r)) 1 :=
  .bit (Fintype.equivFin _ w)

@[simp] theorem frameRead_eval {n r : ℕ} (w : FrameWire n r) (f : Frame n r) :
    (frameRead w).eval f.encodeBits 0 = f.encode w := by simp [frameRead]

@[simp] theorem frameRead_count {n r : ℕ} (w : FrameWire n r) :
    (frameRead w).net.count = 0 := rfl

/-- Pack one Boolean network per frame wire into a single multi-output network. -/
noncomputable def framePack {a n r : ℕ} (g : FrameWire n r → BooleanNetwork a 1) :
    BooleanNetwork a (Fintype.card (FrameWire n r)) :=
  .vector (fun i => g ((Fintype.equivFin (FrameWire n r)).symm i))

@[simp] theorem framePack_eval {a n r : ℕ} (g : FrameWire n r → BooleanNetwork a 1)
    (x : Fin a → Bool) (w : FrameWire n r) :
    (framePack g).eval x (Fintype.equivFin _ w) = (g w).eval x 0 := by simp [framePack]

theorem framePack_eval_encodeBits {a n r : ℕ} (g : FrameWire n r → BooleanNetwork a 1)
    (x : Fin a → Bool) (f : Frame n r) (hg : ∀ w, (g w).eval x 0 = f.encode w) :
    (framePack g).eval x = f.encodeBits := by
  funext i
  obtain ⟨w, rfl⟩ := (Fintype.equivFin (FrameWire n r)).surjective i
  rw [framePack_eval, Frame.encodeBits_wire, hg]

theorem framePack_count {a n r C : ℕ} (g : FrameWire n r → BooleanNetwork a 1)
    (h : ∀ w, (g w).net.count ≤ C) :
    (framePack g).net.count ≤ Fintype.card (FrameWire n r) * C :=
  BooleanNetwork.count_vector_le _ fun _ => h _

/-- An initial-row cell reads a fixed input literal, or a constant for a
blank or out-of-range position. -/
private def initialCellCircuit {n : ℕ} (z : ℤ) (s : Symbol) : BooleanNetwork n 1 :=
  if hz : 0 ≤ z ∧ z.toNat < n then
    match s with
    | .blank => .constant false
    | .zero => (BooleanNetwork.bit ⟨z.toNat, hz.2⟩).bnot
    | .one => .bit ⟨z.toNat, hz.2⟩
  else .constant (decide (Symbol.blank = s))

private theorem initialCellCircuit_eval {n : ℕ} (x : Fin n → Bool) (z : ℤ) (s : Symbol) :
    (initialCellCircuit (n := n) z s).eval x 0 = decide (initialSymbol x z = s) := by
  by_cases hz : 0 ≤ z ∧ z.toNat < n
  · cases s <;> cases h : x ⟨z.toNat, hz.2⟩ <;> simp [initialCellCircuit, initialSymbol, hz, h]
  · simp [initialCellCircuit, initialSymbol, hz]

private theorem initialCellCircuit_count {n : ℕ} (z : ℤ) (s : Symbol) :
    (initialCellCircuit (n := n) z s).net.count ≤ 1 := by
  by_cases hz : 0 ≤ z ∧ z.toNat < n
  · have heq : initialCellCircuit (n := n) z s =
        (match s with
         | .blank => .constant false
         | .zero => (BooleanNetwork.bit ⟨z.toNat, hz.2⟩).bnot
         | .one => .bit ⟨z.toNat, hz.2⟩) := dite_eq_left hz
    rw [heq]
    cases s <;> simp
  · have heq : initialCellCircuit (n := n) z s = .constant (decide (Symbol.blank = s)) := dite_eq_right hz
    rw [heq]
    simp

private def initialWireCircuit {n r : ℕ} : FrameWire n r → BooleanNetwork n 1
  | .inl (.inl _) => .constant false
  | .inl (.inr q) => .constant (decide (0 = q.val))
  | .inr (none, i, s) => initialCellCircuit i.position s
  | .inr (some _, _, s) => .constant (decide (Symbol.blank = s))

/-- Circuit filling the whole radius-`r` initial tableau row from the public input. -/
noncomputable def initialFrameCircuit (n r : ℕ) :
    BooleanNetwork n (Fintype.card (FrameWire n r)) :=
  framePack initialWireCircuit

theorem initialFrameCircuit_eval (n r : ℕ) (x : Fin n → Bool) :
    (initialFrameCircuit n r).eval x = (Frame.initial (r := r) x).encodeBits := by
  funext i
  obtain ⟨w, rfl⟩ := (Fintype.equivFin (FrameWire n r)).surjective i
  rw [initialFrameCircuit, framePack_eval, Frame.encodeBits_wire]
  rcases w with (o | q) | ⟨(_ | j), i, s⟩ <;>
    simp [Frame.encode, Frame.initial, initialWireCircuit, initialCellCircuit_eval] <;> rfl

theorem initialFrameCircuit_count (n r : ℕ) :
    (initialFrameCircuit n r).net.count ≤ Fintype.card (FrameWire n r) := by
  apply (framePack_count (C := 1) _ ?_).trans (Nat.mul_one _).le
  rintro ((o | q) | ⟨(_ | j), i, s⟩) <;> simp [initialWireCircuit, initialCellCircuit_count]

end SignedProgram

end SpectralBooks
end LinearAlgebra
end OAI
