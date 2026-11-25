import OAI.Computability.BorderVNP.DiagonalResidueRAM

/-!
# Semantics of the three-word gate records

A gate appended at the next fresh address preserves all preceding inputs and
wires. The initial memory may carry unrelated data outside the valuation bank.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace DiagonalResidueRAM

open VPVNP VPVNP.BooleanTranscript VPVNP.BurstRAM VPVNP.BurstRAM.PrivateRAM

variable {w u v : ℕ}

/-- Word encoding of a bit on the external RAM. -/
def wordBit (w : ℕ) (b : Bool) : Word w := Fin.ofNat _ b.toNat

/-- A canonical bit has its own natural representative at every positive width. -/
theorem wordBit_val (hw : 1 < 2^w) (b : Bool) : (wordBit w b).val = b.toNat := by
  cases b <;> simp [wordBit, Nat.mod_eq_of_lt hw]

/-- The raw word arithmetic executed by one row. -/
def Row.value (r : Row) (m : Memory w) : Word w :=
  BinaryOp.bitXor.eval (BinaryOp.bitAnd.eval (m r.left) (m r.right)) (wordBit w r.invert)

private theorem bit_ops (hw : 1 < 2^w) (x y z : Bool) :
    BinaryOp.bitXor.eval (BinaryOp.bitAnd.eval (wordBit w x) (wordBit w y)) (wordBit w z) =
      wordBit w (Bool.xor (x && y) z) := by
  cases x <;> cases y <;> cases z <;>
    simp [BinaryOp.eval, wordBit, Nat.mod_eq_of_lt hw]

/-- The input and already materialized gate registers agree with the designated valuation. -/
def Knows {k : ℕ} (base : ℕ) (x : Fin u → Bool) (y : Fin v → Bool)
    (g : Fin k → Bool) (m : Memory w) : Prop :=
  ∀ r : Ref Bool (Fin u ⊕ Fin v) k,
    m (address base r) = wordBit w (r.read id (Sum.elim x y) g)

/-- All possible sources for a gate precede its destination. -/
theorem address_lt {k : ℕ} (base : ℕ) (r : Ref Bool (Fin u ⊕ Fin v) k) :
    address base r < gateBase base u v + k := by
  cases r with
  | const b => cases b <;> simp [address, gateBase] <;> omega
  | var i => cases i <;> simp [address, gateBase] <;> omega
  | gate i => simp [address]

/-- Evaluating two loads and the Boolean word operations computes the specified gate. -/
theorem gateRow_value {k base : ℕ} (hw : 1 < 2^w) {x : Fin u → Bool} {y : Fin v → Bool}
    {g : Fin k → Bool} {m : Memory w} (h : Knows base x y g m) (r : Gate (Fin u ⊕ Fin v) k) :
    (gateRow base r).value m = wordBit w (r.eval (Sum.elim x y) g) := by
  cases r with
  | and a b =>
    simp only [gateRow, Row.value, h a, h b, bit_ops hw, Bool.xor_false, Gate.eval]
  | not a =>
    simp only [gateRow, Row.value, h a, bit_ops hw, Bool.and_self, Bool.xor_true, Gate.eval]

/-- Writing the new gate bit extends the semantic invariant to its snoc. -/
theorem knows_snoc {k base : ℕ} (hw : 1 < 2^w) {x : Fin u → Bool} {y : Fin v → Bool}
    {g : Fin k → Bool} {m : Memory w} (h : Knows base x y g m) (r : Gate (Fin u ⊕ Fin v) k) :
    Knows base x y (Fin.snoc g (r.eval (Sum.elim x y) g))
      (Function.update m (gateBase base u v + k) ((gateRow base r).value m)) := by
  intro source
  cases source with
  | const b =>
    have hne : base + b.toNat ≠ gateBase base u v + k := (address_lt base (.const b : Ref Bool (Fin u ⊕ Fin v) k)).ne
    rw [address, Function.update_of_ne hne]
    exact h (.const b)
  | var i =>
    cases i with
    | inl i =>
      have hne : base + 2 + i.val ≠ gateBase base u v + k :=
        (address_lt base (.var (.inl i) : Ref Bool (Fin u ⊕ Fin v) k)).ne
      rw [address, Function.update_of_ne hne]
      exact h (.var (.inl i))
    | inr i =>
      have hne : base + 2 + u + i.val ≠ gateBase base u v + k :=
        (address_lt base (.var (.inr i) : Ref Bool (Fin u ⊕ Fin v) k)).ne
      rw [address, Function.update_of_ne hne]
      exact h (.var (.inr i))
  | gate i =>
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp [address, Ref.read, gateRow_value hw h]
    · have hne : gateBase base u v + j.val ≠ gateBase base u v + k := by omega
      simp only [address, Fin.val_castSucc, Ref.read, Fin.snoc_castSucc, Function.update_of_ne hne]
      exact h (.gate j)

/-- Gate evaluation in physical memory, in increasing gate order. -/
def executeGates (base : ℕ) (m : Memory w) : {k : ℕ} → Program (Fin u ⊕ Fin v) k → Memory w
  | _, .nil => m
  | k+1, .snoc p r =>
    let prev := executeGates base m p
    Function.update prev (gateBase base u v + k) ((gateRow base r).value prev)

/-- At the end of the row scan the designated output is its Boolean circuit value. -/
theorem executeGates_correct {base : ℕ} (hw : 1 < 2^w) {x : Fin u → Bool} {y : Fin v → Bool}
    {m : Memory w} (h : Knows base x y Fin.elim0 m) {k : ℕ} (p : Program (Fin u ⊕ Fin v) k) :
    Knows base x y (p.run (Sum.elim x y)) (executeGates base m p) := by
  induction p with
  | nil => exact h
  | snoc p r ih => exact knows_snoc hw ih r

/-- Word-level projection to the verifier's final bit after shared-gate evaluation. -/
theorem read_output {base : ℕ} (hw : 1 < 2^w) {x : Fin u → Bool} {y : Fin v → Bool}
    {m : Memory w} (h : Knows base x y Fin.elim0 m) {k : ℕ} (c : Circuit (Fin u ⊕ Fin v) k) :
    executeGates base m c.program (address base c.output) = wordBit w (c.eval (Sum.elim x y)) :=
  executeGates_correct hw h c.program c.output

end DiagonalResidueRAM

end BorderVNP
end Computability
end OAI
