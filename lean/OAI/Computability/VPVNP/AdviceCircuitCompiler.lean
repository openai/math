import OAI.Computability.VPVNP.AdviceCircuitProgram
import OAI.Computability.VPVNP.BooleanTranscript

/-!
# Translating coefficient verifiers to bit-stack interpreter advice

The initial valuation stack holds zero, one, the query word, and the candidate
witness, in that order. A gate pushes its result, so a reference to an earlier
gate is addressed from the newest gate backwards. Two final NOT instructions
copy the designated output to the top, including for circuits with no gates.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace AdviceCircuit

variable {u w n : ℕ}

/-- Initial valuation in stack order, with false and true followed by the query bits and the
candidate witness bits. -/
def inputs (x : Fin u → Bool) (bits : Fin w → Bool) : List Bool :=
  false :: true :: (List.ofFn x ++ List.ofFn bits)

private def valuation (x : Fin u → Bool) (bits : Fin w → Bool) (gates : Fin n → Bool) :
    List Bool := (List.ofFn gates).reverse ++ inputs x bits

/-- Address in the valuation stack after `n` instructions. -/
def address : Ref Bool (Fin u ⊕ Fin w) n → ℕ
  | .const b => n + b.toNat
  | .var (.inl i) => n + 2 + i.val
  | .var (.inr j) => n + 2 + u + j.val
  | .gate i => n - 1 - i.val

private theorem address_lt (r : Ref Bool (Fin u ⊕ Fin w) n) :
    address r < n + 2 + u + w := by
  cases r with
  | var i => cases i with
    | inl i => dsimp [address]; have := i.isLt; omega
    | inr i => dsimp [address]; have := i.isLt; omega
  | const b => cases b <;> simp [address] <;> omega
  | gate i => dsimp [address]; omega

private theorem read_address (x : Fin u → Bool) (bits : Fin w → Bool) (g : Fin n → Bool)
    (r : Ref Bool (Fin u ⊕ Fin w) n) :
    (valuation x bits g)[address r]? = some (r.read id (Sum.elim x bits) g) := by
  cases r with
  | const b =>
    cases b <;> simp [valuation, address, inputs, Ref.read]
  | var z =>
    cases z with
    | inl i =>
      simp only [valuation, address, Ref.read, Sum.elim_inl]
      rw [show n + 2 + i.val = n + (i.val + 1 + 1) by omega,
        List.getElem?_append_right (by simp)]
      simp [inputs, List.getElem?_append, i.isLt]
    | inr j =>
      simp only [valuation, address, Ref.read, Sum.elim_inr]
      rw [show n + 2 + u + j.val = n + (u + j.val + 1 + 1) by omega,
        List.getElem?_append_right (by simp)]
      simp [inputs]
  | gate i =>
    have hi : n-1-i.val < n := by have := i.isLt; omega
    have hr : n-1-(n-1-i.val) = i.val := by have := i.isLt; omega
    simp [valuation, address, List.getElem?_append, hi, hr, Ref.read]

private def emit : BooleanTranscript.Gate (Fin u ⊕ Fin w) n → Instruction
  | .not a => .not (address a)
  | .and a b => .and (address a) (address b)

private theorem emit_value (x : Fin u → Bool) (bits : Fin w → Bool) (g : Fin n → Bool)
    (a : BooleanTranscript.Gate (Fin u ⊕ Fin w) n) :
    (emit a).value (valuation x bits g) = some (a.eval (Sum.elim x bits) g) := by
  cases a <;> simp [emit, Instruction.value, read_address, BooleanTranscript.Gate.eval]

/-- Compile the gates of a Boolean transcript program into unary-address instructions in gate
order. -/
def instructions : {n : ℕ} → BooleanTranscript.Program (Fin u ⊕ Fin w) n → List Instruction
  | _, .nil => []
  | _, .snoc p g => instructions p ++ [emit g]

private theorem valuation_snoc (x : Fin u → Bool) (bits : Fin w → Bool) (g : Fin n → Bool) (b : Bool) :
    valuation x bits (Fin.snoc g b) = b :: valuation x bits g := by
  simp only [valuation, List.ofFn_succ', Fin.snoc_castSucc, Fin.snoc_last, List.concat_eq_append,
    List.reverse_append, List.reverse_singleton, List.cons_append, List.nil_append]

theorem instructions_run (p : BooleanTranscript.Program (Fin u ⊕ Fin w) n)
    (x : Fin u → Bool) (bits : Fin w → Bool) :
    run (instructions p) (inputs x bits) = some (valuation x bits (p.run (Sum.elim x bits))) := by
  induction p with
  | nil => simp [instructions, valuation]
  | snoc p g ih =>
    simp only [instructions, run_append, ih, Option.bind_some, BooleanTranscript.Program.run,
      valuation_snoc]
    exact run_cons (emit_value x bits _ g)

/-- Compile all gates and copy the designated output to the top. -/
def compile (c : BooleanTranscript.Circuit (Fin u ⊕ Fin w) n) : List Instruction :=
  instructions c.program ++ [.not (address c.output), .not 0]

theorem compile_run (c : BooleanTranscript.Circuit (Fin u ⊕ Fin w) n)
    (x : Fin u → Bool) (bits : Fin w → Bool) :
    ∃ tail, run (compile c) (inputs x bits) = some (c.eval (Sum.elim x bits) :: tail) := by
  let g := c.program.run (Sum.elim x bits)
  let b := c.eval (Sum.elim x bits)
  have first : (Instruction.not (address c.output)).value (valuation x bits g) = some (!b) := by
    simp [Instruction.value, read_address, b, g, BooleanTranscript.Circuit.eval]
  have second : (Instruction.not 0).value ((!b) :: valuation x bits g) = some b := by simp [Instruction.value]
  refine ⟨(!b) :: valuation x bits g, ?_⟩
  rw [compile, run_append, instructions_run, Option.bind_some, run_cons first, run_cons second, run_nil]

@[simp] theorem instructions_length (p : BooleanTranscript.Program (Fin u ⊕ Fin w) n) :
    (instructions p).length = n := by induction p <;> simp_all [instructions]

@[simp] theorem compile_length (c : BooleanTranscript.Circuit (Fin u ⊕ Fin w) n) :
    (compile c).length = n + 2 := by simp [compile]

private theorem emit_length (a : BooleanTranscript.Gate (Fin u ⊕ Fin w) n) :
    (emit a).encode.length ≤ 2*(n+u+w+2)+3 := by
  cases a with
  | not r => have := address_lt r; simp [emit, Instruction.encode, unary]; omega
  | and r s => have := address_lt r; have := address_lt s; simp [emit, Instruction.encode, unary]; omega

private theorem instructions_size (p : BooleanTranscript.Program (Fin u ⊕ Fin w) n) :
    (encode (instructions p)).length ≤ n*(2*(n+u+w+2)+3) := by
  induction p with
  | nil => simp [encode, instructions]
  | @snoc n p g ih =>
    have hs := emit_length g
    have hm := Nat.mul_le_mul_left n (show 2*(n+u+w+2)+3 ≤ 2*(n+1+u+w+2)+3 by omega)
    simp only [instructions, encode, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
      List.append_nil, List.length_append]
    change (encode (instructions p)).length + (emit g).encode.length ≤ (n+1)*(2*(n+1+u+w+2)+3)
    rw [Nat.succ_mul]
    omega

/-- Unary addresses make the bit length quadratic in the combined input and gate bound. -/
theorem compile_size (c : BooleanTranscript.Circuit (Fin u ⊕ Fin w) n) :
    (encode (compile c)).length ≤ (n+2)*(2*(n+u+w+2)+3) := by
  have hg := instructions_size c.program
  have ho := address_lt c.output
  simp only [compile, encode, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
    List.append_nil, List.length_append]
  change (encode (instructions c.program)).length + _ ≤ _
  simp [Instruction.encode, unary, Nat.add_mul]
  omega

end AdviceCircuit

end VPVNP
end Computability
end OAI
