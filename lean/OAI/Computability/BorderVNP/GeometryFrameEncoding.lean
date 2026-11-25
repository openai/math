import OAI.Computability.VPVNP.VerifierMachineNetwork

/-! # A single shared Boolean gate table for a geometry frame

The named outputs of a frame consist of words and a validity flag. The Cook–Levin
compiler emits its AND/NOT table from the frame's gate list. Selecting another
output changes only a reference. Primary inputs may be identified or pinned to
either Boolean constant.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace GeometryFrameEncoding

open VPVNP VerifierNetwork

variable {σ τ : Type*} {o w : ℕ}

/-- Output words, indexed by word and bit, together with the validity flag. -/
abbrev Outputs (o w : ℕ) := (Fin o × Fin w) ⊕ Unit

/-- One AND/NOT program and references to all outputs of its geometry frame. -/
structure Table (σ : Type*) (o w : ℕ) where
  /-- Number of shared AND/NOT gates. -/
  size : ℕ
  /-- Ordered program containing the gates. -/
  program : BooleanTranscript.Program σ size
  /-- Reference to the validity flag. -/
  valid : Ref Bool σ size
  /-- References to the bits of all output words, in frame order. -/
  bit : Fin o → Fin w → Ref Bool σ size

/-- The scalar circuit used by the RAM's gate-table reader. -/
def Table.circuit (t : Table σ o w) : BooleanTranscript.Circuit σ t.size :=
  ⟨t.program, t.valid⟩

variable [Fintype σ]

private noncomputable def selected (f : Frame σ (Outputs o w)) (pins : σ → τ ⊕ Bool)
    (i : Outputs o w) : BooleanTranscript.Circuit τ (f.circuitSize i) :=
  CookCircuit.toTranscriptWith (f.core.toCircuit (Fintype.equivFin _ i))
    (pins ∘ (Fintype.equivFin σ).symm)

private theorem selected_eval (f : Frame σ (Outputs o w)) (pins : σ → τ ⊕ Bool)
    (i : Outputs o w) (x : τ → Bool) :
    (selected f pins i).eval x = f.eval (fun j => (pins j).elim x id) i :=
  CookCircuit.toTranscriptWith_eval _ _ _

private theorem cast_program {k l : ℕ} (h : k = l)
    (p : BooleanTranscript.Program τ k) (r s : Ref Bool τ k) :
    ((h ▸ (⟨p, r⟩ : BooleanTranscript.Circuit τ k) : BooleanTranscript.Circuit τ l).program) =
    ((h ▸ (⟨p, s⟩ : BooleanTranscript.Circuit τ k) : BooleanTranscript.Circuit τ l).program) := by
  cases h
  rfl

private theorem selected_program (f : Frame σ (Outputs o w)) (pins : σ → τ ⊕ Bool)
    (i j : Outputs o w) : (selected f pins i).program = (selected f pins j).program := by
  unfold selected CookCircuit.toTranscriptWith
  apply cast_program

/-- Compile the gate list once and select all live outputs. The same primary input
can occur at several pins, and a pin can instead be a fixed constant. -/
noncomputable def compile (f : Frame σ (Outputs o w)) (pins : σ → τ ⊕ Bool) : Table τ o w where
  size := f.circuitSize (.inr ())
  program := (selected f pins (.inr ())).program
  valid := (selected f pins (.inr ())).output
  bit i j := (selected f pins (.inl (i, j))).output

/-- Translating all outputs together costs at most four gates per source gate. -/
theorem size_le (f : Frame σ (Outputs o w)) (pins : σ → τ ⊕ Bool) :
    (compile f pins).size ≤ 4 * f.size := f.circuitSize_le _

/-- The selected validity reference evaluates to the flag of the original frame. -/
theorem valid_eval (f : Frame σ (Outputs o w)) (pins : σ → τ ⊕ Bool) (x : τ → Bool) :
    (compile f pins).valid.read id x ((compile f pins).program.run x) =
      f.eval (fun j => (pins j).elim x id) (.inr ()) := selected_eval f pins _ x

/-- Every bit reference reads its corresponding frame output from the same run. -/
theorem bit_eval (f : Frame σ (Outputs o w)) (pins : σ → τ ⊕ Bool) (i : Fin o) (j : Fin w)
    (x : τ → Bool) :
    ((compile f pins).bit i j).read id x ((compile f pins).program.run x) =
      f.eval (fun a => (pins a).elim x id) (.inl (i, j)) := by
  change (selected f pins (.inl (i, j))).output.read id x
      ((selected f pins (.inr ())).program.run x) = _
  rw [selected_program f pins (.inr ()) (.inl (i, j))]
  exact selected_eval f pins _ x

end GeometryFrameEncoding

end BorderVNP
end Computability
end OAI
