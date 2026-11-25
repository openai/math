import OAI.Computability.BorderVNP.GeometryAdvicePipeline
import OAI.Computability.VPVNP.CircuitComposition

/-! # Reserving a fixed gate count for a geometry program

The packet circuit may encode absolute addresses derived from the very
allocation containing its gates. Choose a public gate ceiling first, compile
at the resulting addresses, and append unused false AND gates up to that
ceiling. All original gate indices, output addresses and Boolean values
remain available at their genuine positions.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace GeometryFrameEncoding.Table

open VPVNP BooleanTranscript VPVNP.BurstRAM DiagonalResidueRAM
open private read_reindex from OAI.Computability.VPVNP.CircuitComposition
open private refChunks from OAI.Computability.BorderVNP.GeometryOutputModel

variable {σ : Type*} {o b n : ℕ}

private def appendFalse (p : BooleanTranscript.Program σ n) : (extra : ℕ) → BooleanTranscript.Program σ (n+extra)
  | 0 => p
  | k+1 => (appendFalse p k).snoc (.and (.const false) (.const false))

private theorem appendFalse_run (p : BooleanTranscript.Program σ n) (x : σ → Bool) (extra : ℕ) :
    (appendFalse p extra).run x ∘ Fin.castAdd extra = p.run x := by
  funext i
  induction extra with
  | zero => rfl
  | succ k ih =>
    simpa only [Function.comp_apply,appendFalse,BooleanTranscript.Program.run,← Fin.castSucc_castAdd,Fin.snoc_castSucc] using ih

/-- Pad only the physical AND/NOT table. The selected references keep their
original numerical gate indices. -/
def reserve (t : Table σ o b) (ceiling : ℕ) : Table σ o b :=
  let extra := ceiling-t.size
  ⟨t.size+extra,appendFalse t.program extra,t.valid.reindex (Fin.castAdd extra),
    fun i j => (t.bit i j).reindex (Fin.castAdd extra)⟩

/-- The reserved count equals the exact numerical ceiling whenever the
proved compilation bound fits that ceiling. -/
theorem reserve_size (t : Table σ o b) (ceiling : ℕ) (fit : t.size≤ceiling) :
    (t.reserve ceiling).size=ceiling := by change t.size+(ceiling-t.size)=_; omega

/-- The returning guard agrees on every input, including rejecting branches. -/
theorem reserve_valid (t : Table σ o b) (ceiling : ℕ) (x : σ → Bool) :
    GeometryOutput.validBit (t.reserve ceiling) x=GeometryOutput.validBit t x := by
  change (t.valid.reindex _).read id x ((appendFalse t.program _).run x) = t.valid.read id x (t.program.run x)
  rw [read_reindex,appendFalse_run]

/-- Every projected bit retains the value of its original reference. -/
theorem reserve_bit (t : Table σ o b) (ceiling : ℕ) (x : σ → Bool) (i : Fin o) (j : Fin b) :
    ((t.reserve ceiling).bit i j).read id x ((t.reserve ceiling).program.run x) =
      (t.bit i j).read id x (t.program.run x) := by
  change ((t.bit i j).reindex _).read id x ((appendFalse t.program _).run x) = _
  rw [read_reindex,appendFalse_run]

/-- Reserving additional gates does not shift any actual output's absolute
address in the native valuation bank. -/
theorem reserve_address {u v : ℕ} (t : Table (Fin u ⊕ Fin v) o b) (ceiling base : ℕ) :
    address base (t.reserve ceiling).valid = address base t.valid ∧
      ∀ i j, address base ((t.reserve ceiling).bit i j) = address base (t.bit i j) := by
  have addr {n : ℕ} (r : Ref Bool (Fin u ⊕ Fin v) n) (d : ℕ) :
      address base (r.reindex (Fin.castAdd d)) = address base r := by
    cases r with
    | var i => cases i <;> rfl
    | const | gate => rfl
  exact ⟨addr _ _,fun i j => addr _ _⟩

/-- The entire serialized output-address suffix is the original row-major
gather directory, including the guard word, at the new fixed packet end. -/
theorem reserve_referenceWords {u v : ℕ} (t : Table (Fin u ⊕ Fin v) o b) (ceiling W base : ℕ) :
    GeometryOutput.referenceWords W base (t.reserve ceiling) = GeometryOutput.referenceWords W base t := by
  obtain ⟨guard,ports⟩ := t.reserve_address ceiling base
  simp only [GeometryOutput.referenceWords,guard,List.map_flatten,refChunks,List.map_ofFn,Function.comp_def,List.map_reverse]
  simp only [ports]

end GeometryFrameEncoding.Table

end BorderVNP
end Computability
end OAI
