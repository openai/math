import OAI.Computability.VPVNP.PairShrinkHiddenTable
import OAI.Computability.VPVNP.PairVertexImage

/-!
# Hosting the absorbed-field scan inside the vertex image

The segment enters the header reader on the caller's live operands and
returns to the supplied continuation after the last owned field. It uses
the same register layout as the reset-entry program.
-/

namespace OAI
namespace Computability
namespace VPVNP

noncomputable section

namespace PairSimulation.ShrinkHiddenGuess.Table

open BurstRAM PrivateRAM CompressorRecords NodeArguments.ChildScan
open scoped Fin.CommRing

variable (s t : ℕ) {p r W : ℕ}

/-- Number of instructions in the hosted scan segment, comprising the compiled header rows
followed by one row for each scan stage. -/
abbrev segmentCount := (lines s t).length + Fintype.card Stage

/-- Host program counter for a scan stage, indexed in the segment after all compiled header
rows. -/
def segmentLoop (pc : Fin (segmentCount s t) → Fin p) (j : Stage) :=
  pc (((Fintype.equivFin Stage) j).natAdd (lines s t).length)

/-- Host program counter for a compiled header row, with indices at or beyond the header length
directed to the scan's initialization. -/
def segmentHeader (pc : Fin (segmentCount s t) → Fin p) (i : ℕ) :=
  if h : i < (lines s t).length then pc ((⟨i,h⟩ : Fin (lines s t).length).castAdd (Fintype.card Stage))
  else segmentLoop s t pc (.inl .one)

/-- The live source bank in the same layout as the four-operand preamble. -/
def segmentInputs : Fin 6 ↪ Fin (R s t) :=
  ⟨inputs s t,fun _ _ eq => Sum.inr.inj (Sum.inr.inj ((Fintype.equivFin _).injective eq))⟩

/-- Vertex-image segment that prepares the scan from the caller's live operands, guesses the
owner's absorbed fields, and jumps to the supplied continuation. -/
def segment : VertexImage.Segment where
  count := segmentCount s t
  privateRegs := R s t
  entry := segmentHeader s t id 0
  row pc _ _ prv ret := Fin.addCases
    (fun i => RegisterSetup.instruction ((vm s t).trans prv) ((segmentInputs s t).trans prv)
      ((lines s t)[i.val]) (segmentHeader s t pc (i.val+1)))
    (fun j => instruction (segmentLoop s t pc) ((regs s t).trans prv) ret ((Fintype.equivFin Stage).symm j))

theorem segment_entry (pc : Fin (segment s t).count → Fin p) :
    pc (segment s t).entry = segmentHeader s t pc 0 := by
  simp only [segment,segmentHeader,segmentLoop]
  split <;> rfl

theorem segment_after_header (pc : Fin (segment s t).count → Fin p) :
    segmentHeader s t pc (lines s t).length = segmentLoop s t pc (.inl .one) := by
  simp [segmentHeader]

private theorem resize_twice {b : ℕ} (op : Instr b p r 11) (hb : b ≤ 5) :
    (op.resize 5).resize W = op.resize W := by
  cases op <;> first | rfl | simp only [Instr.resize,resize_literal hb]

theorem segment_linked (M : Machine W p r 11) (pc : Fin (segment s t).count → Fin p)
    (dfs : Fin 9 ↪ Fin r) (saved : VertexImage.Saved ↪ Fin r)
    (prv : Fin (segment s t).privateRegs ↪ Fin r) (ret : Fin p)
    (rows : ∀ i, M.code (pc i) = ((segment s t).row pc dfs saved prv ret i).resize W) :
    RegisterSetup.Linked ((vm s t).trans prv) ((segmentInputs s t).trans prv) M (segmentHeader s t pc) (lines s t) ∧
      Linked M (segmentLoop s t pc) ((regs s t).trans prv) ret := by
  constructor
  · intro i
    unfold segmentHeader
    rw [dite_eq_left i.isLt]
    apply (rows (i.castAdd (Fintype.card Stage))).trans
    simp only [segment,Fin.addCases_left]
    rw [← RegisterSetup.resize_instruction (w := 5), resize_twice _ (by decide), RegisterSetup.resize_instruction]
    rfl
  · intro j
    apply (rows (((Fintype.equivFin Stage) j).natAdd (lines s t).length)).trans
    simp only [segment,Fin.addCases_right,Equiv.symm_apply_apply]
    rw [← resize_instruction (W := 5),resize_twice _ (by decide),resize_instruction]

/-- The host supplies four live operands in the protected six-register bank. -/
structure SegmentOperands (prv : Fin (segment s t).privateRegs ↪ Fin r)
    (g : Args W) (oldLevel : ℕ) (c : Config W p r) : Prop where
  level : c.reg (prv (segmentInputs s t 5)) = (oldLevel : Word W)
  owner : c.reg (prv (segmentInputs s t 0)) = (g.owner : Word W)
  base : c.reg (prv (segmentInputs s t 1)) = (g.scratchBase : Word W)
  stride : c.reg (prv (segmentInputs s t 2)) = (g.slotStride : Word W)

end PairSimulation.ShrinkHiddenGuess.Table

end

end VPVNP
end Computability
end OAI
