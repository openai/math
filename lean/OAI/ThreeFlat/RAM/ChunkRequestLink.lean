import OAI.ThreeFlat.RAM.ChunkRequestContinue
import OAI.ThreeFlat.RAM.ContinuationLink
import Mathlib.Data.Fin.VecNotation

namespace OAI
/-! # Linkable ROM for the chunk scan with a caller-supplied continuation -/

namespace ThreeFlat.RAM.ChunkRequests

open Computability.VPVNP.BurstRAM PrivateRAM DescriptorExpr ContinuationLink

variable {w P R K : ℕ}

private theorem exprLabels (w k : ℕ) : (rowTerm w k).labels = 88 := by
  rw [Term.labels_eq, rowTerm_binds]

def linkedRegisters (w K : ℕ) (reg : Fin 37 ↪ Fin R) : Registers w K R where
  slot := (Fin.castLEEmb (by decide : 7 ≤ 37)).trans reg
  tmp := ((finCongr (rowTerm_binds (w := w) (k := K))).toEmbedding.trans
    ((Fin.natAddEmb 7).trans (Fin.castLEEmb (by decide : 36 ≤ 37)))).trans reg
  fresh i j e := by
    have eq := congrArg Fin.val (reg.injective e)
    change i.val = 7 + j.val at eq
    omega

def linkedControl (pc : Fin 93 ↪ Fin P) (i : Fin 5) := pc (Fin.natAdd 88 i)

def linkedLabels (w K : ℕ) (pc : Fin 93 ↪ Fin P) : Labels w K P where
  guard := linkedControl pc 0
  next := linkedControl pc 1
  exit := linkedControl pc 2
  expr := fun i => pc ((i.cast (exprLabels w K)).castAdd 5)

private def exitRows (w K : ℕ) (pc : Fin 93 ↪ Fin P) (reg : Fin 37 ↪ Fin R) (exit : Fin P) :
    Fin 5 → Instr w P R K :=
  let A := linkedRegisters w K reg
  let L := linkedLabels w K pc
  ![.jumpLt (A.slot 0) (A.slot 6) (L.expr (rowTerm w K).first) L.exit,
    .binary .add (A.slot 0) (A.slot 0) (A.slot 5) L.guard,
    .constant (reg 36) 0 (linkedControl pc 3),
    .jumpEq (A.slot 4) (reg 36) (linkedControl pc 4) exit, .reject]

/-- The chunk scan uses no public operands and accepts at the next block's entry. -/
def linkedBlock (w : ℕ) : Block w 93 37 0 where
  first := Fin.natAdd 88 (0 : Fin 5)
  emit {_P _R K} pc reg _ exit :=
    let A := linkedRegisters w K reg
    let L := linkedLabels w K pc
    Fin.append (fun i : Fin 88 => (rowTerm w K).emit L.expr A.input A.tmp (A.slot 4) L.next
      (i.cast (exprLabels w K).symm)) (exitRows w K pc reg exit)

theorem linkedBlock_installed (M : Machine w P R K) (pc : Fin 93 ↪ Fin P) (reg : Fin 37 ↪ Fin R)
    (pub : Fin 0 → Fin K) (exit : Fin P) (h : (linkedBlock w).Installed M pc reg pub exit) :
    ContinueInstalled M (linkedRegisters w K reg) (linkedLabels w K pc) (reg 36)
      (linkedControl pc 3) (linkedControl pc 4) exit := by
  have ctrl (i : Fin 5) : M.code (linkedControl pc i) = exitRows w K pc reg exit i := by
    simpa only [linkedControl, linkedBlock, Fin.append_right] using h (Fin.natAdd 88 i)
  refine ⟨⟨ctrl 0, ?_, ctrl 1⟩, ctrl 2, ctrl 3, ctrl 4, ?_⟩
  · intro i
    simpa only [linkedBlock, linkedLabels, Fin.append_left, Fin.cast_cast, Fin.cast_refl, id_eq] using
      h ((i.cast (exprLabels w K)).castAdd 5)
  · exact reg.injective.ne (by decide : (4 : Fin 37) ≠ 36)

end ThreeFlat.RAM.ChunkRequests

end OAI
