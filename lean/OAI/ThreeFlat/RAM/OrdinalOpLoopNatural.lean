import OAI.ThreeFlat.RAM.OrdinalOpLoop
import OAI.ThreeFlat.RAM.CachedBlock
import Mathlib.Tactic.FinCases

namespace OAI
/-! # Relocating the ordinal-loop driver and row instructions -/

namespace ThreeFlat.RAM.OrdinalOpLoop
open Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.PrimedStackRAM CachedBlock

private def continuation {n P : ℕ} (pc : Fin (3+n) ↪ Fin P) : Fin (n+1) → Fin P :=
  Fin.lastCases (pc ((2 : Fin 3).castAdd n)) (fun j => pc (Fin.natAdd 3 j))

private theorem target_continuation {n P : ℕ} (pc : Fin (3+n) ↪ Fin P) (exit : Fin P)
    (j : Fin (n+1)) :
    targets pc exit (continuation (Fin.castAddEmb 1) j) = continuation pc j := by
  induction j using Fin.lastCases with
  | last =>
    simp only [continuation, Fin.lastCases_last]
    exact Fin.addCases_left ..
  | cast i =>
    simp only [continuation, Fin.lastCases_castSucc]
    exact Fin.addCases_left ..

private theorem relocate_id {r k : ℕ} (op : Op r k) :
    relocate (Function.Embedding.refl (Fin r)) id op = op := by
  cases op <;> rfl

private theorem relocate_emit {A P r R k K : ℕ} (w : ℕ) (f : Fin A → Fin P)
    (reg : Fin r ↪ Fin R) (pub : Fin k → Fin K) (next bad : Fin A) (op : Op r k) :
    ((relocate reg pub op).emit (f next) (f bad)).resize w =
      mapInstr f reg pub ((op.emit next bad).resize w) := by
  cases op <;> rfl

/-- Every label, register and public-word index comes from the installation maps. -/
theorem block_natural {r k : ℕ} (w : ℕ) (xs : List (Op r k)) (cursor bound : Fin r)
    (limit : Fin k) : Natural (block w xs cursor bound limit) := by
  intro P R K pc reg pub exit i
  have slot (j : Fin (3+xs.length)) : targets pc exit ((Fin.castAddEmb 1) j) = pc j :=
    Fin.addCases_left ..
  have done_ : targets pc exit (Fin.natAdd (3+xs.length) 0) = exit := Fin.addCases_right ..
  refine Fin.addCases ?_ ?_ i
  · intro j
    simp only [canonicalRow, block, Fin.addCases_left]
    fin_cases j
    · exact congrArg (fun next => Instr.constant (k := K) (reg cursor) (0 : Word w) next)
        (slot ((1 : Fin 3).castAdd xs.length)).symm
    · exact congrArg (fun next => Instr.publicWord (w := w) (reg bound) (pub limit) next)
        (slot ((2 : Fin 3).castAdd xs.length)).symm
    · change (Instr.jumpLt (w := w) (k := K) (reg cursor) (reg bound) (continuation pc 0) exit) =
        .jumpLt (reg cursor) (reg bound) (targets pc exit (continuation (Fin.castAddEmb 1) 0))
          (targets pc exit (Fin.natAdd (3+xs.length) 0))
      rw [target_continuation, done_]
  · intro j
    simp only [canonicalRow, block, Fin.addCases_right]
    change ((relocate reg pub (xs.get j)).emit (continuation pc j.succ) exit).resize w =
      mapInstr (targets pc exit) reg pub
        (((relocate (Function.Embedding.refl (Fin r)) id (xs.get j)).emit
          (continuation (Fin.castAddEmb 1) j.succ) (Fin.natAdd (3+xs.length) 0)).resize w)
    rw [relocate_id, ← relocate_emit, target_continuation, done_]

end ThreeFlat.RAM.OrdinalOpLoop

end OAI
