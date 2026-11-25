import OAI.ThreeFlat.RAM.DescriptorExpr
import Mathlib.Data.ZMod.Defs

namespace OAI
/-! # Exact unsigned quotient and remainder on represented natural words -/

namespace ThreeFlat.RAM.WordQuotients

open Computability.VPVNP.BurstRAM PrivateRAM
open scoped Fin.CommRing
variable {w : ℕ}

theorem div_at (a b : ℕ) (ha : a<2^w) (hb : b<2^w) :
    BinaryOp.div.eval (a : Word w) (b : Word w) = ((a/b : ℕ) : Word w) := by
  change Fin.ofNat _ (((a : Word w)).val / ((b : Word w)).val) = _
  rw [Fin.val_cast_of_lt ha, Fin.val_cast_of_lt hb]; exact Fin.ext (by rfl)

theorem mod_at (a b : ℕ) (ha : a<2^w) (hb : b<2^w) :
    BinaryOp.mod.eval (a : Word w) (b : Word w) = ((a%b : ℕ) : Word w) := by
  change Fin.ofNat _ (((a : Word w)).val % ((b : Word w)).val) = _
  rw [Fin.val_cast_of_lt ha, Fin.val_cast_of_lt hb]; exact Fin.ext (by rfl)

end ThreeFlat.RAM.WordQuotients

end OAI
