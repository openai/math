import OAI.ThreeFlat.RAM.ChunkRequestExpr
import Mathlib.Data.List.OfFn

namespace OAI
/-! # Physical request addresses -/

namespace ThreeFlat.RAM.ChunkRequests

open Computability.VPVNP.BurstRAM PrivateRAM

variable {w p r k : ℕ}

/-- The i-th successive request address, with word arithmetic as executed by the RAM. -/
def cursorAt (stride : Word w) : ℕ → Word w → Word w
  | 0, cursor => cursor
  | i+1, cursor => cursorAt stride i (cursor+stride)

theorem cursorAt_val (stride cursor : Word w) (i : ℕ)
    (fit : cursor.val + i * stride.val < 2^w) :
    (cursorAt stride i cursor).val = cursor.val + i * stride.val := by
  induction i generalizing cursor with
  | zero => simp [cursorAt]
  | succ i ih =>
    rw [Nat.succ_mul] at fit ⊢
    have step : (cursor+stride).val = cursor.val + stride.val :=
      Fin.val_add_eq_of_add_lt (by omega)
    rw [cursorAt, ih _ (by rw [step]; omega), step]
    omega

/-- Records in physical scan order, starting at the prepared interval. -/
def preparedRows (m : Memory w) (cursor stride : Word w) (n : ℕ) : List (Request w) :=
  List.ofFn (fun i : Fin n => readRow m (cursorAt stride i.val cursor))

end ThreeFlat.RAM.ChunkRequests

end OAI
