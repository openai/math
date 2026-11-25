import OAI.ThreeFlat.Diagonal.TraceWordTests
import OAI.ThreeFlat.RAM.ProgramEncoding

namespace OAI
/-! # Program text coordinates and word equality tests -/

namespace ThreeFlat.Diagonal.TraceProgram

open TraceWords RAM
open Computability.VPVNP.BurstRAM Computability.VPVNP.BurstRAM.PrivateRAM
open BinPackingGames.Foundations.Complexity.CookLevin.StatementCircuit (Expr)

variable {w p r k : ℕ} {σ : Type*}

/-- Public coordinates of the instruction and public-operand words. -/
abbrev Text (w p k : ℕ) := Fin (1+6*p+k) × Fin w

def instructionField (i : Fin p) (j : Fin 6) : Fin (1+6*p+k) :=
  ⟨instructionAddress i.val + j.val, by unfold instructionAddress; have := i.isLt; have := j.isLt; omega⟩

def publicField (i : Fin k) : Fin (1+6*p+k) := ⟨1+6*p+i.val, by have := i.isLt; omega⟩

def contents (data : Memory w) : Text w p k → Bool :=
  fun b => bits (data b.1.val) b.2

theorem fetchRow_get (data : Memory w) (i : Fin p) (j : Fin 6) :
    (fetchRow data i).get j = (data (instructionField (k:=k) i j).val).val := by
  fin_cases j <;> rfl

/-- An out-of-range constant operand can never match a word. -/
def fieldIs (read : Fin w → Expr σ) (n : ℕ) : Expr σ :=
  if h : n < 2^w then sameWord read (fun j => .const (bits (⟨n,h⟩ : Word w) j))
  else .const false

theorem fieldIs_true (read : Fin w → Expr σ) (n : ℕ) (input : σ → Bool) (v : Word w)
    (h : ∀ j, (read j).eval input = bits v j) :
    (fieldIs read n).eval input = true ↔ v.val = n := by
  by_cases hn : n < 2^w
  · simpa [fieldIs, hn, Fin.ext_iff] using
      (sameWord_at (a:=v) (b:=⟨n,hn⟩) read (fun j => .const (bits (⟨n,hn⟩ : Word w) j))
        input h (fun _ => rfl))
  · simp [fieldIs, hn, Expr.eval, ne_of_lt (v.isLt.trans_le (Nat.le_of_not_gt hn))]

theorem fieldIs_size (read : Fin w → Expr σ) (n : ℕ) (h : ∀ j, (read j).size ≤ 1) :
    (fieldIs read n).size ≤ 10*w + 1 := by
  unfold fieldIs
  split
  · next hn =>
    simpa [Nat.mul_comm] using (sameWord_size_le read
      (fun j => .const (bits (⟨n,hn⟩ : Word w) j)) h (fun _ => le_rfl))
  · simp [Expr.size]

end ThreeFlat.Diagonal.TraceProgram

end OAI
