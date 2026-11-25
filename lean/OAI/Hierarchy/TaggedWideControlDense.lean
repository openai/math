import OAI.Hierarchy.TaggedWideControlProgram

namespace OAI
/-! # Fixed address and bit projections from the paid controller's dense readout -/

noncomputable section
namespace Hierarchy.Tagged.WideControlJoin.Gate
open ThreeFlat.RAM PhysicalProcedure
open ThreeFlat.Diagonal TraceWords
open Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.RAMMemory
open scoped Classical

def denseAddr {U W : ℕ} (extent : U≤2^W) (i : Fin U) : Word W :=
  ⟨i.val,i.isLt.trans_le extent⟩

/-- The gate reads each address below the charged extent once, in its native order. -/
abbrev denseProcedure {W S f U : ℕ} (P : Procedure W) (ret start : Word W)
    (extent : U≤2^W) (m : ℕ) (word : 3≤W+1) (labels : P.labels+3≤2^(W+1))
    (hs : S≤2^W) (clock : f+U≤2^(W+1)) : Gate :=
  ofProcedure P ret start (denseAddr extent) m word labels hs clock

def denseSeen {U W : ℕ} (a : ℕ) (inside : a<U) (j : Fin (W+1)) : Fin U × Fin (W+1) :=
  (⟨a,inside⟩,j)

variable {W S f U : ℕ} (P : Procedure W) (ret start : Word W)
    (extent : U≤2^W) (m : ℕ) (word : 3≤W+1) (labels : P.labels+3≤2^(W+1))
    (hs : S≤2^W) (clock : f+U≤2^(W+1))
local notation "G" => denseProcedure P ret start extent m word labels hs clock

/-- Each fixed address pin is a literal projection of the actual terminal word. -/
theorem dense_terminal (out : Memory W) (a : ℕ) (inside : a<U) (j : Fin (W+1)) :
    (G).terminal out (denseSeen a inside j) = (out a).val.testBit j.val := rfl

theorem dense_terminal_word (out : Memory W) (a : ℕ) (inside : a<U) (j : Fin W) :
    (G).terminal out (denseSeen a inside j.castSucc) = TraceWords.bits (out a) j := rfl

theorem dense_terminal_high (out : Memory W) (a : ℕ) (inside : a<U) :
    (G).terminal out (denseSeen a inside (Fin.last W)) = false := by
  exact Nat.testBit_eq_false_of_lt (out a).isLt

theorem dense_terminal_flag (out : Memory W) (a : ℕ) (inside : a<U) (b : Bool)
    (value : (out a).val=b.toNat) :
    (G).terminal out (denseSeen a inside 0) = b := by
  change (out a).val.testBit 0=b
  rw [value]
  cases b <;> decide

end Hierarchy.Tagged.WideControlJoin.Gate

end
end OAI
