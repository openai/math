import OAI.ThreeFlat.RAM.PhysicalPinsNat

namespace OAI
/-! # Agreement of word-fit certificates and natural execution under a memory change -/
namespace ThreeFlat.RAM.PhysicalPinsExpr
open Computability.VPVNP.BurstRAM PrivateRAM DescriptorExpr

variable {n W : ℕ} {data : Param → ℕ} {a b : ℕ → ℕ} {v : Fin n → ℕ}

def MemoryAgreement (W : ℕ) (data : Param → ℕ) (a b : ℕ → ℕ) (v : Fin n → ℕ) (f : Formula n) : Prop :=
  f.natural W data a v = f.natural W data b v ∧ (f.Fits W data a v ↔ f.Fits W data b v)

local notation "P" => MemoryAgreement W data a b v

theorem MemoryAgreement.reg (i : Fin n) : P (.reg i) := ⟨rfl,Iff.rfl⟩
theorem MemoryAgreement.lit (i : ℕ) : P (.lit i) := ⟨rfl,Iff.rfl⟩

theorem MemoryAgreement.op (o : BinaryOp) {x y : Formula n} (hx : P x) (hy : P y) :
    P (.op o x y) := by
  constructor <;> simp only [Formula.natural,Formula.Fits,hx.1,hy.1,hx.2,hy.2]

theorem MemoryAgreement.select (q : Comparison) {x y c d : Formula n}
    (hx : P x) (hy : P y) (hc : P c) (hd : P d) : P (.select q x y c d) := by
  constructor <;> simp only [Formula.natural,Formula.Fits,hx.1,hy.1,hc.1,hd.1,hx.2,hy.2,hc.2,hd.2]

theorem MemoryAgreement.atOffset (i : Fin n) (j : ℕ) (h : a (v i+j) = b (v i+j)) :
    P (.load (.op .add (.reg i) (.lit j))) :=
  ⟨h,Iff.rfl⟩

end ThreeFlat.RAM.PhysicalPinsExpr

end OAI
