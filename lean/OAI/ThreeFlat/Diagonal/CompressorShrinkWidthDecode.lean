import OAI.ThreeFlat.Diagonal.CompressorShrinkWidthWriter
import OAI.ThreeFlat.Diagonal.CompressorEdgeKey

namespace OAI
/-! # The admitted width reader decodes precisely the recorded rooted edge -/

namespace ThreeFlat.Diagonal.CompressorPacking.Native.ShrinkWidth
open Computability.VPVNP.BurstRAM Computability.VPVNP.BurstRAM.PrivateRAM RAM.PhysicalPinsExpr Placement Computability.VPVNP.Compression
open scoped BigOperators
variable {n mw : ℕ}
variable (data : Param → ℕ) (mem : ℕ → ℕ) (vs : Fin n → ℕ)
local notation "V" => Formula.natural mw data mem vs

theorem choose4_value (k : F n) (f : Fin 4 → F n) (i : Fin 4) (hi : V k = i.val) :
    V (choose4 k f) = V (f i) := by
  fin_cases i <;> simp [choose4,Formula.natural,natTest,hi]

variable {B H Tag L : Type*} {d c J : ℕ}
variable [AddCommGroup H] [AddCommGroup Tag] [AddCommGroup L]
variable (P : PackingData B H Tag L d c)
variable (b : B ↪ ℕ) (tag : Tag ↪ Fin J) (count : Fin 4 → ℕ) (pieces : ℕ) (bound : ∀ k, count k ≤ pieces)

private theorem digit_mod {r : ℕ} (a : ℕ) (i : Fin r) : appendKey a i % r = i.val := by
  simp [appendKey,Nat.mod_eq_of_lt i.isLt]

private theorem digit_div {r : ℕ} (a : ℕ) (i : Fin r) : appendKey a i / r = a := by
  simp only [appendKey,Nat.mul_comm a r,Nat.mul_add_div (Nat.zero_lt_of_lt i.isLt),
    Nat.div_eq_of_lt i.isLt,Nat.add_zero]

theorem decode_value (live output : ℕ) (key tags : F n) (e : ShrinkEdge P count)
    (hk : V key = 1+edgeKey P b tag count pieces bound e) (ht : V tags = J) :
    let S : Graph.Stage := ⟨d,c,count,pieces,live,output⟩
    let a := decode S tags key
    let m := e.2.1.val.val
    a.old.map V = ⟨⟨b m.1.1.1,(tag m.1.1.2.1).val,0⟩,
      (finFunctionFinEquiv (m:=2) m.2.1).val,(P.slotLabel m.2.2).val⟩ ∧
      V a.oldPort=m.1.2.val ∧ V a.survivor=e.1.val ∧ V a.copy=e.2.2.val := by
  dsimp only
  simp only [decode,Position.map,Placement.Site.map,Formula.natural,natOp,hk,ht,Nat.add_sub_cancel_left,
    edgeKey,rootKey,digit_div,digit_mod,Fin.val_castLE,and_self]

end ThreeFlat.Diagonal.CompressorPacking.Native.ShrinkWidth

end OAI
