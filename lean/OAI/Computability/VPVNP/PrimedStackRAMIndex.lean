import OAI.Computability.VPVNP.PrimedStackRAM

/-!
# Dense counter addresses computed by the word opcodes

The terminal and binary instruction blocks produce the index of the chosen
production. Only the product used before division by two requires a separate
intermediate word bound. All arithmetic after the triangular prefix is
compatible with reduction modulo the word modulus.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PrimedStackRAM

open BurstRAM BurstRAM.PrivateRAM
open scoped Fin.CommRing

variable {w : ℕ} (pub : Fin 11 → Word w) (state : Word w) (regs : Regs w 16) (mem : Memory w)

theorem terminalIndex_word :
    ∃ es rs, trace pub state terminalIndex regs mem = some (es, rs, mem) ∧
      countProbes es = 0 ∧ es.length = 6 ∧ rs 7 = (regs 1 * pub 6 + regs 2)*2 + regs 6 := by
  simp (config := { decide := true }) [terminalIndex, trace, Op.effect, BinaryOp.eval,
    Function.update, countProbes]

theorem binaryIndex_word :
    let tri := Fin.ofNat (2^w) (((regs 0 - 1)*regs 0).val / (2 : Word w).val)
    ∃ es rs, trace pub state binaryIndex regs mem = some (es, rs, mem) ∧
      countProbes es = 0 ∧ es.length = 15 ∧
      rs 7 = (((tri + regs 2)*pub 7 + regs 1)*pub 7 + regs 3)*pub 7 + regs 4 + pub 9 := by
  simp (config := { decide := true }) [binaryIndex, trace, Op.effect, BinaryOp.eval,
    Function.update, countProbes]

variable {n m H : ℕ}

/-- Word indices are exact for all legal terminal choices whenever the dense array fits. -/
theorem terminalIndex_spec (h : Fin H) (j : Fin m) (b : Bool)
    (hp : pub 6 = (m : Word w)) (hr₁ : regs 1 = (h.val : Word w))
    (hr₂ : regs 2 = (j.val : Word w)) (hr₆ : regs 6 = (b.toNat : Word w))
    (hfit : labelCount n m H ≤ 2^w) :
    ∃ es rs, trace pub state terminalIndex regs mem = some (es, rs, mem) ∧
      countProbes es = 0 ∧ es.length = 6 ∧
      (rs 7).val = (labelIndex n m H (.inl (h,j,b))).val := by
  obtain ⟨es, rs, ht, hc, hl, he⟩ := terminalIndex_word pub state regs mem
  refine ⟨es, rs, ht, hc, hl, ?_⟩
  have hw := ((labelIndex n m H (.inl (h,j,b))).isLt).trans_le hfit
  rw [labelIndex_terminal] at hw ⊢
  rw [he, hr₁, hr₂, hr₆, hp]
  exact (show ((↑((h.val*m + j.val)*2+b.toNat) : Word w)).val = _ from
    (Fin.val_natCast ..).trans (Nat.mod_eq_of_lt hw)) ▸ by push_cast; rfl

/-- The exact triangular prefix of the split after the divide instruction. -/
private theorem tri_exact (d : Fin n) (b : Fin d.val) (hr : (regs 0).val = d.val)
    (hw : 2 < 2^w) (hprod : (d.val-1)*d.val < 2^w) :
    Fin.ofNat (2^w) (((regs 0 - 1)*regs 0).val / (2 : Word w).val) = (d.val.choose 2 : Word w) := by
  have hz : regs 0 ≠ 0 := by
    intro hh
    have hb := b.isLt
    rw [hh] at hr
    simp at hr
    omega
  change Fin.ofNat (2^w) ((((regs 0 - 1).val * (regs 0).val) % (2^w)) / (2 : Word w).val) = _
  rw [Fin.val_sub_one_of_ne_zero hz, hr, Nat.mod_eq_of_lt hprod]
  have htwo : (2 : Word w).val = 2 := Nat.mod_eq_of_lt hw
  rw [htwo, Nat.choose_two_right, Nat.mul_comm (d.val-1), Fin.ofNat_eq_cast]

theorem binaryIndex_spec (d : Fin n) (b : Fin d.val) (h i j : Fin H)
    (hp : pub 7 = (H : Word w)) (hp₉ : pub 9 = (H*m*2 : ℕ))
    (hr₀ : (regs 0).val = d.val) (hr₁ : regs 1 = (h.val : Word w))
    (hr₂ : regs 2 = (b.val : Word w)) (hr₃ : regs 3 = (i.val : Word w))
    (hr₄ : regs 4 = (j.val : Word w)) (hw : 2 < 2^w)
    (hprod : (d.val-1)*d.val < 2^w) (hfit : labelCount n m H ≤ 2^w) :
    ∃ es rs, trace pub state binaryIndex regs mem = some (es, rs, mem) ∧
      countProbes es = 0 ∧ es.length = 15 ∧
      (rs 7).val = (labelIndex n m H (.inr ⟨d,h,b,i,j⟩)).val := by
  obtain ⟨es, rs, ht, hc, hl, he⟩ := binaryIndex_word pub state regs mem
  refine ⟨es, rs, ht, hc, hl, ?_⟩
  have hw' := ((labelIndex n m H (.inr ⟨d,h,b,i,j⟩)).isLt).trans_le hfit
  rw [labelIndex_binary] at hw' ⊢
  rw [he, tri_exact regs d b hr₀ hw hprod, hr₁, hr₂, hr₃, hr₄, hp, hp₉]
  let ix := H*m*2 + (((d.val.choose 2 + b.val)*H + h.val)*H + i.val)*H + j.val
  have hx : (↑ix : Word w).val = ix := (Fin.val_natCast ..).trans (Nat.mod_eq_of_lt hw')
  convert hx using 2
  simp only [ix, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
  ring

end PrimedStackRAM

end VPVNP
end Computability
end OAI
