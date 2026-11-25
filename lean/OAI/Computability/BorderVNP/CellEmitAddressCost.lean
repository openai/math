import OAI.Computability.BorderVNP.CellEmitAddress
import OAI.Computability.BorderVNP.CellEmitWordCost

/-! # Sharp clocks for construction of private arithmetic-address templates -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace CellSparse.Packet.Emit

open ExactQuantumFactoring.BitStackProgram
open CellMacro.Generator (exprBits)
open RationalHitting.StackLanguage (codeWord)
open private binAddr litHead from OAI.Computability.BorderVNP.CellEmitAddress

variable {α : Type} {ea : α → List Bool} {a b : α → NatExpr} {n : α → ℕ}

/-- Largest actual charge among the nine address layouts used by the fixed
depth-eight generator. -/
noncomputable def addrMeter (p : Address ea a) (x : α) : ℕ :=
  (Finset.range 9).sup (fun d => (p d).meter x)

/-- Every layout read by the native generator lies in this common maximum. -/
theorem meter_le_addrMeter (p : Address ea a) (x : α) {d : ℕ} (hd : d ≤ 8) :
    (p d).meter x ≤ addrMeter p x := by
  unfold addrMeter
  exact Finset.le_sup (f := fun k => (p k).meter x) (Finset.mem_range.mpr (by omega))

/-- Size of a fixed address template at every possible arithmetic depth. -/
def layoutSize (e : NatExpr) : ℕ := (Finset.range 9).sup (fun d => (exprBits d e).length)

private theorem layout_le (e : NatExpr) {d : ℕ} (h : d ≤ 8) : (exprBits d e).length ≤ layoutSize e :=
  Finset.le_sup (f := fun k => (exprBits k e).length) (Finset.mem_range.mpr (by omega))

/-- A fixed address layout charges its stored bits and the source argument once. -/
theorem meter_constAddr (ea : α → List Bool) (e : NatExpr) (x : α) :
    addrMeter (constAddr ea e) x ≤ 3*((ea x).length+layoutSize e+1) := by
  apply Finset.sup_le
  intro d hd
  exact (meter_constWord ea (exprBits d e) x).trans (by
    have := layout_le e (show d ≤ 8 by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hd)
    omega)

private theorem meter_litHead (p : Procedure ea Nat.bits n) (x : α) :
    (litAddr p 0).meter x ≤ 5000*p.meter x := by
  let raw : Word ea (fun z => (n z).bits) := p.result (fun _ => rfl)
  let tag := codeWord [false] ++ codeWord [false] ++ codeWord [false]
  have h := meter_wordPrepend tag (framed raw) x
  have hf := meter_framed raw x
  have hw := p.words_le_meter x
  have hraw : raw.meter x = p.meter x := Procedure.meter_result ..
  have ht : tag.length = 9 := rfl
  rw [ht] at h
  simp only [litAddr,litHead,Procedure.meter_congrFun]
  change (wordPrepend tag (framed raw)).meter x ≤ _
  omega

/-- Even a padded dynamic literal is printed with only linear overhead in the
input-specific numeric procedure and the fixed padding word. -/
theorem meter_litAddr (p : Procedure ea Nat.bits n) (x : α) :
    addrMeter (litAddr p) x ≤ 10^19*(p.meter x+layoutSize (.lit 0)+1) := by
  apply Finset.sup_le
  intro d hd
  have h₀ := meter_litHead p x
  cases d with
  | zero => omega
  | succ d =>
    let pad := codeWord (exprBits d (.lit 0)) ++ exprBits d (.lit 0)
    have ha := meter_wordAppend (framed (litAddr p 0)) (constWord (ea:=ea) pad) x
    have hf := meter_framed (litAddr p 0) x
    have hc := meter_constWord ea pad x
    have hw := p.words_le_meter x
    have hl := layout_le (.lit 0) (d:=d) (by simp only [Finset.mem_range] at hd; omega)
    have hpad : pad.length = 3*(exprBits d (.lit 0)).length+1 := by
      simp only [pad,List.length_append,RationalHitting.StackLanguage.codeWord_length]; omega
    rw [hpad] at hc
    simp only [litAddr]
    change (wordAppend (framed (litAddr p 0)) (constWord (ea:=ea) pad)).meter x ≤ _
    omega

private theorem meter_binAddr (op : NatExpr → NatExpr → NatExpr) (h0 hs) (p : Address ea a)
    (q : Address ea b) (x : α) :
    addrMeter (binAddr op h0 hs p q) x ≤
      10^17*(addrMeter p x+addrMeter q x+(exprBits 0 (op (.lit 0) (.lit 0))).length+1) := by
  apply Finset.sup_le
  intro d hd
  let head := exprBits 0 (op (.lit 0) (.lit 0))
  cases d with
  | zero =>
    have hw := (p 0).words_le_meter x
    have hp := meter_le_addrMeter p x (d:=0) (by decide)
    have hc := meter_constWord ea head x
    simp only [binAddr,Procedure.meter_congrFun]
    change (constWord (ea:=ea) head).meter x ≤ 10^17*(addrMeter p x+addrMeter q x+head.length+1)
    omega
  | succ d =>
    have hle : d ≤ 8 := by simp only [Finset.mem_range] at hd; omega
    have hp := meter_le_addrMeter p x hle
    have hq := meter_le_addrMeter q x hle
    have hf := meter_framed (p d) x
    have ha := meter_wordAppend (framed (p d)) (q d) x
    have hh := meter_wordPrepend (codeWord head) (wordAppend (framed (p d)) (q d)) x
    rw [RationalHitting.StackLanguage.codeWord_length] at hh
    simp only [binAddr,Procedure.meter_congrFun]
    change (wordPrepend (codeWord head) (wordAppend (framed (p d)) (q d))).meter x ≤ 10^17*(addrMeter p x+addrMeter q x+head.length+1)
    omega

/-- Printing an addition layout has linear input-specific charge in the child printers. -/
theorem meter_addAddr (p : Address ea a) (q : Address ea b) (x : α) :
    addrMeter (addAddr p q) x ≤ 10^19*(addrMeter p x+addrMeter q x+1) := by
  have h := meter_binAddr NatExpr.add (fun _ _ => rfl) (fun _ _ _ => rfl) p q x
  have hl : (exprBits 0 (.add (.lit 0) (.lit 0))).length ≤ 32 := by decide
  exact h.trans (by omega)

/-- Multiplication layouts have the same charge. -/
theorem meter_mulAddr (p : Address ea a) (q : Address ea b) (x : α) :
    addrMeter (mulAddr p q) x ≤ 10^19*(addrMeter p x+addrMeter q x+1) := by
  have h := meter_binAddr NatExpr.mul (fun _ _ => rfl) (fun _ _ _ => rfl) p q x
  have hl : (exprBits 0 (.mul (.lit 0) (.lit 0))).length ≤ 32 := by decide
  exact h.trans (by omega)

/-- Truncated subtraction layouts have the same charge. -/
theorem meter_subAddr (p : Address ea a) (q : Address ea b) (x : α) :
    addrMeter (subAddr p q) x ≤ 10^19*(addrMeter p x+addrMeter q x+1) := by
  have h := meter_binAddr NatExpr.sub (fun _ _ => rfl) (fun _ _ _ => rfl) p q x
  have hl : (exprBits 0 (.sub (.lit 0) (.lit 0))).length ≤ 32 := by decide
  exact h.trans (by omega)

end CellSparse.Packet.Emit

end BorderVNP
end Computability
end OAI
