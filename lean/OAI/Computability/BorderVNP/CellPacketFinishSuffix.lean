import OAI.Computability.BorderVNP.CellPacketCopy
import OAI.Computability.BorderVNP.CellPacketEncode

/-! # Terminating the sparse descriptor and appending the external input bank -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.CellPacket

open VPVNP.BurstRAM CellPacketEncode

variable {w : ℕ} {pub : Arg → Word w} {macros : TeamOpcode.Macros w 8}

/-- After the final field marker, copy the separately addressed external bits verbatim. -/
def writeSuffix : Code := .seq CellPacketCopy.appendOne
  (.seq (.block [.copy 14 4, .binary .add 15 4 5]) (CellPacketCopy.copy false))

/-- Registers used by the enclosing cell dispatcher survive preparation of the external suffix. -/
def Controls (s t : Reg → ℕ) := ∀ i : Reg, i.val ≤ 9 → t i = s i

private theorem controls_of_fixed {s t : Reg → ℕ} (h : Fixed s t) : Controls s t := by
  intro i hi
  apply h <;> intro e <;> subst i <;> norm_num at hi

private theorem copy_setup (s : Bank w) (m : Memory w) (fit : readings s 4+readings s 5 < 2^w) :
    BoundedRun pub macros (.block [.copy 14 4, .binary .add 15 4 5]) s m 2 (fun z =>
      z.reg 14 = readings s 4 ∧ z.reg 15 = readings s 4+readings s 5 ∧
      (∀ j, j ≠ 14 → j ≠ 15 → z.reg j = readings s j) ∧ z.mem = readings m) := by
  let setup := Code.block [.copy 14 4, .binary .add 15 4 5]
  have safe : setup.fixedSafe w (readings pub) (.ofWords s m) := by
    simp (config := {decide := true}) [setup, Code.block, Code.fixedSafe, Code.fixedEval,
      Code.safeReadOnly, Code.evalNat, addressOpFits, NatState.ofWords, fit]
  apply (setup.runFixed pub macros s m safe).mono le_rfl
  rintro _ rfl
  simp (config := {decide := true}) [setup, Code.block, Code.fixedEval, Code.evalNat,
    addressOp, NatState.ofWords]
  intro j h14 h15
  simp [h14,h15]

/-- The source read is preserved across the terminator store. The native bit-copy loop
then leaves the enclosing marker and every external bit consecutively in shared memory. -/
theorem writeSuffix_run (s : Bank w) (m : Memory w) (ext : List Bool) (base cursor : ℕ)
    (c : Constants (readings s)) (sourceReg : readings s 4 = base)
    (lengthReg : readings s 5 = ext.length) (destReg : readings s 20 = cursor)
    (input : CompactWrite.Source m base ext)
    (apart : CompactWrite.Disjoint base ext.length cursor ([true]++ext).length)
    (srcFit : base+ext.length < 2^w) (dstFit : cursor+([true]++ext).length < 2^w) :
    BoundedRun pub macros writeSuffix s m (7*ext.length+5) (fun z =>
      Controls (readings s) z.reg ∧ z.reg 20 = cursor+([true]++ext).length ∧
      z.mem = putDigits (readings m) cursor ([true]++ext)) := by
  have length : ([true]++ext).length = 1+ext.length := by simp [Nat.add_comm]
  rw [length] at apart dstFit
  have init := CellPacketCopy.appendOne_run (pub := pub) (macros := macros) s m c (by omega)
  have run := init.seq (b := .seq (.block [.copy 14 4,.binary .add 15 4 5]) (CellPacketCopy.copy false))
    (t := 2+(7*ext.length+1)) (Q := fun z => Controls (readings s) z.reg ∧
      z.reg 20 = cursor+([true]++ext).length ∧ z.mem = putDigits (readings m) cursor ([true]++ext)) (by
      intro t mt h
      have base' : readings t 4 = base := (h.regs 4 (by decide)).trans sourceReg
      have len' : readings t 5 = ext.length := (h.regs 5 (by decide)).trans lengthReg
      have cur' : readings t 20 = cursor+1 := h.cursor.trans (congrArg (· + 1) destReg)
      have mem' : readings mt = putDigits (readings m) cursor [true] := by
        rw [← destReg]; exact h.mem
      have c' := h.effect.fixed.constants c
      apply (copy_setup (pub := pub) (macros := macros) t mt (by omega)).seq
        (b := CellPacketCopy.copy false) (t := 7*ext.length+1)
      rintro u mu ⟨h14,h15,regs,mem⟩
      have src : readings u 14 = base := h14.trans base'
      have cursor' : readings u 20 = cursor+1 := (regs 20 (by decide) (by decide)).trans cur'
      have stop : readings u 15 = readings u 14+ext.length := by
        change readings u 15 = readings t 4+readings t 5 at h15; omega
      have cu : Constants (readings u) :=
        ⟨(regs 0 (by decide) (by decide)).trans c'.1, (regs 1 (by decide) (by decide)).trans c'.2.1,
         (regs 18 (by decide) (by decide)).trans c'.2.2⟩
      have input' (i : Fin ext.length) : readings mu (readings u 14+i.val) = ext[i].toNat := by
        change readings mu = readings mt at mem
        rw [mem,mem',src,putDigits_outside]
        · exact input i i.isLt
        · have hi := i.isLt
          rcases apart with ha | ha <;> change _ < _ ∨ _ + 1 ≤ _ <;> omega
      have disj : readings u 14+ext.length ≤ readings u 20 ∨ readings u 20+ext.length ≤ readings u 14 := by
        rcases apart with ha | ha <;> omega
      apply (CellPacketCopy.copy_run (pub := pub) (macros := macros) false u mu ext cu stop input' disj
        (by change readings u 20+ext.length < 2^w; omega)).mono le_rfl
      rintro z ⟨fixed,_,dest,mz⟩
      constructor
      · intro i hi
        have n14 : i ≠ 14 := by intro eq; subst i; norm_num at hi
        have n15 : i ≠ 15 := by intro eq; subst i; norm_num at hi
        exact ((controls_of_fixed fixed i hi).trans (regs i n14 n15)).trans
          (controls_of_fixed h.effect.fixed i hi)
      constructor
      · change z.reg 20 = readings u 20+ext.length at dest
        rw [length]; omega
      · change z.mem = putDigits (readings mu) (readings u 20) ext at mz
        change readings mu = readings mt at mem
        rw [putDigits_append, ← mem', ← mem, show [true].length = 1 by rfl, ← cursor', mz])
  exact run.mono (by omega) fun _ h => h

end RoutingISA.CellPacket

end BorderVNP
end Computability
end OAI
