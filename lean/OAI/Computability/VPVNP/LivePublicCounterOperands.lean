import OAI.Computability.VPVNP.LivePublicCounterPrefix
import OAI.Computability.VPVNP.RAMTapePublicInputOperands

/-! # The auxiliary public table in the live linker's operand format -/

namespace OAI
namespace Computability
namespace VPVNP

namespace LiveProgram.CounterPublic

open BurstRAM PrimedCounter RAMTape.PublicExprMachine

/-- The length and packed word of the supplied universal-machine program's literal prefix. -/
def actualPrefix (p : UniversalMachine.Program) : LiteralPrefix :=
  ⟨(UniversalMachine.programPrefix p).length,(PrimedInputRAM.Opcodes.packedPrefix p).val⟩

/-- Positions 7 and 12 come from the input prefix. Every other operand uses geometry arithmetic. -/
def operands (c : Constants) (j : Fin 34) : InputOperand :=
  if j.val = 7 then .prefixLength else if j.val = 12 then .prefixWord else .geometry (shape c j)

variable (c : Constants) {p : UniversalMachine.Program} {B n H : ℕ}
  {i : Fin (2^(n^c.chainPower-1))}
  (Q : PrimedInputRAM.Layout ((spec p c).lengths n i) n (addressWidth B n) H (CursorBounds.wordBits B n))
  (D : Data Q (n^(c.circuitExponent+5)))

theorem operands_correct (hB : 1 ≤ B) (hn : 2 ≤ n) (hp : Q.program = p)
    (hbase : Q.scratchBase = 2^CursorBounds.virtualBits B n) (hf : D.Fits) (hroot : D.root.val = 0)
    (j : Fin 34) :
    let g := AssemblerPublic.geometry B n H
    Pieces.word g (actualPrefix p) (operands c j) = D.pub j ∧
      match operands c j with
      | .geometry e => e.Fits g (2^g.w)
      | a => a.eval g (actualPrefix p) < 2^g.w := by
  let g := AssemblerPublic.geometry B n H
  have hc := correct p c Q D hB hn hp hbase hf hroot j
  by_cases h7 : j.val = 7
  · have he : j = 7 := Fin.ext h7
    subst j
    have hval : (UniversalMachine.programPrefix p).length < 2^g.w := by
      rw [← hp]; exact PrimedInputRAM.Opcodes.pubNat_lt Q hf.assembler 7
    exact ⟨hc.1,hval⟩
  by_cases h12 : j.val = 12
  · have he : j = 12 := Fin.ext h12
    subst j
    have hval : (PrimedInputRAM.Opcodes.packedPrefix p).val < 2^g.w := by
      exact (congrArg (fun q => (PrimedInputRAM.Opcodes.packedPrefix q).val) hp).symm ▸
        (show (PrimedInputRAM.Opcodes.packedPrefix Q.program).val < 2^g.w from
          PrimedInputRAM.Opcodes.pubNat_lt Q hf.assembler 12)
    exact ⟨hc.1,hval⟩
  simp only [operands,h7,h12,↓reduceIte,Pieces.word,InputOperand.eval,table_other c p j h7 h12]
  exact hc

/-- Physical execution of the auxiliary table loader, with a fixed program independent of its own prefix. -/
theorem fixed_runs (hB : 1 ≤ B) (hn : 2 ≤ n) (hp : Q.program = p)
    (hbase : Q.scratchBase = 2^CursorBounds.virtualBits B n) (hf : D.Fits) (hroot : D.root.val = 0)
    (persistent : Word (CursorBounds.wordBits B n))
    (rs : Fin (RAMTape.InputOperandMachine.registers (operands c)) → Word (CursorBounds.wordBits B n))
    (log : BurstRAM.PrivateRAM.WriteLog (CursorBounds.wordBits B n)) :
    let g := AssemblerPublic.geometry B n H
    let args := operands c
    let pub := RAMTape.InputOperandMachine.input g (actualPrefix p)
    ∃ t ≤ coefficient (RAMTape.InputOperandMachine.geometryOnly args)*(g.w+1)^2 + 34*(8*g.w+3)+2,
      ∃ out : Fin (RAMTape.InputOperandMachine.registers args) → Word g.w,
        (RAMTape.InputOperandMachine.program args).Runs t (RAMTape.ISA.bank pub persistent rs log)
          (RAMTape.ISA.bank pub persistent out log) ∧
        ∀ j, out (RAMTape.InputOperandMachine.slot args j) = D.pub j := by
  let g := AssemblerPublic.geometry B n H
  have h := operands_correct c Q D hB hn hp hbase hf hroot
  have hfits (j : Fin 34) : (RAMTape.InputOperandMachine.geometryOnly (operands c) j).Fits g (2^g.w) := by
    have hh := (h j).2
    cases he : operands c j with
    | geometry e =>
      rw [he] at hh
      simpa only [RAMTape.InputOperandMachine.geometryOnly,he] using hh
    | prefixWord | prefixLength =>
      simp only [RAMTape.InputOperandMachine.geometryOnly,he]
      exact ⟨Nat.two_pow_pos _,trivial⟩
  obtain ⟨t,ht,out,run,hout⟩ := RAMTape.InputOperandMachine.runs (operands c) g (actualPrefix p) hfits persistent rs log
  exact ⟨t,ht,out,run,fun j => (hout j).trans (h j).1⟩

end LiveProgram.CounterPublic

end VPVNP
end Computability
end OAI
