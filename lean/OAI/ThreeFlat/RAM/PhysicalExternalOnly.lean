import OAI.ThreeFlat.RAM.PhysicalProgramValue

namespace OAI
/-! # Relocation of the physical descriptor and contraction program -/

namespace ThreeFlat.RAM

open Computability.VPVNP.BurstRAM PrivateRAM NativeRelocate DescriptorExpr

private theorem op_externalOnly {w k n p r : ℕ} (op : Op w k n) (pc : Fin 3 → Fin p)
    (vars : Fin n → Fin r) (dst : Fin r) (exit : Fin p) (i : Fin 3) :
    ExternalOnly (op.instruction pc vars dst exit i) := by
  cases op with
  | select cmp a b yes no => cases cmp <;> fin_cases i <;> trivial
  | _ => fin_cases i <;> trivial

theorem DescriptorExpr.Term.emit_externalOnly {w k n p r : ℕ} (e : Term w k n)
    (loc : Fin e.labels → Fin p) (vs : Fin n → Fin r) (tmp : Fin e.binds → Fin r)
    (out : Fin r) (exit : Fin p) (i : Fin e.labels) :
    ExternalOnly (e.emit loc vs tmp out exit i) := by
  induction e with
  | result => trivial
  | bind op body ih =>
    refine Fin.addCases (fun j : Fin 3 => ?_) (fun j : Fin body.labels => ?_) i
    · simp only [Term.emit,Fin.addCases_left]
      apply op_externalOnly
    · simp only [Term.emit,Fin.addCases_right]
      apply ih

private theorem relocated_externalOnly {w p r k P R K : ℕ} (pc : Fin p ↪ Fin P)
    (reg : Fin r ↪ Fin R) (pub : Fin k → Fin K) (i : Instr w p r k)
    (h : ExternalOnly i) : ExternalOnly (relocate pc reg pub i) := by
  cases i <;> exact h

open GeneratedContraction DescriptorScan BitLayout
open Contraction (Fits)

/-- The expression rows, the six scan instructions, and the 35 relocated
contraction instructions all operate independently of the caller's private memory. -/
theorem GeneratedContraction.expressionMachine_externalOnly {F : Type*} [Fintype F] [Field F]
    {w p k : ℕ} (N : BitNetwork F p) (fit : Fits N w)
    (e : Term w (2+(5+k)) 1) (pub : Fin k → Word w) (i) :
    ExternalOnly ((machine N fit e.first (expressionRows e) pub).code i) := by
  refine Fin.addCases (fun j : Fin e.labels => ?_) (fun j : Fin (6+35) => ?_) i
  · simp only [machine,assemble,Fin.addCases_left,expressionRows]
    apply Term.emit_externalOnly
  · refine Fin.addCases (fun j : Fin 6 => ?_) (fun j : Fin 35 => ?_) j
    · simp only [machine,assemble,Fin.addCases_right,Fin.addCases_left]
      fin_cases j <;> trivial
    · simp only [machine,assemble,Fin.addCases_right,evalRow]
      exact relocated_externalOnly _ _ _ _ (ContractionTail.instruction_externalOnly j)

namespace PhysicalPinsExpr.Program

attribute [local irreducible] program GeneratedContraction.machine

/-- Every instruction of the native physical program can run under the
external-memory relocation theorem. Its public parameters carry the instance. -/
theorem native_externalOnly {F : Type*} [Fintype F] [Field F] {w : ℕ}
    (s : Shape) [NeZero s.period] (N : BitNetwork F (s.area+2*s.halfBits))
    (params : Fin s.parameterBits → Bool) (fit : Fits (H s N params) w)
    (i : Fin ((program w).labels+(6+35))) :
    ExternalOnly ((native s N params fit).code i) := by
  unfold native
  exact expressionMachine_externalOnly (w := w) (p := sizePins s) (k := 20)
    (H s N params) fit (program w) (pub s N params fit) i

end PhysicalPinsExpr.Program
end ThreeFlat.RAM

end OAI
