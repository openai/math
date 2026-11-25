import OAI.ThreeFlat.RAM.ExpressionContraction
import OAI.ThreeFlat.RAM.NativeRelocate

namespace OAI
/-! # Relocation of the compiled descriptor and contraction instruction table -/

namespace ThreeFlat.RAM.GeneratedContraction

open Computability.VPVNP.BurstRAM Computability.VPVNP.BurstRAM.PrivateRAM Contraction DescriptorScan DescriptorExpr NativeRelocate

private theorem expression_allowed {w k n q r : ℕ} (e : Term w k n) (loc : Fin e.labels → Fin q)
    (vs : Fin n → Fin r) (tmp : Fin e.binds → Fin r) (out : Fin r) (exit : Fin q)
    (i : Fin e.labels) : ExternalOnly (e.emit loc vs tmp out exit i) := by
  induction e with
  | result => trivial
  | bind op body ih =>
    refine Fin.addCases (fun j : Fin 3 => ?_) (fun j : Fin body.labels => ?_) i
    · simp only [Term.emit, Fin.addCases_left]
      fin_cases j <;> cases op <;> simp [Op.instruction] <;> first | trivial | (split <;> trivial)
    · simp only [Term.emit, Fin.addCases_right]
      apply ih

/-- Every instruction in the assembled descriptor, driver and contraction tail is
independent of the enclosing caller's private memory and persistent word. -/
theorem machine_externalOnly {F : Type*} [Fintype F] [Field F] {p w k : ℕ}
    (N : BitNetwork F p) (fit : Fits N w) (e : Term w (2+(5+k)) 1) (pub : Fin k → Word w)
    (i : Fin (e.labels+(6+35))) :
    ExternalOnly ((machine N fit e.first (expressionRows e) pub).code i) := by
  refine Fin.addCases (fun j : Fin e.labels => ?_) (fun j : Fin (6+35) => ?_) i
  · simp only [machine, assemble, Fin.addCases_left, expressionRows]
    apply expression_allowed
  · refine Fin.addCases (fun v : Fin 6 => ?_) (fun v : Fin 35 => ?_) j
    · simp only [machine, assemble, Fin.addCases_right, Fin.addCases_left]
      fin_cases v <;> trivial
    · simp only [machine, assemble, Fin.addCases_right, evalRow]
      unfold Contraction.instruction
      split <;> trivial

end ThreeFlat.RAM.GeneratedContraction

end OAI
