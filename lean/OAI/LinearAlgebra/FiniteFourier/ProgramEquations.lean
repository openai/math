import OAI.LinearAlgebra.FiniteFourier.Circuit

/-! # Simultaneous equations for a straight-line program

The register numbered zero is the newest register. When a gate is appended,
the source registers of each equation are therefore shifted by one.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

namespace Program

variable {K I : Type*}

private def shiftGate {s : ℕ} (g : BinaryGate K (I ⊕ Fin s)) :
    BinaryGate K (I ⊕ Fin (s + 1)) where
  left := Sum.map id Fin.succ g.left
  right := Sum.map id Fin.succ g.right
  leftCoeff := g.leftCoeff
  rightCoeff := g.rightCoeff

private theorem shiftGate_eval [Semiring K] {s : ℕ} (g : BinaryGate K (I ⊕ Fin s))
    (x : I → K) (v : Fin (s + 1) → K) :
    (shiftGate g).eval (Sum.elim x v) = g.eval (Sum.elim x (fun j => v j.succ)) := by
  have h (w : I ⊕ Fin s) :
      Sum.elim x v (Sum.map id Fin.succ w) = Sum.elim x (fun j => v j.succ) w := by
    cases w <;> rfl
  simp only [BinaryGate.eval, shiftGate, h]

/-- The gate defining each register, with all sources indexed in the completed program. -/
def equations : {s : ℕ} → Program K I s → Fin s → BinaryGate K (I ⊕ Fin s)
  | _, .nil => Fin.elim0
  | _, .step p g => Fin.cases (shiftGate g) (fun j => shiftGate (p.equations j))

/-- Sequential evaluation gives the unique simultaneous solution of all gate equations. -/
theorem solves_equations_iff [Field K] {s : ℕ} (p : Program K I s) (x : I → K)
    (v : Fin s → K) :
    (∀ j, v j = (p.equations j).eval (Sum.elim x v)) ↔ v = p.value x := by
  induction p with
  | nil => exact ⟨fun _ => funext fun j => j.elim0, fun _ j => j.elim0⟩
  | step p g ih =>
    constructor
    · intro h
      have htail : (fun j => v j.succ) = p.value x := by
        apply (ih _).1
        intro j
        simpa only [equations, Fin.cases_succ, shiftGate_eval] using h j.succ
      apply funext
      intro j
      refine Fin.cases ?_ (fun k => congrFun htail k) j
      simpa only [equations, Fin.cases_zero, shiftGate_eval, htail, value] using h 0
    · rintro rfl j
      refine Fin.cases ?_ (fun k => ?_) j
      · simp only [value, equations, Fin.cases_zero, shiftGate_eval, Fin.cases_succ]
      · simpa only [value, equations, Fin.cases_succ, shiftGate_eval] using (ih _).2 rfl k

end Program

end FiniteFourier
end LinearAlgebra
end OAI
