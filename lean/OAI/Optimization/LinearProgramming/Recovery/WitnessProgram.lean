import OAI.Optimization.LinearProgramming.Recovery.WitnessProgramBody
import OAI.Optimization.LinearProgramming.Recovery.WitnessProgramCode
import OAI.Optimization.LinearProgramming.RAM.RAMPolynomial

/-! A fixed finite RAM program for the anchored normalized LP witness. It takes
only the two dimensions, the opposite equation matrix, and the chosen support. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Recovery
namespace WitnessProgram

open RAM RAM.Callable Polynomial

theorem program_spec {h n : ℕ} (E : Matrix (Fin h) (Fin n) ℚ) (S : Finset (Fin n))
    (hn : 0<n) (e : ℕ) (three : 3≤e) (entries : ∀ i j, ratBits (E i j) ≤ e)
    (w : Fin n → ℚ)
    (answer : Elimination.fixedSolve (normalizedSystem (maskedEquations E S) ⟨0,hn⟩)
      (Presentation.anchorRhs (h+n)) = some w) :
    ∃ k ≤ clockPolynomial.eval (h+n), ∃ tr : Fin (k+1) → State ℚ,
      Trace program (start [h,n] (MaskedInput.bundle E S)) k tr ∧
      (tr (Fin.last k)).output = some 0 ∧ (∀ j : Fin n, (tr (Fin.last k)).data j.val = w j) ∧
      ∀ i a, ratBits ((tr i).data a) ≤ heightPolynomial.eval (h+n+e) := by
  obtain ⟨out,work,vector⟩ := body_run E S hn e three entries w answer
  let M := heightPolynomial.eval (h+n+e)
  have leM : e ≤ M := WitnessSolve.old_height_le h n e
  have size : (MaskedInput.bundle E S).length = MaskedDecision.lengthTerm.value (Boot.dimensions h n) := by
    change (MaskedInput.bundle E S).length = h*n+n
    simp [MaskedInput.bundle]
  have bounded : (start [h,n] (MaskedInput.bundle E S)).memory.AllData (fun q => ratBits q ≤ M) :=
    fun j => (MaskedInput.bundle_height E S e three entries j).trans leM
  have count := (bodyTime_bound h n).trans (polynomial_eval_le_polyBound bodyPolynomial _)
  obtain ⟨k,hk,tr,trace,tag,data,safe⟩ := Boot.publicDecision_correct
    MaskedDecision.lengthTerm body (.addrLT 0 0) 0 0 (bodyPolynomial.eval 1) bodyPolynomial.natDegree
    h n (MaskedInput.bundle E S) (fun z => ratBits z ≤ M) out size bounded (three.trans leM) (work.mono count)
  refine ⟨k,hk,tr,trace,?_,?_,safe⟩
  · simpa using tag
  · intro j
    exact (congrFun data j.val).trans (vector j)

end WitnessProgram
end Recovery
end LinearProgramming
end Optimization
end OAI
