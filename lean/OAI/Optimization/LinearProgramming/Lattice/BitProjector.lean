import OAI.Optimization.LinearProgramming.Lattice.BitProjectorProcedures
import OAI.Optimization.LinearProgramming.Lattice.BitProjectorSize

/-! Uniform bit-stack deployment and its agreement with the orthogonal projector. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Lattice
namespace Bit
namespace Projector

open ExactQuantumFactoring.BitStackProgram
open ExactQuantumFactoring.BitStackProgram.Procedure
open WithLp

/-- Function deployed on packets of arbitrary shape. A guard bounded by the input word
is exact whenever the directions are independent. -/
noncomputable def deployed (x : Arg) : Table :=
  (((cappedTransition workCode next)^[(argCode x).length])
    (space.eval (argCode x).length,start x)).2.2

/-- Uniform finite Boolean-stack code for the complete residual projector. -/
noncomputable def projectorP : Procedure argCode tableCode deployed :=
  ((second intMatrixCode tableCode).comp (cappedIterationP startP nextP Polynomial.X space)).congrFun
    (by intro x; simp only [Function.comp_apply, Polynomial.eval_X, deployed])

/-- Generate the dimension tally from an actual length-p integer row whenever the caller
already carries one (the row contents may all be zero). -/
noncomputable def projectorFromWidthRowP : Procedure (prodCode intRowCode intMatrixCode) tableCode
    (fun x : List ℤ × IntMatrix => deployed (x.1.length,x.2)) := by
  let length := PriceGame.Learning.GenerationCost.lengthUnaryP intCode (0:ℤ)
  exact projectorP.comp ((length.comp (first intRowCode intMatrixCode)).pair (second intRowCode intMatrixCode))

/-- Agreement with the materialized orthogonal complement projector on each independent
list. Its clock and all intermediate packet lengths are polynomials in the actual input encoding. -/
theorem projector_pack {p : ℕ} (zs : List (Fin p → ℤ))
    (hli : LinearIndependent ℝ (fun i : Fin zs.length => toLp 2 (realCoordinates (zs.get i)))) :
    deployed (input zs) = pack (residualTableMatrix zs) := by
  let n := (argCode (input zs)).length
  have hp : p ≤ n := by
    simp only [n,input,argCode,prodCode,pairBits_length,unaryCode,List.length_replicate]
    omega
  have htime : zs.length ≤ n := (by simpa using hli.fintype_card_le_finrank : zs.length ≤ p).trans hp
  unfold deployed
  rw [cappedTransition_iterate_exact _ _ _ _ _ (fun k _ _ => next_input_fits zs hli k)]
  rw [next_input_iterate,residualTableMatrix_eq]
  simp [show zs.length-(argCode (input zs)).length = 0 from Nat.sub_eq_zero_of_le htime]

theorem deployed_cell {p : ℕ} (zs : List (Fin p → ℤ))
    (hli : LinearIndependent ℝ (fun i : Fin zs.length => toLp 2 (realCoordinates (zs.get i))))
    (i j : Fin p) : cell (deployed (input zs)) i.val j.val = rationalResidualMatrix zs i j := by
  rw [projector_pack zs hli,pack_cell,residualTableMatrix_eq]

end Projector
end Bit
end Lattice
end LinearProgramming
end Optimization
end OAI
