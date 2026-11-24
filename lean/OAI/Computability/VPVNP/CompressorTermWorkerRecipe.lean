import OAI.Computability.VPVNP.CompressorTermWorkerRun
import OAI.Computability.VPVNP.CompressorRecordsPhaseRecipe

/-!
# Fixed planner operands for the motif worker

The four physical address formulas are supplied by the level planner. Every
remaining operand is the reduction of a fixed natural coefficient. The word
reader determines the width by doubling a one-bit mask until it vanishes.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.TermWorker

open BurstRAM PhaseRecipe MotifGrid MotifBlocks MotifConversion MotifSelector

variable {k : Type*} [Field k] {J D S : Type} [Fintype J] [Fintype D] [Fintype S]
variable {a b : D → J} {P : Supply J S} {p : D → ℚ} {q : S → ℚ} {H H' : ℝ}
variable (B : FixedBlock k a b P (realWidths p) (realWidths q) H H')
variable {d n t w : ℕ}

private def demandLiterals (order : Fin d ≃ D) (p : D → ℚ) (scale : ℕ) : Fin (d+1) → Expr :=
  Fin.lastCases (.lit (scale^2 * MotifAdmission.denominator p))
    (fun i => .lit (MotifAdmission.weight p (order i)))

private def gridLiterals (order : Fin d ≃ D) (p : D → ℚ) (rows : Fin t → D → ℚ)
    (x : Fin (t*d*3)) : Expr :=
  let (ji,f) := finProdFinEquiv.symm x
  let (j,i) := finProdFinEquiv.symm ji
  let u := rows j (order i)
  .lit (if f = 0 then i.val else if f = 1 then u.den^2 * MotifAdmission.denominator p else u.num.natAbs^2)

private theorem evalDemand (order : Fin d ≃ D) (p : D → ℚ) (scale : ℕ) (pub : Fin 5 → BurstRAM.Word w)
    (state : BurstRAM.Word w) (m : Memory w) (i : Fin (d+1)) :
    (demandLiterals order p scale i).eval pub state m = DemandPreparation.publicWords order p scale w i := by
  cases i using Fin.lastCases <;> simp [demandLiterals,DemandPreparation.publicWords,Expr.eval]

private theorem evalGrid (order : Fin d ≃ D) (p : D → ℚ) (rows : Fin t → D → ℚ)
    (pub : Fin 5 → BurstRAM.Word w) (state : BurstRAM.Word w) (m : Memory w) (i : Fin (t*d*3)) :
    (gridLiterals order p rows i).eval pub state m = GridRAM.coefficients order p rows i := by
  unfold gridLiterals GridRAM.coefficients
  dsimp only [Expr.eval]
  split <;> first | rfl | (split <;> rfl)

/-- Planner formulas in exactly the worker's public-operand order. -/
noncomputable def motifExprs (order : Fin d ≃ D) (supply : Fin n ≃ S) (head : Fin 4 → Expr) :
    Fin (motifPass B order n).params → Expr :=
  Fin.append head <| Fin.append
    (Fin.append (demandLiterals order p 1) (gridLiterals order p (DemandGridRAM.fixedRows B))) <|
    Fin.append (demandLiterals order p B.scale)
      (fun i => .lit (MotifAdmission.weight q (supply i) * B.radius.den^2))

theorem eval_motifExprs (order : Fin d ≃ D) (supply : Fin n ≃ S) (head : Fin 4 → Expr)
    (pub : Fin 5 → BurstRAM.Word w) (state : BurstRAM.Word w) (m : Memory w) :
    (fun i => (motifExprs B order supply head i).eval pub state m) =
      motifData B order supply w (fun j => (head j).eval pub state m) := by
  funext i
  change ((Fin.append head (Fin.append (Fin.append (demandLiterals order p 1)
    (gridLiterals order p (DemandGridRAM.fixedRows B))) (Fin.append (demandLiterals order p B.scale)
      (fun i => Expr.lit (MotifAdmission.weight q (supply i) * B.radius.den^2))))) i).eval pub state m =
    (Fin.append (fun j => (head j).eval pub state m)
      (Fin.append (Fin.append (DemandPreparation.publicWords order p 1 w)
        (GridRAM.coefficients order p (DemandGridRAM.fixedRows B)))
        (Fin.append (DemandPreparation.publicWords order p B.scale w)
          (fun j => Fin.ofNat (2^w) (MotifAdmission.weight q (supply j) * B.radius.den^2))))) i
  cases i using Fin.addCases with
  | left i => simp
  | right i =>
    simp only [Fin.append_right]
    cases i using Fin.addCases with
    | left i =>
      simp only [Fin.append_left]
      cases i using Fin.addCases <;> simp [evalDemand,evalGrid]
    | right i =>
      simp only [Fin.append_right]
      cases i using Fin.addCases <;> simp [evalDemand,Expr.eval]

end CompressorRecords.TermWorker

end VPVNP
end Computability
end OAI
