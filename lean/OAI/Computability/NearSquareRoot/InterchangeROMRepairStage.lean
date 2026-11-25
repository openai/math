import OAI.Computability.NearSquareRoot.InterchangeROMRepairApply
import OAI.Computability.NearSquareRoot.InterchangeStageRoute

/-! # Grouped rectangle routing for a serialized repair table -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace InterchangeROMRepair

open Interchange Matrix StageScript SwapSpectrum

variable {R V U L B H Addr C : Type} [Field R] [Fintype V]
  [DecidableEq L] [Fintype L] [Fintype B] [Fintype H] {m : ℕ}
variable (r : B → Rectangle L) (I J : H → L)

/-- The pointwise row operator emitted for a ground-field matrix. -/
def mixerMap (A : Matrix V V R) : (V → R) →+ (V → R) where
  toFun := A.mulVec
  map_zero' := Matrix.mulVec_zero _
  map_add' := Matrix.mulVec_add _

/-- The rectangle bank uses exactly one shared row operator for each pencil term. -/
noncomputable def stageBank (t : Spec R V U m) (M : Matrix H H R) :
    Program (StageRoute.Move r (Fin m) I J) (V → R) L L :=
  StageRoute.stage r I J M (mixerMap t.base) (fun j => mixerMap (t.term j))

theorem stageBank_eval (t : Spec R V U m) (M : Matrix H H R)
    (hM : (rectangleMatrix (K := R) r).submatrix id J * M *
        (rectangleMatrix r).submatrix I id = rectangleMatrix r)
    (g : StageRoute.Layout r (Fin m) Addr) (key : Address (Fin m) C → Addr)
    (hswap : ∀ j w a, (g.S j w).symm (g.T j w (key a)) = key (swap j a))
    (X : L → Addr → V → R) (w : L) :
    (fun i a => eval g.perm (stageBank r I J t M) X w (key a) i) =
      pencil t (fun i a => X w (key a) i) := by
  funext i a
  rw [stageBank, StageRoute.eval_stage I J g X M hM]
  simp only [pencil, mix, mixerMap, hswap, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
    Matrix.mulVec, dotProduct, swapRow, Pi.add_apply, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul]

theorem stageBank_iterate (t : Spec R V U m) (M : Matrix H H R)
    (hM : (rectangleMatrix (K := R) r).submatrix id J * M *
        (rectangleMatrix r).submatrix I id = rectangleMatrix r)
    (g : StageRoute.Layout r (Fin m) Addr) (key : Address (Fin m) C → Addr)
    (hswap : ∀ j w a, (g.S j w).symm (g.T j w (key a)) = key (swap j a))
    (X : L → Addr → V → R) (w : L) (order : ℕ) :
    (fun i a => (eval g.perm (stageBank r I J t M))^[order] X w (key a) i) =
      (pencil t)^[order] (fun i a => X w (key a) i) := by
  induction order with
  | zero => rfl
  | succ k ih =>
    simp only [Function.iterate_succ_apply']
    rw [← ih]
    apply stageBank_eval r I J t M hM g key hswap

end InterchangeROMRepair

end NearSquareRoot
end Computability
end OAI
