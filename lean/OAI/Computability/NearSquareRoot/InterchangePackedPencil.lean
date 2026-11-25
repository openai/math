import OAI.Computability.NearSquareRoot.InterchangeStageRoute
import OAI.Computability.NearSquareRoot.KernelSwapRepair

/-!
# The shared bank program for a packed binary pencil

Each extension coefficient acts by its multiplication matrix on independent
ground-field rows. The address size and the spectator values can vary while the
clock, coefficient tables, rectangle minor and finite bank script remain fixed.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

noncomputable section
namespace Interchange.PackedPencil

open StageScript OAI.LinearAlgebra.FiniteFourier Matrix SwapSpectrum
open SwapRepair hiding stage

variable {K C Addr L B H : Type} [Field K] {m : ℕ}

abbrev Index (m : ℕ) := Fin (SwapRepair.width m) × BasisIndex m
abbrev ClockPos (m : ℕ) := Fin (clock m) → Fin (order m)
abbrev rowIndex (m : ℕ) := clockShiftRowEquivFin 2 m (order m) (clock m)

/-- Apply one block matrix to packed ground-field components pointwise. -/
noncomputable def mixer
    (A : Pattern m → ClockPos m → ClockPos m → Coeff K m) :
    (Index m → K) →+ (Index m → K) where
  toFun x i :=
    let t := (rowIndex m).symm i.1
    ∑ v, (coefficientMatrix (A t.1 t.2 v) *ᵥ fun d => x (rowIndex m (t.1,v),d)) i.2
  map_zero' := by ext; simp [Matrix.mulVec, dotProduct]
  map_add' x y := by
    ext i
    simp only [Pi.add_apply, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    exact congrFun (Matrix.mulVec_add ..) _

variable [Fintype L] [DecidableEq L] [Fintype B] [Fintype H]
  (r : B → Rectangle L) (I J : H → L)
  (M : Matrix H H K)
  (e : Environment K m)

noncomputable def program : Program (StageRoute.Move r (Fin m) I J) (Index m → K) L L :=
  StageRoute.stage r I J M (mixer e.pencil.A₀) (fun j => mixer (fun β => e.pencil.A β j 1))

/-- Restricting the grouped stage to one fixed spectator fibre gives exactly
the extension-valued pencil at each basis component on that fibre. -/
theorem eval_on_fibre (g : StageRoute.Layout r (Fin m) Addr)
    (hM : (rectangleMatrix (K := K) r).submatrix id J * M *
        (rectangleMatrix r).submatrix I id = rectangleMatrix r)
    (key : Address (Fin m) C → Addr)
    (hswap : ∀ j w a, (g.S j w).symm (g.T j w (key a)) = key (swap j a))
    (X : L → Addr → Index m → K) (w : L) (a : Address (Fin m) C) (t : Index m) :
    eval g.perm (program r I J M e) X w (key a) t =
      components K m (SwapRepair.stage e
        (pack (fun i d a => X w (key a) (i,d))) t.1 a) t.2 := by
  rcases t with ⟨u,d⟩
  obtain ⟨⟨β,u⟩,rfl⟩ := (rowIndex m).surjective u
  rw [program, StageRoute.eval_stage I J g X M hM]
  simp only [hswap, mixer, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Equiv.symm_apply_apply,
    Pi.add_apply, Finset.sum_apply]
  exact (packed_stage_on_block e (fun i d a => X w (key a) (i,d)) β u a d).symm

/-- Composing the same ordinary bank program the required number of times
realizes the predictor, with all intermediate data still in base-field rows. -/
theorem iterate_on_fibre (g : StageRoute.Layout r (Fin m) Addr)
    (hM : (rectangleMatrix (K := K) r).submatrix id J * M *
        (rectangleMatrix r).submatrix I id = rectangleMatrix r)
    (key : Address (Fin m) C → Addr)
    (hswap : ∀ j w a, (g.S j w).symm (g.T j w (key a)) = key (swap j a))
    (X : L → Addr → Index m → K) (w : L) (k : ℕ) :
    pack (fun i d a => (eval g.perm (program r I J M e))^[k] X w (key a) (i,d)) =
      (SwapRepair.stage e)^[k] (pack (fun i d a => X w (key a) (i,d))) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    funext i a
    simp only [Function.iterate_succ_apply']
    apply (components K m).injective
    ext d
    change components K m ((components K m).symm _) d = _
    rw [LinearEquiv.apply_symm_apply]
    dsimp only
    rw [eval_on_fibre r I J M e g hM key hswap]
    rw [ih]

end Interchange.PackedPencil

end

end NearSquareRoot
end Computability
end OAI
