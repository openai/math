import OAI.Computability.BorderVNP.DiagonalTaggedStep
import OAI.Computability.BorderVNP.ShortenRetable

/-! # Tagged tables after specialization on fixed reference-field geometry

The selected bin, seed orientations, interval order and profile indices are
those already chosen by the geometric step over the reference field. The
finite-field entries are then read at their true positions in the joint
gadget table. This lets the geometric constants precede the prime used by
the diagonal argument in characteristic zero.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal.CellEntries.Tracked

open Crossing Shortening Packing PlacedStep
open scoped BigOperators Classical

set_option maxHeartbeats 2000000

variable {D m k l next exp : ℕ} [NeZero D] {P I B : Type} [Fintype I] [Fintype B]
    {bits : P → ℕ} {Team Param Gadget K E : Type*} [Fintype Team] [Fintype Param]
    [Field K] [Field E] (e : PaidIdentity K D m) (y : e.Entry → E)
    (hy : ∀ f : MvPolynomial e.Entry ℤ, MvPolynomial.eval₂Hom (Int.castRingHom K) e.entry f = 0 →
      MvPolynomial.eval₂Hom (Int.castRingHom E) y f = 0)
    (pos : e.Entry → Gadget) {child : Fin k → PlacedPack D P bits K I l}
    (step : PlacedStep m B next child) (input : ∀ i, Tracked Team Param Gadget exp (child i).pack.layout)

/-- Apply the specialized profile identity at exactly the chosen public move.
The temporary scalar tables only fix the type of the geometry. The actual
private tags and original power words are supplied by `input`. -/
noncomputable def specializedOutput (q : step.Index e) :
    Tracked (Fin k × Team) Param Gadget exp (step.result e q).pack.layout :=
  output (e.specialize y hy) pos (step.retable fun _ _ _ _ => (0:E)) input q

/-- Over the selected scalar field, the reference-field histograms expand
the product exactly, including all choices whose weight specializes to zero. -/
theorem sum_specializedOutput (values : Gadget → E) (lookup : ∀ i, values (pos i) = y i)
    (x : Ports fun z : Fin k × P => bits z.2) :
    (∏ i, ((input i).valued values).tensor (fun p => x (i,p))) =
      ∑ q : step.Index e, ((specializedOutput e y hy pos step input q).valued values).tensor x :=
  sum_output (e.specialize y hy) pos (step.retable fun _ _ _ _ => (0:E)) input values lookup x

end Diagonal.CellEntries.Tracked

end BorderVNP
end Computability
end OAI
