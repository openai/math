import OAI.Computability.BorderVNP.DiagonalSignedReferenceFrame
import OAI.Computability.BorderVNP.CubeScatterReturnedOwnedFamily

/-! # The native reference group's owner on every matching declared selector -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamContraction

open VPVNP BurstRAM Diagonal.Layout Routing RoutingISA RoutingISA.Transmission RoutingISA.Evaluator
open BorderVNP.Cube Physical Scatter Scatter.Assignment SignedPrep TeamRows JointHeader
open private declaredTeam_eq from OAI.Computability.BorderVNP.CubeScatterReturnedOwnedFamily

variable {R r t pins link inner n w : ℕ} {Edge : Type} {G : Wiring R r t pins link inner n Edge}
    {wire : WireLayout (R+1) r link} (ar : CubeArena.Layout) {decl : LengthDeclaration ar.n ar.header.d}
    {header : List Bool} {pin : Fin pins → Bool} {pub : HeaderExterior wire header → Fin (R+1) → Arg → Word w}
    {mac : HeaderExterior wire header → Fin (R+1) → TeamOpcode.Macros w 8}
    {reg : HeaderExterior wire header → Fin (R+1) → Bank w}
    {mem : HeaderExterior wire header → Fin (R+1) → Memory w}
    (F : PreparationFrame G wire ar decl header pin pub mac reg mem)
    {A : Type*} [Fintype A] (label : Fin ar.cells → Label (ar.n+1) ar.header.d)
    (recv : A → Fin ar.cells) (width : A → ℕ)

local notation "who" => greedyOwner R ar.b ar.s label recv width

/-- The declaration stored in the reference frame suffices to identify the
group on every routed selector in its fibre: the field may vary across
declarations, while the selector may vary within one declaration. -/
theorem PreparationFrame.groupMap (scheduled : F.group=declaredTeam ar decl label recv width R)
    (q : Declared ar who decl) : F.group=who q.val.1 := by
  have shape : Routed.trueDeclaration ar.b ar.s q.val.1=decl := q.property
  have owner := declaredTeam_eq (R:=R) ar (Routed.trueDeclaration ar.b ar.s q.val.1) label recv width
    (Routed.physicalShared who q.val)
  exact scheduled.trans ((congrArg (fun d => declaredTeam ar d label recv width R) shape).symm.trans owner)

/-- Read the actual group numbers in the installed reference RAM and use
the native scheduler's image of the advertised rows. This identifies the
owner on the exact selected routed tuple before using a post-call receipt. -/
theorem PreparationFrame.groupMap_of_stored {head : ℕ} {before after : ℕ → ℕ}
    (result : GroupWeights.ScheduleResult (LocalRow.weightLayout ar head decl.1.val)
      (LocalRow.teamLayout ar R) before after)
    (image : GroupWeights.PhysicalImage (LocalRow.weightLayout ar head decl.1.val) before ar.header.blocks ar.b
      ar.K ar.h decl label recv width)
    (stored : ∀ g : Fin ar.header.d, after (ar.ownerBase+g.val)=(F.group g).val)
    (q : Declared ar who decl) : F.group=who q.val.1 := by
  apply F.groupMap ar label recv width _ q
  exact declared_owner_of_native_schedule result decl label recv width image F.group stored

end TeamContraction

end BorderVNP
end Computability
end OAI
