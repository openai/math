import OAI.Hierarchy.DescentDistinctPrivateKey
import OAI.Hierarchy.DescentHaloAtSource

namespace OAI
/-! The physical ordinary capture slot counts true visits at the source host. -/
namespace Hierarchy.DescentOrdinaryNativeNames
open DescentPackedOperand DescentCableDonorNames DescentHostDirectory
open scoped Classical
noncomputable section
variable {U:Type}
section Measured
open DescentHaloWalkRAM DescentHaloCompilation DescentOrdinaryDonorHalo DescentColonies DescentHostDegree
variable {J V C:Type} [Fintype U] [DecidableEq J] [DecidableEq V] {H D k B:ℕ}
    (near:V→Finset V) (name:V↪Fin H) (roster:Fin H→Fin D→Option (Fin H))
    (listed:∀u v,v∈near u→∃j,roster (name u) j=some (name v))
    (pos:U→J×V) (blk:U→Block k) (unique:Function.Injective fun u=>(pos u,blk u))
    (whereAt:C→DescentHostDirectory.Key (J×V)) (resident:Halo C U B)
    (members:∀c,resident.member c=siteSet (groupedNear near) pos (whereAt c))
local notation "sparse" => atSource near name roster listed pos blk unique whereAt

private def sameMembers (c:C) : ↥(resident.member c)↪ ↥(siteSet (groupedNear near) pos (whereAt c)) :=
  ⟨fun u=>⟨u.val,Eq.mp (congrArg (fun sites : Finset U=>u.val∈sites) (members c)) u.property⟩,
    fun _ _ eqn=>Subtype.ext (congrArg (fun t : ↥(siteSet (groupedNear near) pos (whereAt c)) => t.val) eqn)⟩

def measured (c:C) : ℕ↪ℕ :=
  donorEmbedding (resident.slot c) ((sameMembers near pos whereAt resident members c).trans ((sparse).slot c))

theorem measured_at (c:C) (u:U) (presence:u∈resident.member c) :
    measured near name roster listed pos blk unique whereAt resident members c ((resident.slot c) ⟨u,presence⟩).val=
      ((sparse).slot c ⟨u,Eq.mp (congrArg (fun sites : Finset U=>u∈sites) (members c)) presence⟩).val :=
  renumber_at (resident.slot c) ((sameMembers near pos whereAt resident members c).trans ((sparse).slot c))
    ⟨u,presence⟩

theorem same_receiver {a b:DescentHostDirectory.Key (J×V)} (common:a.1=b.1)
    (u:U) (ma:u∈siteSet (groupedNear near) pos a) (mb:u∈siteSet (groupedNear near) pos b) :
    ((shared near name roster listed pos blk unique).slot a ⟨u,ma⟩).val=
      ((shared near name roster listed pos blk unique).slot b ⟨u,mb⟩).val :=by
  rcases a with ⟨a,aa⟩
  rcases b with ⟨b,bb⟩
  cases common
  rfl

end Measured
end
end Hierarchy.DescentOrdinaryNativeNames

end OAI
