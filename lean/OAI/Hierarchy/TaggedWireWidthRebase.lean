import OAI.Hierarchy.TaggedWireSiteMatrix

namespace OAI
/-! # Transport of a site matrix along two equal width ledgers -/
noncomputable section
namespace Hierarchy.WireTelescope
open LinearAlgebra.SpectralBooks ChordGraph SiteTensor

def rebase {K : ℕ} {F : Type*} {A B U V : Widths K} (old : A=B) (new : U=V)
    (M : SiteMatrix (State A) (State U) F) : SiteMatrix (State B) (State V) F := old ▸ new ▸ M

theorem rebase_action {K : ℕ} {F : Type*} [Field F] {A B U V : Widths K} (old : A=B) (new : U=V)
    (M : SiteMatrix (State A) (State U) F)
    (base : ∀x,(raw F A).coeff x=SiteMatrix.act M (raw F U).coeff x)
    (x : ∀i,State B i) : (raw F B).coeff x=SiteMatrix.act (rebase old new M) (raw F V).coeff x := by
  subst B
  subst V
  exact base x

end Hierarchy.WireTelescope

end
end OAI
