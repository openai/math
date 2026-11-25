import OAI.Hierarchy.TaggedWireWidthRebase

namespace OAI
/-! # A pair of physical site matrices with matching interior widths -/

noncomputable section
namespace Hierarchy.WireTelescope
open LinearAlgebra.SpectralBooks ChordGraph SiteTensor

variable {s : ℕ} {F : Type*} [Field F] {U V W X A B : Widths s}

def Through (first : SiteMatrix (State U) (State V) F) (next : SiteMatrix (State W) (State X) F)
    (gate : SiteMatrix (State A) (State B) F) : Prop :=
  ∃entry : U=A, ∃join : V=W, ∃exit : X=B,
    gate=SiteMatrix.compose (rebase entry join first) (rebase rfl exit next)

theorem Through.relabel {first : SiteMatrix (State U) (State V) F} {next : SiteMatrix (State W) (State X) F}
    {gate : SiteMatrix (State A) (State B) F} (fact : Through first next gate)
    {A' B' : Widths s} (left : A=A') (right : B=B') : Through first next (rebase left right gate) := by
  subst A' B'
  exact fact

end Hierarchy.WireTelescope
end

end OAI
