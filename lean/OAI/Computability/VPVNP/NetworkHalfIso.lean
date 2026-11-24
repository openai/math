import OAI.Computability.VPVNP.NetworkIso

/-!
# Half-wire coordinates under network relabelling

In a placed expansion, changing the coordinates of the input network gives
a bijection on the independent half-wire assignments at each old site. The
same expansion can then use the original output network for each choice.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace NetworkKernel

namespace Network.Iso

variable {N M : Network}

/-- Relabel each site, edge and payload by its identity map. -/
def refl (N : Network) : N.Iso N where
  site := Equiv.refl _
  edge := Equiv.refl _
  src _ := rfl
  dst _ := rfl
  payload _ := Equiv.refl _

/-- Pulling the half-wire indices back to an original site is a bijection. -/
def pullHalfEquiv (f : N.Iso M) (u : N.Site) : M.Half (f.site u) ≃ N.Half u where
  toFun := f.pullHalf u
  invFun a :=
    ⟨Equiv.piCongrLeft (fun e ↦ f.site u = M.src e → M.Payload e) f.edge
        (fun e h ↦ f.payload e (a.1 e (f.site.injective (h.trans (f.src e).symm)))),
     Equiv.piCongrLeft (fun e ↦ f.site u = M.dst e → M.Payload e) f.edge
        (fun e h ↦ f.payload e (a.2 e (f.site.injective (h.trans (f.dst e).symm))))⟩
  left_inv a := by
    apply Prod.ext <;> funext e h <;> obtain ⟨x, rfl⟩ := f.edge.surjective e <;>
      simp only [pullHalf, Equiv.piCongrLeft_apply_apply, Equiv.apply_symm_apply]
  right_inv a := by
    apply Prod.ext <;> funext e h <;>
      simp only [pullHalf, Equiv.piCongrLeft_apply_apply, Equiv.symm_apply_apply]

end Network.Iso

variable {k : Type*} [CommSemiring k] {N M : Network}

/-- Reindex the input of an exact step, retaining its chosen output for every term. -/
noncomputable def Step.reindexInput (s : Step k N) (input : N.Iso M) : Step k M :=
  s.reindex input fun i ↦ Network.Iso.refl (s.term i).output

/-- An input reindexing retains the output network at each choice. -/
@[simp] theorem Step.reindexInput_term_output (s : Step k N) (input : N.Iso M) (i : s.Choice) :
    ((s.reindexInput input).term i).output = (s.term i).output := rfl

end NetworkKernel

end VPVNP
end Computability
end OAI
