import OAI.Hierarchy.DescentResetCandidatePair

namespace OAI
/-! # Change the finite notation for the measured candidate sheets -/
namespace Hierarchy.DescentResetCandidatePair
open ProtocolRAM Computability.VPVNP.BurstRAM
variable {w X s c p X' s' c' p' : ℕ} (hx : X=X') (hs : s=s') (hc : c=c') (hp : p=p')
  (src : Inputs X s c p)

def shaped : Inputs X' s' c' p' :=by subst X';subst s';subst c';subst p';exact src

theorem shaped_fits (cut : ℕ) (ready : ∀x j,(src x j).Fits w cut) :
    ∀x j,((shaped hx hs hc hp src) x j).Fits w cut:=by
  subst X';subst s';subst c';subst p'
  exact ready

theorem shaped_memory (orig : Inputs X s c p) (start bits : ℕ) {H G M H' G' M' : ℕ}
    (h : H=H') (g : G=G') (l : M=M') (m : Memory w) :
    memory start bits H G M src orig m=
      memory start bits H' G' M' (shaped hx hs hc hp src) (shaped hx hs hc hp orig) m:=by
  subst X';subst s';subst c';subst p';subst H';subst G';subst M'
  rfl

end Hierarchy.DescentResetCandidatePair

end OAI
