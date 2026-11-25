import OAI.LinearAlgebra.SpectralBooks.PortGraph.PlanarPortRotation
import Mathlib.GroupTheory.Perm.Fin

/-! # The rotation obtained by reading port numbers cyclically -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

namespace PortGraph

open Equiv Equiv.Perm HyperbolicObstruction.PictureSwitch

variable {V E : Type*} [DecidableEq V] [Fintype E] (G : PortGraph V E)

/-- The ports at each vertex are numbered consecutively, starting from zero. -/
abbrev Numbering := (v : V) → G.Port v ≃ Fin (Fintype.card (G.Port v))

namespace Numbering

variable {G} (num : G.Numbering)

/-- The next local port number, with wrapping at the last port. -/
def successor (v : V) : Perm (G.Port v) := (num v).symm.permCongr (finRotate _)

private def groupPorts : (Σ v, G.Port v) ≃ E × Bool :=
  Equiv.sigmaFiberEquiv (fun p : E × Bool => G.vertex p.1 p.2)

/-- Apply the cyclic successor in the appropriate vertex fiber. -/
def turn : Perm (E × Bool) :=
  (groupPorts (G := G)).permCongr (Equiv.sigmaCongrRight num.successor)

theorem turn_port {v : V} (p : G.Port v) : num.turn p.val = (num.successor v p).val := by
  rcases p with ⟨p, rfl⟩
  rfl

private theorem finRotate_sameCycle {n : ℕ} (a b : Fin n) : (finRotate n).SameCycle a b := by
  cases n with
  | zero => exact Fin.elim0 a
  | succ n =>
    cases n with
    | zero => exact (show a = b by apply Fin.ext; omega).sameCycle _
    | succ n => exact isCycle_finRotate.sameCycle (by simp) (by simp)

/-- The cyclic order obtained from port numbers has precisely the vertex fibers as cycles. -/
def rotation : G.Rotation where
  turn := num.turn
  sameCycle := by
    intro a b
    constructor
    · intro h
      apply sameCycle_one.mp (semiconj_perm_sameCycle (t := (1 : Perm V))
        (j := fun p => G.vertex p.1 p.2) ?_ h)
      intro p
      have ht := num.turn_port (⟨p, rfl⟩ : G.Port (G.vertex p.1 p.2))
      change G.vertex (num.turn p).1 (num.turn p).2 = G.vertex p.1 p.2
      rw [ht]
      exact (num.successor _ ⟨p, rfl⟩).property
    · intro h
      let v := G.vertex a.1 a.2
      let f : Fin (Fintype.card (G.Port v)) → E × Bool := fun i => ((num v).symm i).val
      have hh : ∀ i, f (finRotate _ i) = num.turn (f i) := by
        intro i
        rw [show num.turn (f i) = _ from num.turn_port ((num v).symm i)]
        simp [f, successor]
      have t := semiconj_perm_sameCycle hh
        (finRotate_sameCycle (num v ⟨a, rfl⟩) (num v ⟨b, h.symm⟩))
      simpa [f] using t

end Numbering
end PortGraph

end SpectralBooks
end LinearAlgebra
end OAI
