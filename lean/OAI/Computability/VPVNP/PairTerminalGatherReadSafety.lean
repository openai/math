import OAI.Computability.VPVNP.PairSimulationTerminalRootGatherReads
import OAI.Computability.VPVNP.PairSimulationFieldReadSafety
import OAI.Computability.VPVNP.PairTerminalGatherGeometry

/-! # External read bounds of the terminal root gather

The inverse mate, width and prefix reads all use genuine arc ordinals. Each
bit read lies in its arc's interval in the shared array. When these arrays
end below the terminal header, every read belongs to the worker memory
that agrees between the source execution and its linked replay.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.TerminalGatherGeometry

open BurstRAM BurstRAM.PrivateRAM Compression TerminalRootGather
open scoped Fin.CommRing

variable {a g w : ℕ} {X : State a g} {L : Layout} {u : X.network.Site} {m : Memory w}

/-- The three incidence arrays and the entire shared-bit interval suffice
to locate every individual read performed by the native root gather. -/
theorem worker_readable (num : Numbering X L u) (rows : Rows X L m) (H : Word w)
    (fit : H.val + 31 < 2^w)
    (heads : ∀ head ∈ [L.incomingHead,L.widthHead,L.prefixHead], head + TerminalPrefix.arcCount X ≤ H.val)
    (wires : L.wires + X.totalWidth ≤ H.val) :
    L.Readable m (TerminalLink.workerCell H) := by
  have addressed (d : Bool) (j : Fin (2^a)) : L.edge m d j.val < TerminalPrefix.arcCount X := by
    rw [edge_eq num rows]
    exact (number X _).isLt
  constructor
  · intro j hj
    rw [num.degree] at hj
    apply TerminalLink.workerCell_of_lt fit
    rw [num.index X L ⟨j,hj⟩]
    exact (Nat.add_lt_add_left (number X (u,⟨j,hj⟩)).isLt _).trans_le (heads _ (by simp))
  · intro d j hj
    rw [num.degree] at hj
    exact TerminalLink.workerCell_of_lt fit
      ((Nat.add_lt_add_left (addressed d ⟨j,hj⟩) _).trans_le (heads _ (by simp)))
  · intro d j hj
    rw [num.degree] at hj
    exact TerminalLink.workerCell_of_lt fit
      ((Nat.add_lt_add_left (addressed d ⟨j,hj⟩) _).trans_le (heads _ (by simp)))
  · intro d j hj i hi
    rw [num.degree] at hj
    let k : Fin (2^a) := ⟨j,hj⟩
    apply TerminalLink.workerCell_of_lt fit
    apply (Nat.add_lt_add_left hi _).trans_le
    rw [start_eq num rows d k, width_eq num rows d k, ← slot_width, Nat.add_assoc]
    have bound := EndpointBits.arc_fits (TerminalPrefix.width X) (number X (arc X u d k))
    rw [TerminalPrefix.width_sum] at bound
    exact (Nat.add_le_add_left bound _).trans wires

end PairSimulation.TerminalGatherGeometry

end VPVNP
end Computability
end OAI
