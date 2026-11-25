import OAI.Hierarchy.ProtocolRAMPortRanks

namespace OAI
/-! # The permutation implemented by least-significant-key-first terminal sorting -/

namespace Hierarchy.DescentTerminalSortRAM

open Computability.BorderVNP.FragmentBucket

variable {N A E O S : ℕ}

/-- The current array maps sorted positions to original immutable records. -/
def perm (old : Fin N≃Fin N) (key : Fin N→Fin A) : Fin N≃Fin N :=
  (dest (fun i=>key (old i))).symm.trans old

def order (edge : Fin N→Fin E) (ordinal : Fin N→Fin O) (side : Fin N→Fin S) :=
  perm (perm (perm (Equiv.refl _) side) ordinal) edge

end Hierarchy.DescentTerminalSortRAM

end OAI
