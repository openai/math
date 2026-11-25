import OAI.Hierarchy.ProtocolRAMPurchaseSampler
import OAI.Hierarchy.TaggedShorterPathPorts

namespace OAI
/-! # Static reverse digits for reconstructing purchased sampler paths -/

namespace Hierarchy.ProtocolRAMPurchaseSampler
open Computability.VPVNP.BurstRAM PrivateRAM ProbeStage
open ThreeFlat.RAM PhysicalProcedure
open scoped Fin.CommRing

variable {w m D : ℕ}

/-- Both directions of the purchased-path directory are fixed by the chosen sampler. -/
noncomputable def mount (base groups : ℕ) (next : Fin m → List (Fin m))
    (col : ∀ i,(TaggedShorterPathPorts.incoming next i).card ≤ D) (mem : Memory w) :=
  install base groups next (TaggedShorterPathPorts.backCode next col) mem

theorem backCode_resident (base groups : ℕ) (next : Fin m → List (Fin m))
    (col : ∀ i,(TaggedShorterPathPorts.incoming next i).card ≤ D)
    (mem : Memory w) (room : m≤2^w) (j : Fin D) :
    Native.Resident (backward base groups m D j) (mount base groups next col mem)
      (fun o => (TaggedShorterPathPorts.backCode next col o j).val) :=
  reverse_resident base groups next _ mem room j

end Hierarchy.ProtocolRAMPurchaseSampler

end OAI
