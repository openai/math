import OAI.Hierarchy.ProtocolRAMPurchaseCTShape
import OAI.Hierarchy.ProtocolRAMPurchaseSampler
import OAI.Hierarchy.ProtocolRAMPurchaseTape

namespace OAI
/-! # Storage of the sampler trajectory and its per-tile capacity -/
namespace Hierarchy.ProtocolRAMPurchaseAllocation.Layout
open Computability.VPVNP.BurstRAM PrivateRAM ProbeStage ProtocolRAM
open scoped Fin.CommRing
noncomputable section

def candidates (L : Layout) := PurchaseTape.count L.rows L.degree L.height
def directory (L : Layout) := L.start+ProtocolRAMPurchaseSampler.words L.groups L.sockets L.degree
def signed (L : Layout) : Bank :=
  ⟨L.directory+(L.height+1)*PurchaseDirectory.span L.rows L.degree L.height,
    ProtocolRAMPurchaseSampler.bits (L.rows+1)⟩
def owner (L : Layout) : Bank :=
  ⟨L.signed.base+L.signed.size,ProtocolRAMPurchaseSampler.bits (L.groups*L.sockets)⟩
def scratch (L : Layout) := L.owner.base+L.owner.size
def source (L : Layout) : Bank :=
  ⟨L.scratch+2*L.rows,ProtocolRAMPurchaseSampler.bits ((L.height+1)*L.candidates)⟩
/-- Number of words per tile sufficient at fixed sampler degree, path length and socket density. -/
def linearFactor (K D h : ℕ) :=
  let p := D^h
  let H := h+1
  (4+4*D)*(K+1) + 2*H*(p+1) + 2*(H*p+1) + 15*(p*(4*H+3)+1) + 14+p
end
end Hierarchy.ProtocolRAMPurchaseAllocation.Layout

end OAI
