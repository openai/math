import OAI.Hierarchy.ProtocolRAMCalendarFrozen
import OAI.Hierarchy.ProtocolRAMPurchaseMarketCausality
import OAI.Hierarchy.TaggedWireCalendarReads

namespace OAI
/-! # Causality of the native price and all-sign purchase prefix -/

noncomputable section
namespace Hierarchy.WireTelescope.ReadBanks
open ProtocolRAM ProtocolRAM.Calendar ProtocolRAM.PurchaseFrozen
open Computability.VPVNP.BurstRAM PrivateRAM ProbeStage ProbeStage.Native PurchaseCT ProtocolRAMPurchaseAllocation
open ThreeFlat.RAM
open scoped Classical Fin.CommRing
variable {z d k : ℕ}

/-- Live addresses after the exact frozen program. It exposes all its
decision and leftover columns; temporary DFS words have no outgoing uses. -/
def MarketLive (v : Market z d k) (future : ℕ→Prop) (a : ℕ) : Prop :=
  ((¬future a ∧ (a<v.shelf.firstBase ∨ v.flags+v.rows≤a ∨
    ∃ i : Key z d k,v.shelf.romAddress v.sampler v.depth i a)) ∨
    v.shelf.Published v.sampler z d k v.depth a)

/-- Re-evaluating the physical purchase prefix after changing only future
histogram words leaves all consumed columns unchanged. -/
theorem market_observed (v : Market z d k) (π : Equiv.Perm (Fin (2^z))) (hd : 1≤d)
    (m m' fixture fixture' : Shelf.Mem z d) (future : ℕ→Prop)
    (same : Agree future m m') (fails : NoFuture future v.failures.pass.term)
    («public» : ∀ (t : StageAt z d) (r : Fin (2^z)) (a : Fin k × Bool),¬future (v.shelf.stockAddress t r a))
    (incoming : v.shelf.Incoming (k:=k) v.sampler π v.depth v.phase v.temperature v.kind (v.failures.pass.apply m))
    (incoming' : v.shelf.Incoming (k:=k) v.sampler π v.depth v.phase v.temperature v.kind (v.failures.pass.apply m'))
    (rom : ∀ i : Key z d k,v.shelf.Prepared v.sampler v.depth fixture i (v.failures.pass.apply m))
    (rom' : ∀ i : Key z d k,v.shelf.Prepared v.sampler v.depth fixture' i (v.failures.pass.apply m'))
    (room : v.flags+v.rows<2^wordBits z d copies) :
    ∀a,MarketLive v future a→v.prefix.after m a=v.prefix.after m' a := by
  have prior : Agree future (v.failures.pass.apply m) (v.failures.pass.apply m') :=
    scan _ _ _ same fails
  have result := v.shelf.result_control v.sampler π v.depth hd v.phase v.temperature v.kind
    (v.failures.pass.apply m) (v.failures.pass.apply m') fixture fixture'
    incoming incoming' rom rom' room (v.shelf.sameStock_of_agree prior «public»)
  exact result.observed_with_rom prior

end Hierarchy.WireTelescope.ReadBanks

end
end OAI
