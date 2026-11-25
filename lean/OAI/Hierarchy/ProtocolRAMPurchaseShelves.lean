import OAI.Hierarchy.ProtocolRAMPurchaseShelfBanks
import OAI.Hierarchy.ProtocolRAMPurchaseFrozenLayout

namespace OAI
/-! # A frozen purchase sweep at caller-specified addresses -/

namespace Hierarchy.ProtocolRAM.PurchaseFrozen
open Computability.VPVNP.BurstRAM PrivateRAM ProbeStage ProbeStage.Native PurchaseCT ProtocolRAMPurchaseAllocation Filter
open scoped Fin.CommRing Classical
noncomputable section

namespace Shelf
variable {z d k : ℕ}

def canonical (z d k extra : ℕ) : Shelf :=
  ⟨heapEnd z d copies,heapEnd z d copies+PurchaseInventory.footprint z (2*rounds d+1) k,
    PurchaseFrozen.firstBase z d k extra,z+extra⟩

@[simp] theorem canonical_lo (S : PurchaseSampler) (extra depth : ℕ) (i : Key z d k) :
    (canonical z d k extra).lo S depth i=start S extra depth i := rfl

@[simp] theorem canonical_hi (S : PurchaseSampler) (extra depth : ℕ) (i : Key z d k) :
    (canonical z d k extra).hi S depth i=stop S extra depth i := rfl

@[simp] theorem canonical_cfg (S : PurchaseSampler) (extra depth : ℕ) (i : Key z d k) :
    (canonical z d k extra).cfg S depth i=config S extra depth i := rfl

@[simp] theorem canonical_L (S : PurchaseSampler) (extra depth : ℕ) (i : Key z d k) :
    (canonical z d k extra).L S depth i=board S extra depth i := rfl

@[simp] theorem canonical_desc (S : PurchaseSampler) (extra depth : ℕ) (i : Key z d k) :
    (canonical z d k extra).desc S depth i=PurchaseFrozen.desc S extra depth i := rfl

@[simp] theorem canonical_flagsBase (S : PurchaseSampler) (z d k extra depth : ℕ) :
    (canonical z d k extra).flagsBase S z d k depth=PurchaseFrozen.flagsBase S z d k extra depth := rfl

@[simp] theorem canonical_flagBank (S : PurchaseSampler) (extra depth : ℕ) (i : Key z d k) :
    (canonical z d k extra).flagBank S depth i=PurchaseFrozen.flagBank S extra depth i := rfl

theorem canonical_ready (S : PurchaseSampler) (d k extra depth : ℕ) (hd : 1≤d) :
    ∀ᶠ z : ℕ in atTop, ∀ i : Key z d k, Ready S (stage i) ((canonical z d k extra).cfg S depth i) :=
  PurchaseFrozen.ready S d k extra depth hd

end Shelf
end
end Hierarchy.ProtocolRAM.PurchaseFrozen

end OAI
