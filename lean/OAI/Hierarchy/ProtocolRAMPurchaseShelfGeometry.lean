import OAI.Hierarchy.ProtocolRAMPurchaseSourceLayout
import OAI.Hierarchy.ProtocolRAMPurchaseKey
import OAI.Hierarchy.ProtocolRAMPurchaseInventory
import OAI.Hierarchy.ProbeAdvisedPurchase

namespace OAI
/-! # Public addresses of the frozen sampler source and decision banks -/
namespace Hierarchy.ProtocolRAM.PurchaseCT
open Computability.VPVNP.BurstRAM PrivateRAM ProbeStage ProbeStage.Native ProtocolRAMPurchaseAllocation
open scoped Fin.CommRing Classical
noncomputable section
variable {z d k : ℕ}
structure PassConfig (k : ℕ) where
  start : ℕ
  depth : ℕ
  first : ℕ
  threshold : Bank
  stock : Fin (2*k) → Bank

abbrev geom (S : PurchaseSampler) (t : StageAt z d) (c : PassConfig k) :=
  allocation t c.start S.degree c.depth c.first
end
end Hierarchy.ProtocolRAM.PurchaseCT

namespace Hierarchy.ProtocolRAM.PurchaseFrozen
open Computability.VPVNP.BurstRAM PrivateRAM ProbeStage ProbeStage.Native ProtocolRAMPurchaseAllocation
open scoped Fin.CommRing Classical
open PurchaseCT
noncomputable section

def factor (d D depth : ℕ) := Layout.linearFactor (4^(rounds d+1)) D depth+1

def blockSize (z d D depth : ℕ) := factor d D depth*2^z

structure Shelf where
  stockBase : ℕ
  thresholdBase : ℕ
  firstBase : ℕ
  tableBits : ℕ

namespace Shelf
variable {z d k : ℕ}

abbrev Mem (z d : ℕ) := Memory (wordBits z d copies)

def table (sh : Shelf) : Bank := ⟨sh.thresholdBase,sh.tableBits⟩

def stock (sh : Shelf) (t : StageAt z d) (j : Fin (2*k)) :=
  PurchaseInventory.bank sh.stockBase z (stageNumber t) j

def lo (sh : Shelf) (S : PurchaseSampler) (depth : ℕ) (i : Key z d k) :=
  sh.firstBase+i.val*blockSize z d S.degree depth

def hi (sh : Shelf) (S : PurchaseSampler) (depth : ℕ) (i : Key z d k) :=
  sh.firstBase+(i.val+1)*blockSize z d S.degree depth

def cfg (sh : Shelf) (S : PurchaseSampler) (depth : ℕ) (i : Key z d k) : PassConfig k :=
  ⟨sh.lo S depth i,depth,0,sh.table,sh.stock (stage i)⟩

abbrev L (sh : Shelf) (S : PurchaseSampler) (depth : ℕ) (i : Key z d k) :=
  geom S (stage i) (sh.cfg S depth i)

def flagsBase (sh : Shelf) (S : PurchaseSampler) (z d k depth : ℕ) :=
  sh.firstBase+count z d k*blockSize z d S.degree depth+2*(paths z S.degree depth+1)


theorem separate (sh : Shelf) (S : PurchaseSampler) (depth : ℕ) {i j : Key z d k} (ne : i≠j) :
    sh.hi S depth i ≤ sh.lo S depth j ∨ sh.hi S depth j ≤ sh.lo S depth i := by
  rcases lt_or_gt_of_ne ne with before|after
  · exact Or.inl (Nat.add_le_add_left (Nat.mul_le_mul_right _ before) _)
  · exact Or.inr (Nat.add_le_add_left (Nat.mul_le_mul_right _ after) _)

theorem final_after (sh : Shelf) (S : PurchaseSampler) (depth : ℕ) (i : Key z d k) :
    sh.hi S depth i ≤ sh.firstBase+count z d k*blockSize z d S.degree depth :=
  Nat.add_le_add_left (Nat.mul_le_mul_right _ i.isLt) _


end Shelf
end
end Hierarchy.ProtocolRAM.PurchaseFrozen

end OAI
