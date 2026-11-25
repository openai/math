import OAI.Hierarchy.ProtocolRAMPurchaseSignedDispatch
import OAI.Hierarchy.ProtocolRAMPurchaseShelfUpper
import OAI.Hierarchy.ProtocolRAMPurchaseRuntimeOperands

namespace OAI
/-! # Decision-bank addresses and word bounds on the executing purchase shelf -/

namespace Hierarchy.ProtocolRAM.PurchaseFrozen
open Computability.VPVNP.BurstRAM PrivateRAM ProbeStage ProbeStage.Native PurchaseCT ProtocolRAMPurchaseAllocation Filter
open scoped Fin.CommRing Classical
noncomputable section

namespace Shelf
variable {z d k : ℕ}

abbrev desc (sh : Shelf) (S : PurchaseSampler) (depth : ℕ) (i : Key z d k) :=
  let t := stage i
  let c := sh.cfg S depth i
  PurchaseStage.layout (embedded S t c) (sign S t c) (2^z) depth

def flagBank (sh : Shelf) (S : PurchaseSampler) (depth : ℕ) (i : Key z d k) : Bank :=
  ⟨PurchaseStage.decisionBase (sh.desc S depth i),ProtocolRAMPurchaseSampler.bits (paths z S.degree depth)⟩

theorem source_fit (sh : Shelf) (S : PurchaseSampler) (depth : ℕ) (i : Key z d k) (hd : 1≤d)
    (space : sh.flagsBase S z d k depth+count z d k*paths z S.degree depth<2^wordBits z d copies) :
    (sh.flagBank S depth i).Fits (wordBits z d copies) (sh.flagsBase S z d k depth) := by
  have capacity := ProtocolRAMPurchaseSampler.span_le (paths z S.degree depth)
  have slab := (sh.end_le S depth i hd).trans (sh.final_after S depth i)
  have addr : PurchaseStage.decisionBase (sh.desc S depth i)≤(sh.L S depth i).endAddress := Nat.le_add_right ..
  change 0<2^_ ∧ ProtocolRAMPurchaseSampler.span _<2^_ ∧
    PurchaseStage.decisionBase (sh.desc S depth i)+ProtocolRAMPurchaseSampler.span _≤_
  dsimp only [flagsBase] at space ⊢
  exact ⟨Nat.two_pow_pos _,by omega,by omega⟩

theorem ready (sh : Shelf) (S : PurchaseSampler) (depth : ℕ) (i : Key z d k) (hd : 1≤d)
    (heap : heapEnd z d copies ≤ sh.thresholdBase) (raw : 2^z ≤ sh.thresholdBase)
    (stocks : ∀ j : Fin (2*k),heapEnd z d copies≤(sh.stock (stage i) j).base ∧
      (sh.stock (stage i) j).Fits (wordBits z d copies) sh.thresholdBase)
    (tableFits : sh.table.Fits (wordBits z d copies) sh.firstBase)
    (ct : (allocation (stage i) sh.firstBase S.degree depth 0).CTFits (banks (stage i)) (wordBits z d copies))
    (wide : 0<wordBits z d copies) (directions : 2*k<2^wordBits z d copies)
    (degree : S.degree≤2^wordBits z d copies) (sockets : (stageAt z d (stage i)).span≤2^wordBits z d copies)
    (space : sh.flagsBase S z d k depth+count z d k*paths z S.degree depth<2^wordBits z d copies) :
    Ready S (stage i) (sh.cfg S depth i) := by
  have head : sh.firstBase ≤ sh.lo S depth i := Nat.le_add_right ..
  have enlarge {b : Bank} (old : b.Fits (wordBits z d copies) sh.firstBase) :
      b.Fits (wordBits z d copies) (sh.lo S depth i) := ⟨old.1,old.2.1,old.2.2.trans head⟩
  have bound := (sh.end_le S depth i hd).trans (sh.final_after S depth i)
  change sh.firstBase+count z d k*blockSize z d S.degree depth+2*(paths z S.degree depth+1)+
    count z d k*paths z S.degree depth<2^wordBits z d copies at space
  exact ⟨heap,raw,stocks,enlarge tableFits,⟨enlarge ct.group,enlarge ct.input,enlarge ct.output⟩,
    wide,directions,degree,sockets,by change (sh.L S depth i).endAddress<_; omega⟩

end Shelf
end
end Hierarchy.ProtocolRAM.PurchaseFrozen

end OAI
