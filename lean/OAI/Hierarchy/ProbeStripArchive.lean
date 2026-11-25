import OAI.Hierarchy.ProbePurchasedOccurrence
import OAI.Hierarchy.ProtocolRAMCalendarSegments

namespace OAI
/-! # The archived purchase geometry read by a later inner attempt -/

noncomputable section
open scoped Fin.CommRing
namespace Hierarchy.ProtocolRAM.StripDirectory

open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage PurchaseFrozen
open scoped Classical

variable {z d k q goods : ℕ}
local notation "W" => Native.wordBits z d Native.copies

/-- Transport an archived ordinary bank through the actual scheduled
inner attempts and preceding reserve feeds. Only the bytes of that bank
need protection. -/
theorem archivedBank (C : Calendar.Chart W q goods) (mem : Memory W) (p h j b : ℕ)
    (bank : Bank) (ready : Calendar.mounted C (Calendar.purchaseTail C.mesh p h j b)
      (Calendar.reserveState C mem p h 0))
    (safe : ∀ x,bank.base≤x → x<bank.base+bank.size →
      ∀ e∈Calendar.purchaseTail C.mesh p h j b,Calendar.protected C x e) (i : Word W) :
    bank.read (Calendar.innerState C mem p h j b) i =
      bank.read (Calendar.reserveState C mem p h 0) i := by
  apply Calendar.purchase_archive C mem p h j b _ ready
  exact safe _ (Nat.le_add_right ..) (Nat.add_lt_add_left (Nat.mod_lt _ (Nat.two_pow_pos _)) _)

/-- Every surviving current board row reads from the preceding outer
acquisition's actual trajectory columns. No new geometric table is
installed by the current inner market. -/
theorem retainedInner (C : Calendar.Chart W q goods) (mem : Memory W) (p h j b : ℕ)
    (sh : Shelf) (S : PurchaseSampler) (π : Equiv.Perm (Fin (2^z))) (depth start : ℕ)
    (phase : PhasePrice) (T : ℝ) (kind : ℕ) (frozen : Shelf.Mem z d)
    (path : LiveChains S π depth (actualMarks sh phase T kind frozen (k:=k)))
    (initial : ∀ key : Key z d k, sh.PortData S π depth key (Calendar.reserveState C mem p h 0))
    (stored : (stratumHeader z d k S.degree depth start).Loaded (Calendar.reserveState C mem p h 0))
    (ready : Calendar.mounted C (Calendar.purchaseTail C.mesh p h j b) (Calendar.reserveState C mem p h 0))
    (protectSource : ∀ key : Key z d k, ∀ x, let s := (sh.L S depth key).source
      s.base≤x → x<s.base+s.size → ∀ e∈Calendar.purchaseTail C.mesh p h j b,Calendar.protected C x e)
    (protectHeader : ∀ x, let head := stratumHeader z d k S.degree depth start
      head.start≤x → x<head.stop → ∀ e∈Calendar.purchaseTail C.mesh p h j b,Calendar.protected C x e)
    (keys : count z d k ≤ 2^W) (room : (depth+1)*paths z S.degree depth≤2^W) :
    let header := stratumHeader z d k S.degree depth start
    ∃ r : Fin header.count, ∀ u : ChainStrip.Axes depth k,
      (allChainSlot (z:=z) (d:=d) sh S depth header u).eval (Calendar.innerState C mem p h j b)
        (r.val:Word W) =
      (PurchaseInventory.slot (stripAddress S π depth (actualMarks sh phase T kind frozen) path u) : Word W) := by
  apply retainedBoardTiles sh S π depth start phase T kind frozen _ path _ _ keys room
  · intro key i pos
    let source := (sh.L S depth key).source
    let rows := (PurchaseDFS.layout (2^z) S.degree depth).length
    have size : (depth+1)*rows ≤ source.size := (ProtocolRAMPurchaseSampler.lt_span _).le
    have base := Nat.mul_le_mul_right rows pos.isLt
    rw [Nat.succ_mul] at base
    have bound : pos.val*rows+i.val<source.size := by
      have hrow : i.val<rows := i.isLt
      omega
    exact (Calendar.purchase_archive C mem p h j b _ ready
      (protectSource key _ (Nat.le_add_right ..) (Nat.add_lt_add_left bound _))).trans ((initial key).tiles i pos)
  · apply stored.frame
    intro x low high
    exact Calendar.purchase_archive C mem p h j b x ready (protectHeader x low high)

end Hierarchy.ProtocolRAM.StripDirectory
end

end OAI
