import OAI.Hierarchy.ProtocolRAMStoredMarkFlags
import OAI.Hierarchy.ProbeRetainedRows
import OAI.Hierarchy.ProbeStripArchive
import OAI.Hierarchy.ProtocolRAMPurchaseMarketResult

namespace OAI
/-! # One injective family of resident affirmative purchase and stock rows -/

noncomputable section
namespace Hierarchy.ProtocolRAM.StripDirectory

open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage PurchaseFrozen
open scoped Classical Fin.CommRing

variable {z d k : ℕ}
local notation "W" => Native.wordBits z d Native.copies

theorem fromRun (sh : Shelf) (S : PurchaseSampler) (π : Equiv.Perm (Fin (2^z))) (depth : ℕ)
    (hd : 1≤d) (phase : PhasePrice) (T : ℝ) (kind : ℕ) (frozen fixture : Shelf.Mem z d)
    (input : sh.Incoming (k:=k) S π depth phase T kind frozen)
    (prepared : ∀ i : Key z d k, sh.Prepared S depth fixture i frozen)
    (room : sh.flagsBase S z d k depth+count z d k*paths z S.degree depth<2^W) :
    StoredFlags sh S π depth phase T kind frozen (sh.result S k depth frozen) k :=
  (sh.run S π depth hd phase T kind frozen fixture input prepared room).2.2.2

theorem liveEmbedding (sh : Shelf) (S : PurchaseSampler) (π : Equiv.Perm (Fin (2^z))) (depth start : ℕ)
    (hk : 0<k) (phase : PhasePrice) (T : ℝ) (kind : ℕ) (frozen m : Shelf.Mem z d)
    (tiles : ∀ key : Key z d k, ProtocolRAMPurchaseGateColumns.TileRows
      (sh.L S depth key).source (Shelf.pathRows S π depth key) m)
    (flags : StoredFlags sh S π depth phase T kind frozen m k)
    (loaded : (stratumHeader z d k S.degree depth start).Loaded m)
    (keys : count z d k≤2^W) (room : (depth+1)*paths z S.degree depth≤2^W)
    (whole : count z d k*paths z S.degree depth≤2^W) (wide : 0<W)
    (stock : PurchaseInventory.footprint z (permutationFabric z d).shapes.length k ≤ 2^W) :
    let header := stratumHeader z d k S.degree depth start
    let marked := actualMarks sh phase T kind frozen (k:=k)
    ∃ pick : LiveChains S π depth marked ↪ Fin header.count, ∀ path,
      (flagBank sh S z d k depth).read m ((pick path).val:Word W) ≠ 0 ∧
      ∀ u : ChainStrip.Axes depth k,
        (allChainSlot (z:=z) (d:=d) sh S depth header u).eval m ((pick path).val:Word W)=
          (PurchaseInventory.slot (stripAddress S π depth marked path u):Word W) := by
  intro header marked
  let keyOf (p : LiveChains S π depth marked) := key p.1 ((PurchaseMarks.signedDirection k).symm p.2.1)
  let index (p : LiveChains S π depth marked) := (retainedStock sh S π depth phase T kind frozen m p tiles room).choose
  let row (p : LiveChains S π depth marked) : Fin header.ports := ⟨(index p).val,by
    simpa [header,stratumHeader,PurchaseFrozen.paths] using (index p).isLt⟩
  let pick (p : LiveChains S π depth marked) := header.enum ⟨keyOf p,row p⟩
  have fields (p : LiveChains S π depth marked) (u : ChainStrip.Axes depth k) :
      (allChainSlot (z:=z) (d:=d) sh S depth header u).eval m ((pick p).val:Word W) =
        (PurchaseInventory.slot (stripAddress S π depth marked p u):Word W) := by
    have split := header_pair header m loaded (keyOf p) (row p)
    exact (allChainSlot_read sh S depth header u m _ (keyOf p) _ keys
      (by rw [split.1,Fin.val_cast_of_lt ((keyOf p).isLt.trans_le keys)]) split.2).trans
      ((retainedStock sh S π depth phase T kind frozen m p tiles room).choose_spec.2 u)
  have injective : Function.Injective pick := by
    intro p q eqn
    let u : ChainStrip.Axes depth k := (0,⟨0,hk⟩,false)
    let get (r : Fin header.count) := (allChainSlot (z:=z) (d:=d) sh S depth header u).eval m (r.val:Word W)
    have nat := congrArg Fin.val ((fields p u).symm.trans ((congrArg get eqn).trans (fields q u)))
    rw [Fin.val_cast_of_lt ((PurchaseInventory.slot_lt _).trans_le stock),
      Fin.val_cast_of_lt ((PurchaseInventory.slot_lt _).trans_le stock)] at nat
    have addr := PurchaseInventory.slot_injective nat
    let emb := allSignedAddresses S π depth marked (actualMarks_unique sh phase T kind frozen)
    have dup : (p,u)=(q,u) := emb.injective addr
    exact congrArg Prod.fst dup
  refine ⟨⟨pick,injective⟩,fun p=>⟨?_,fields p⟩⟩
  let bank := flagBank sh S z d k depth
  have address : (pick p).val = (index p).val + paths z S.degree depth*(keyOf p).val := rfl
  have small : (pick p).val < bank.size := (pick p).isLt.trans (ProtocolRAMPurchaseSampler.lt_span _)
  have narrow : (pick p).val < 2^W := (pick p).isLt.trans_le whole
  change m (bank.base+(((pick p).val:Word W).val%bank.size)) ≠ 0
  have absolute : bank.base+(pick p).val = bank.base+(keyOf p).val*paths z S.degree depth+(index p).val := by
    rw [address,Nat.mul_comm (paths z S.degree depth) (keyOf p).val]
    omega
  rw [Fin.val_cast_of_lt narrow,Nat.mod_eq_of_lt small,absolute]
  have cell := flags (keyOf p) (row p)
  have yes := (retainedStock sh S π depth phase T kind frozen m p tiles room).choose_spec.1
  rw [yes] at cell
  exact fun zero => (of_decide_eq_true (PurchaseStage.decode_flag wide true)) (cell.symm.trans zero)

end Hierarchy.ProtocolRAM.StripDirectory
end

end OAI
