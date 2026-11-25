import OAI.Hierarchy.ProbeRetainedLive
import OAI.Hierarchy.ProtocolRAMPurchaseLiveCount

namespace OAI
/-! # Exact correspondence between active replay records and the bought typed paths -/

namespace Hierarchy.ProtocolRAM.StripDirectory
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage ProbeStage.Native PurchaseFrozen
open scoped BigOperators Fin.CommRing Classical
noncomputable section

private theorem true_count : ∀ {n : ℕ} (a : Fin n→Bool),
    (List.ofFn a).count true=∑ i,if a i=true then 1 else 0 := by
  intro n; induction n with
  | zero => intro a; simp
  | succ n ih =>
    intro a
    rw [List.ofFn_succ,Fin.sum_univ_succ,List.count_cons,ih]
    cases val : a 0 <;> simp [Nat.add_comm]

variable {z d k : ℕ}
local notation "W" => wordBits z d copies

/-- Count the literal nonzero flag-bank rows in the same memory from which the
committed histograms will read their stock. This holds for malformed words too. -/
theorem packedCount_card (sh : Shelf) (S : PurchaseSampler) (k depth : ℕ) (m : Shelf.Mem z d)
    (whole : count z d k*PurchaseFrozen.paths z S.degree depth≤2^W) :
    sh.packedCount S k depth m = Fintype.card {i : Fin (count z d k*PurchaseFrozen.paths z S.degree depth) //
      (flagBank sh S z d k depth).read m (i.val:Word W)≠0} := by
  let bank := flagBank sh S z d k depth
  have read (i : Fin (count z d k*PurchaseFrozen.paths z S.degree depth)) :
      bank.read m (i.val:Word W)=m (sh.flagsBase S z d k depth+i.val) := by
    have small : i.val < bank.size := i.isLt.trans (ProtocolRAMPurchaseSampler.lt_span _)
    change m (bank.base + (i.val : Word W).val % bank.size) = _
    rw [Fin.val_cast_of_lt (i.isLt.trans_le whole), Nat.mod_eq_of_lt small]
    rfl
  rw [PurchaseFrozen.Shelf.packedCount,true_count,Fintype.card_subtype]
  simp only [←read,decide_eq_true_eq,Finset.sum_boole]; rfl

/-- Each selected native row corresponds to exactly one real path, with all of
its physical stock addresses. Reverse lookup is justified by counting the stored
flags, so even a padded region with coincident geometry cannot add a new row. -/
theorem liveBoardEquiv (sh : Shelf) (S : PurchaseSampler) (π : Equiv.Perm (Fin (2^z))) (depth start : ℕ)
    (hk : 0<k) (phase : PhasePrice) (T : ℝ) (kind : ℕ) (frozen m : Shelf.Mem z d)
    (tiles : ∀ key : Key z d k,ProtocolRAMPurchaseGateColumns.TileRows (sh.L S depth key).source (Shelf.pathRows S π depth key) m)
    (flags : StoredFlags sh S π depth phase T kind frozen m k)
    (loaded : (stratumHeader z d k S.degree depth start).Loaded m)
    (keys : count z d k≤2^W) (room : (depth+1)*PurchaseFrozen.paths z S.degree depth≤2^W)
    (whole : count z d k*PurchaseFrozen.paths z S.degree depth≤2^W) (wide : 0<W)
    (stock : PurchaseInventory.footprint z (permutationFabric z d).shapes.length k≤2^W) :
    let header := stratumHeader z d k S.degree depth start
    let marked := actualMarks sh phase T kind frozen (k:=k)
    let Active := {i : Fin header.count // (flagBank sh S z d k depth).read m (i.val:Word W)≠0}
    ∃ board : Active ≃ LiveChains S π depth marked,∀i u,
      (allChainSlot (z:=z) (d:=d) sh S depth header u).eval m (i.val.val:Word W)=
        (PurchaseInventory.slot (stripAddress S π depth marked (board i) u):Word W) := by
  intro header marked Active
  obtain ⟨pick,correct⟩ := liveEmbedding sh S π depth start hk phase T kind frozen m tiles flags loaded keys room whole wide stock
  let f : LiveChains S π depth marked→Active := fun p=>⟨pick p,(correct p).1⟩
  have inj : Function.Injective f := fun _ _ eq=>pick.injective (congrArg Subtype.val eq)
  have size : Fintype.card (LiveChains S π depth marked)=Fintype.card Active :=
    (sh.packedCount_liveChains S π depth phase T kind frozen m flags).symm.trans (packedCount_card sh S k depth m whole)
  let equiv := Equiv.ofBijective f ((Fintype.bijective_iff_injective_and_card f).2 ⟨inj,size⟩)
  refine ⟨equiv.symm,?_⟩
  intro i u
  have row : pick (equiv.symm i)=i.val := congrArg Subtype.val (equiv.apply_symm_apply i)
  simpa only [row] using (correct (equiv.symm i)).2 u

end
end Hierarchy.ProtocolRAM.StripDirectory

end OAI
