import OAI.Hierarchy.ProtocolRAMPurchaseMarketResult

namespace OAI
/-! # Binary values at every address of the packed purchase flag bank -/

namespace Hierarchy.ProtocolRAM.PurchaseFrozen.Shelf

open Computability.VPVNP.BurstRAM PrivateRAM ProbeStage ProbeStage.Native
open scoped Fin.CommRing Classical
noncomputable section
variable {z d k : ℕ}

/-- A flat address in the returned bank contains the binary native flag for
its unique stage/sign key and candidate. -/
theorem packed_binary (sh : Shelf) (S : PurchaseSampler) (π : Equiv.Perm (Fin (2^z)))
    (depth : ℕ) (hd : 1≤ d) (phase : PhasePrice) (T : ℝ) (kind : ℕ) (frozen fixture : Mem z d)
    (input : sh.Incoming (k:=k) S π depth phase T kind frozen)
    (prepared : ∀ i : Key z d k, sh.Prepared S depth fixture i frozen)
    (room : sh.flagsBase S z d k depth+count z d k*paths z S.degree depth<2^wordBits z d copies)
    (r : Fin (count z d k*paths z S.degree depth)) :
    (sh.result S k depth frozen (sh.flagsBase S z d k depth+r.val)).val ≤ 1 := by
  obtain ⟨_,_,_,words⟩ := sh.run S π depth hd phase T kind frozen fixture input prepared room
  obtain ⟨⟨i,j⟩,rfl⟩ := finProdFinEquiv.surjective r
  have address : sh.flagsBase S z d k depth+(finProdFinEquiv (i,j)).val =
      sh.flagsBase S z d k depth+i.val*paths z S.degree depth+j.val := by
    change _+(j.val+paths z S.degree depth*i.val) = _
    ac_rfl
  have bit (b : Bool) : (MarkTape.encode (wordBits z d copies) b).val≤1 := by
    cases b with
    | false => exact Nat.zero_le _
    | true => exact Nat.mod_le 1 _
  rw [address,words i j]
  exact bit _

end
end Hierarchy.ProtocolRAM.PurchaseFrozen.Shelf

end OAI
