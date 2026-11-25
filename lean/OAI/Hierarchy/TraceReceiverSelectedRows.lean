import OAI.Hierarchy.TraceReceiverTerminalRows
import OAI.Hierarchy.TraceReceiverOwnerRegistered

namespace OAI
/-! # The S17 factor list and the terminal cache have the same elected owners -/

noncomputable section
namespace Hierarchy.TraceFactorReceiver.Gather
open ThreeFlat RAM Computability.VPVNP.BurstRAM PrivateRAM
open HistoryNodeDirectory HistoryNodeDirectory.Selected HistoryStageBody.Physical
open scoped Fin.CommRing

/-- After the complete chronological pass every occurrence selected for the
tick has an S13 and S12 cache, including the case of an empty factor list. -/
theorem selected_published {F : Type} {w W first N d T age : ℕ}
    (chron : Chronology (first+N)) (closed : chron.firstFinal=first) (ht : 0<T)
    (cost : Fin N→Fin d→ℕ) (tick : Fin T) (v : Fin (first+N)→NodeValue F)
    (tag : ((Fin 3→Bool)→F)→ℕ) (keep : ℕ→Prop) (input out : Memory W)
    (small : first+N<2^W) (fits : T≤2^W)
    (done : Ledger age (TraceReceiverOwnerMount.directory chron
        (fun j=>((FactorAllocation.owner ht w cost j).val:Word W)) (tick.val:Word W))
      tag v keep input (first+N) out)
    (f : Fin N) (chosen : f∈FactorAllocation.factors w cost (List.finRange N) tick) :
    let id : Fin (first+N):=⟨first+f.val,Nat.add_lt_add_left f.isLt first⟩
    (v id).Cached tag age id.val out := by
  intro id
  apply done.published id id.isLt
  rw [TraceReceiverOwnerMount.picked_iff chron closed (FactorAllocation.owner ht w cost) tick id small fits]
  have eqn : chron.root id=f.val:=by
    rw [Chronology.root,closed,dite_eq_right (by change ¬first+f.val<first;omega)]
    change first+f.val-first=f.val
    omega
  have addr : (⟨chron.root id,by have hh:=chron.root_lt id;rw [closed] at hh;omega⟩ : Fin N)=f :=
    Fin.ext eqn
  rw [addr]
  exact ((FactorAllocation.mem_factors_iff_owner ht w cost f tick).mp chosen).symm

end Hierarchy.TraceFactorReceiver.Gather
end

end OAI
