import OAI.Hierarchy.DescentPackedMinimum
import OAI.Hierarchy.ProtocolRAMGeneratedWrite

namespace OAI
/-! # The first-minimum controller preserves shared ROM on either side of its workspace -/

namespace Hierarchy.DescentFirstMinimumRAM
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
theorem frame_high {w : ℕ} (out : ℕ) (b : Bank) (m : Memory w) (xs : List ℕ) (a : ℕ)
    (hi : out+xs.length≤a) : after out b m xs a=m a := by
  induction xs with
  | nil=>rfl
  | cons i is ih=>
    simp only [List.length_cons] at hi
    exact (ProtocolRAMGeneratedWrite.frame_image _ _ _ _ _ (.inr (by omega))).trans (ih (by omega))
end Hierarchy.DescentFirstMinimumRAM

namespace Hierarchy.DescentPackedMinimum
open DescentSIMDLookup DescentPackedScore ProtocolRAM
open Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.RAMSerialization
open ThreeFlat.RAM PhysicalProcedure
open scoped Fin.CommRing Classical BigOperators
noncomputable section
attribute [local irreducible] Procedure.Exec
variable {a M H r w q : ℕ}

private theorem memory_frame (L : Layout q) (bounds : Fits L w a M H r) (f : Fin q→Cell a→ℕ)
    (x : Fin q→Fin H→Fin r→Cell a) (m : Memory w) (xs : List (Fin q)) {u : ℕ} (away : u<L.work ∨ L.result≤u) :
    memory (M:=M) L f x m xs u=m u := by
  induction xs with
  | nil=>rfl
  | cons i is ih=>
    have span:=bounds.workspace
    have top:=bounds.ledger.2.2
    have cap:=i.isLt.trans_le bounds.capacity
    have saved : ¬(L.work≤u ∧ u<L.work+(H*chunks r M+1)):=by omega
    have score : ¬(L.ledger.base+i.val≤u ∧ u<L.ledger.base+i.val+1):=by omega
    simpa only [memory,fillSegment,ite_eq_right saved,ite_eq_right score] using ih

theorem minimum_frames (L : Layout q) (bounds : Fits L w a M H r) (f : Fin q→Cell a→ℕ)
    (x : Fin q→Fin H→Fin r→Cell a) (m : Memory w) (zero : ∀i,f i 0=0) (positive : 0<M)
    (sumFits : ∀i,scores f x i<2^w)
    (ready : ∀i,Input (M:=M) (L.source i) (L.dictionary i) (f i) (x i) m) {j s : ℕ}
    (winner : (DescentColonies.scanMinimum (scoreAt f x) (List.range q)).1=some (j,s)) :
    ∃after, (search L w H r M).Exec m after
       ((4+q*cost L.work (H*chunks r M))+DescentFirstMinimumRAM.ticks L.result L.ledger (List.range q)) ∧
       after (L.result+(q-1))=(j:Word w) ∧ (∀u<L.work,after u=m u) ∧ ∀u,L.result+q≤u→after u=m u := by
  let ledger:=memory (M:=M) L f x m (List.finRange q)
  have run:=issue L bounds f x m zero positive sumFits ready (List.finRange q)
  have select:=DescentFirstMinimumRAM.exec L.ledger ledger (List.range q) bounds.ledger (by simpa using bounds.room) bounds.word
  have words (k : ℕ) (hk : k∈List.range q) : ledger (L.ledger.base+k)=(scoreAt f x k:Word w) := by
    let i : Fin q:=⟨k,List.mem_range.mp hk⟩
    have out:=entries L bounds f x m (List.finRange q) i (List.mem_finRange i)
    simpa only [ledger,scoreAt,dite_eq_left (List.mem_range.mp hk)] using out
  refine ⟨_,by simpa [search,ledger] using run.then select,?_,?_,?_⟩
  · simpa only [List.length_range] using DescentFirstMinimumRAM.winner L.ledger ledger (scoreAt f x) (List.range q) bounds.ledger
      (fun k hk=>(List.mem_range.mp hk).trans_le bounds.capacity) words
      (fun k hk=>by simpa [scoreAt,List.mem_range.mp hk] using sumFits ⟨k,List.mem_range.mp hk⟩) winner
  · intro u hu
    rw [DescentFirstMinimumRAM.frame _ _ _ _ _ (by have:=bounds.workspace;have:=bounds.ledger.2.2;omega)]
    exact memory_frame L bounds f x m _ (.inl hu)
  · intro u hu
    rw [DescentFirstMinimumRAM.frame_high _ _ _ _ _ (by simpa only [List.length_range] using hu)]
    exact memory_frame L bounds f x m _ (.inr (by omega))

end
end Hierarchy.DescentPackedMinimum

end OAI
