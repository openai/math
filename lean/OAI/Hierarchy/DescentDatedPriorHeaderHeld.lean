import OAI.Hierarchy.DescentDatedPriorHeaderPorts

namespace OAI
/-! Every rooted path, rank, and sparse-access row lies strictly below the geometry boundary. -/
namespace Hierarchy.DescentDatedAddressBook.PriorHeader
open DescentHaloWalkRAM DescentPackedColony DescentSIMDLookup DescentDyadicSpan
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure ProtocolRAM
open scoped Classical Fin.CommRing
noncomputable section
variable {w H G M D:ℕ} (base:ℕ) (adj:Bank)
local notation "P"=>breadth D
local notation "N"=>H*P
local notation "J"=>H*(P*P)
local notation "n"=>H*chunks G M
local notation "old"=>ports H G M D base
local notation "unique₀"=>uniquePorts H G M D base
local notation "ranks₀"=>rankBanks H G M D base
local notation "out"=>image H G M D base adj
variable (ok:Room adj H G M D base w) (m:Memory w) (R:Fin H→Fin D→Option (Fin H))
  (initial:∀ (v:Fin H) (j:Fin D),m (adj.base+v.val*D+j.val)=(number (R v j):Word w))
variable (mem:Memory w)
  (kept:∀a<endAddress H G M D base,mem a=image H G M D base adj m a)

include kept

theorem kept_word (j i:ℕ) (l:j<P+20) (r:i<stride H G M D):
    mem ((bank H G M D base j).base+i)=out m ((bank H G M D base j).base+i):=by
  have extent:=Nat.mul_le_mul_right (stride H G M D) (show j+1≤P+20 by omega)
  rw [Nat.add_mul,Nat.one_mul] at extent
  apply kept
  change base+j*stride H G M D+i<base+(P+20)*stride H G M D
  omega

include ok initial

theorem held_directory:DescentOrdinaryDonorRankDirectory.Reads R ranks₀ mem:=by
  have d:=directory base adj ok m R initial
  have c:=limits H G M D
  have stay (j i:ℕ) (hj:j<P+20) (hi:i<stride H G M D):=kept_word base adj m mem kept j i hj hi
  refine ⟨fun v p=>?_,fun v p q=>?_,fun v p q=>?_,fun v=>?_,fun v p=>?_,fun v p=>?_,fun v p q=>?_⟩
  · exact (stay (P+15) _ (by omega) ((Ranks.id v p).isLt.trans_le c.2.2.1)).trans (d.visit v p)
  · exact (stay 8 _ (by omega) ((Ranks.id v (PairRanks.pair p q)).isLt.trans_le c.2.2.2.1)).trans (d.prev v p q)
  · exact (stay 9 _ (by omega) ((Ranks.id v (PairRanks.pair p q)).isLt.trans_le c.2.2.2.1)).trans (d.suffix v p q)
  · exact (stay 7 _ (by omega) (v.isLt.trans_le c.2.1)).trans (d.offset v)
  · exact (stay (P+16) _ (by omega) ((Ranks.id v p).isLt.trans_le c.2.2.1)).trans (d.reverse v p)
  · exact (stay (P+14) _ (by omega) ((Ranks.id v p).isLt.trans_le c.2.2.1)).trans (d.localValue v p)
  · exact (stay (P+19) _ (by omega) ((Ranks.id v (PairRanks.pair p q)).isLt.trans_le c.2.2.2.1)).trans (d.shared v p q)

theorem held_ports:Mounted old (Gather.reaching R) mem G M ∧ Mounted unique₀ (Gather.select (Gather.reaching R)) mem G M:=by
  have d:=mounted base adj ok m R initial
  have c:=limits H G M D
  have stay (j i:ℕ) (hj:j<P+20) (hi:i<stride H G M D):=kept_word base adj m mem kept j i hj hi
  have ids (p:Row H G M) (i:Fin P):= (stay (13+i.val) _ (by have:=i.isLt;omega) ((DescentSIMDLookup.row H G M p).isLt.trans_le c.2.2.2.2)).trans (d.1.ids p i)
  have off (v:Fin H):= (stay 11 _ (by omega) (v.isLt.trans_le c.2.1)).trans (d.1.offsets v)
  have chunk (p:Row H G M):=(stay 12 _ (by omega) ((DescentSIMDLookup.row H G M p).isLt.trans_le c.2.2.2.2)).trans (d.1.chunks p)
  refine ⟨⟨ids,fun v p=>?_,off,chunk⟩,⟨ids,fun v p=>?_,off,chunk⟩⟩
  · exact (stay (P+13) _ (by omega) (by simpa only [Ranks.id,rect] using (Ranks.id v p).isLt.trans_le c.2.2.1)).trans (d.1.roster v p)
  · exact (stay (P+15) _ (by omega) (by simpa only [Ranks.id,rect] using (Ranks.id v p).isLt.trans_le c.2.2.1)).trans (d.2.roster v p)

theorem held_reverse (v:Fin H) (p:Fin P):
    mem ((reversePath H G M D base).base+(Ranks.id v p).val)=(Rebase.value R .path v p:Word w):=
  (kept_word base adj m mem kept (P+17) _ (by omega) ((Ranks.id v p).isLt.trans_le (limits H G M D).2.2.1)).trans
    (reversed base adj ok m R initial v p)

theorem held_eight (v:Fin H) (t:Fin (P*P)):
    mem ((priorEnds H G M D base).base+(Ranks.id v t).val)=(number (PairRanks.combined (Gather.reaching R) v t):Word w) ∧
    mem ((priorRanks H G M D base).base+(Ranks.id v t).val)=
      (Ranks.earlier (fun v t=>number (PairRanks.combined (Gather.reaching R) v t)) v
        (number (PairRanks.combined (Gather.reaching R) v t)):Word w):=by
  have bound:=(Ranks.id v t).isLt.trans_le (limits H G M D).2.2.2.1
  exact ⟨(kept_word base adj m mem kept (P+18) _ (by omega) bound).trans (octets base adj ok m R initial v t),
    (kept_word base adj m mem kept (P+19) _ (by omega) bound).trans (octet_rank base adj ok m R initial v t)⟩


end
end Hierarchy.DescentDatedAddressBook.PriorHeader

end OAI
