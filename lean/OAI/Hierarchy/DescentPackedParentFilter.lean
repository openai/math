import OAI.Hierarchy.DescentParentLocalRank
import OAI.Hierarchy.DescentHaloPairRanks
import OAI.Hierarchy.DescentPackedParentIncidence
import OAI.Hierarchy.DescentParallelBaseStream

namespace OAI
/-! # Two-sided packed reception towardOld actual rooted endpoint paths and normalized local slots -/
namespace Hierarchy.DescentParallelBase.ParentFilter
open DescentSIMDLookup DescentHaloWalkRAM DescentSharedCableNames
open scoped Classical
noncomputable section
variable {H D Q K L : ℕ}
local notation "reach" => Gather.reaching

structure Endpoint (P Q : ℕ) where
  path : Fin P
  low : Fin Q

structure Source (P Q K L : ℕ) where
  src : Endpoint P Q
  dst : Endpoint P Q
  upper : Bool
  ticket : Fin K
  weight : Fin (L+1)

local notation "P" => breadth D

/-- The peer field uses the original receiver as a common observer, including
when the two records were issued by different prior neighbors. -/
def peer (R : Fin H→Fin D→Option (Fin H)) (v : Fin H) (p : Fin P) (j : Endpoint P Q) : Fin (P*P*Q) :=
  finProdFinEquiv (PairRanks.ticket (reach R) v p j.path,j.low)

def filter (R : Fin H→Fin D→Option (Fin H)) (receiver : Fin H×Fin Q) (p : Fin P) (old : Fin H) (r : Source P Q K L) : Option (Entry (P*P*Q) K L) :=
  let self:=Rebase.value R .rank receiver.1 p
  let atSource:= (localRank R old r.src.path).val=self ∧ r.src.low=receiver.2
  let atTarget:= (localRank R old r.dst.path).val=self ∧ r.dst.low=receiver.2
  if r.weight.val=0 then none else if atSource then some ⟨peer R receiver.1 p r.dst,r.upper,r.ticket,r.weight⟩
  else if atTarget then some ⟨peer R receiver.1 p r.src,r.upper,r.ticket,r.weight⟩ else none

structure Witness (R : Fin H→Fin D→Option (Fin H)) (old : Fin H) (r : Source P Q K L) (s t : Fin H×Fin Q) : Prop where
  src : reach R old r.src.path=some s.1
  dst : reach R old r.dst.path=some t.1
  srcLow : r.src.low=s.2
  dstLow : r.dst.low=t.2

theorem unique (R : Fin H→Fin D→Option (Fin H)) (symmetric : ∀v u i,R v i=some u→∃j,R u j=some v) (old v t : Fin H) (p q : Fin P)
    (towardOld : reach R v p=some old) (to_ : reach R old q=some t) : (localRank R old q).val=Rebase.value R .rank v p ↔ v=t :=by
  obtain ⟨r,back,_,rank⟩:=Rebase.actual R symmetric v old p towardOld
  have r_val:Rebase.terminal R old r=v.val:=by simp [Rebase.terminal,back,number]
  have q_val:Rebase.terminal R old q=t.val:=congrArg number to_
  have less:=Ranks.compare (Rebase.terminal R) old q r;have greater:=Ranks.compare (Rebase.terminal R) old r q
  rw [q_val,r_val] at less greater
  rw [rank]
  change Ranks.earlier (Rebase.terminal R) old (Rebase.terminal R old q) = _ ↔ v=t
  rw [q_val,Fin.ext_iff];omega

theorem accepted (R : Fin H→Fin D→Option (Fin H)) (symmetric : ∀v u i,R v i=some u→∃j,R u j=some v)
    (v s t : Fin H×Fin Q) (old : Fin H) (p : Fin P) (r : Source P Q K L) (towardOld : reach R v.1 p=some old) (real : Witness R old r s t) :
    filter R v p old r=if r.weight.val=0 then none else if v=s then some ⟨peer R v.1 p r.dst,r.upper,r.ticket,r.weight⟩ else
      if v=t then some ⟨peer R v.1 p r.src,r.upper,r.ticket,r.weight⟩ else none :=by
  have src : (localRank R old r.src.path).val=Rebase.value R .rank v.1 p ∧ r.src.low=v.2 ↔ v=s:=by
    rw [unique R symmetric old v.1 s.1 p r.src.path towardOld real.src,real.srcLow,Prod.ext_iff];tauto
  have dst : (localRank R old r.dst.path).val=Rebase.value R .rank v.1 p ∧ r.dst.low=v.2 ↔ v=t:=by
    rw [unique R symmetric old v.1 t.1 p r.dst.path towardOld real.dst,real.dstLow,Prod.ext_iff];tauto
  simp only [filter,src,dst]

theorem peer_iff (R : Fin H→Fin D→Option (Fin H)) (v x y : Fin H) (p q : Fin P) (a b : Endpoint P Q) (sa sb : Fin H×Fin Q)
    (left : reach R v p=some x) (right : reach R v q=some y)
    (first : reach R x a.path=some sa.1) (second : reach R y b.path=some sb.1) (lo : a.low=sa.2) (hi : b.low=sb.2) :
    peer R v p a=peer R v q b ↔ sa=sb :=by
  rw [peer,peer,Equiv.apply_eq_iff_eq,Prod.ext_iff,Prod.ext_iff]
  rw [PairRanks.same (reach R) v x y sa.1 sb.1 p a.path q b.path left first right second,lo,hi]

/-- Native local filter: all common ranks and current/other endpoint slots
have already been read. No absolute rack number occurs in the local LUT. -/
def chip (self sl sr dl dr here farS farT : ℕ) (upper : Bool) (ticket : Fin K) (weight : Fin (L+1)) (bound : ℕ) : Option (Entry bound K L):=
  if weight.val=0 then none else
    if self=sr ∧ here=sl then if inside:farT<bound then some ⟨⟨farT,inside⟩,upper,ticket,weight⟩ else none
    else if self=dr ∧ here=dl then if inside:farS<bound then some ⟨⟨farS,inside⟩,upper,ticket,weight⟩ else none else none

theorem chip_filter (R : Fin H→Fin D→Option (Fin H)) (v : Fin H×Fin Q) (p : Fin P) (old : Fin H) (r : Source P Q K L) :
    chip (Rebase.value R .rank v.1 p) r.src.low.val (localRank R old r.src.path).val r.dst.low.val (localRank R old r.dst.path).val v.2.val
      (peer R v.1 p r.src).val (peer R v.1 p r.dst).val r.upper r.ticket r.weight (P*P*Q)=filter R v p old r :=by
  simp only [chip,filter,dite_eq_left (peer R v.1 p r.src).isLt,dite_eq_left (peer R v.1 p r.dst).isLt,Fin.mk_val]
  have test (path : Fin P) (low : Fin Q) :
      (Rebase.value R .rank v.1 p = (localRank R old path).val ∧ v.2.val = low.val) ↔
        (localRank R old path).val = Rebase.value R .rank v.1 p ∧ low = v.2 :=
    and_congr eq_comm (Fin.ext_iff.symm.trans eq_comm)
  simp only [test]

end
end Hierarchy.DescentParallelBase.ParentFilter

end OAI
