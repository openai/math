import OAI.Hierarchy.DescentPackedActorPath
import OAI.Hierarchy.DescentParallelBaseLUT
import OAI.Hierarchy.DescentNamedGeometry
import OAI.Hierarchy.DescentPackedTrimOwner

namespace OAI
/-! # True source direction for an undirected pair from its two short rooted endpoint walks -/
namespace Hierarchy.DescentOrdinaryParallelSide
open DescentHostDirectory DescentSixParty DescentStageEdgeReceipt DescentHaloWalkRAM DescentParallelBase
open scoped Classical
noncomputable section
variable {J V F P : Type} [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V] [Field F]
  {d age k slots hosts D : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits} {G : PoweredGadget F} {price ε : ℝ}
variable (A : GroupStage W G price ε J (Host V k slots) age) (group : J↪ℕ) (vertex : V↪Fin hosts)
variable (coord : Function.Injective (fun s=>(A.pos s,A.block s)))
local notation "rank" => vertex.trans Fin.valEmbedding
local notation "name" => A.siteFrom (groupRank group (hostRank rank k slots)) coord
variable (R : Fin hosts→Fin D→Option (Fin hosts))
local notation "endp" => Rebase.terminal R

def localID (u : Host V k slots) :=SiteDecode.localNumber k slots u.val

omit [DecidableEq V] in
theorem local_bound (u : Host V k slots) : localID u<2^(k+1)*slots:=by
  simpa [localID,SiteDecode.localNumber] using packed_room («rank»:=fun _:V=>0) (places:=1) (fun _=>by decide) u.val u.property

omit [DecidableEq V] in
theorem splitID (u : Host V k slots) : hostRank rank k slots u=(vertex u.val.1).val*(2^(k+1)*slots)+localID u :=by
  change packedNumber _ k slots u.val=(vertex u.val.1).val*(2^(k+1)*slots)+packedNumber (fun _=>0) k slots u.val
  simp only [packedNumber,Function.Embedding.trans_apply,Fin.valEmbedding_apply,Nat.zero_mul,Nat.zero_add];ring

/-- Both endpoint ranks use the original donor as their common observer.
The high digit is a four-hop census rank, the low digit the true merged
heap and slot. Every edge has the same next group and block on its ends. -/
def shorter (root : Fin hosts) (p : Fin (breadth D)) (low : ℕ) :=Ranks.earlier endp root (endp root p)*(2^(k+1)*slots)+low

theorem side_at (e : W.graph.Edge) (root : Fin hosts) (src dst : Fin (breadth D))
    (seenS : walk R root (path src) 4=some (vertex (A.pos (W.graph.src e)).2.val.1))
    (seenT : walk R root (path dst) 4=some (vertex (A.pos (W.graph.dst e)).2.val.1)) :
    decide (shorter (k:=k) (slots:=slots) R root dst (localID (A.pos (W.graph.dst e)).2)<
      shorter (k:=k) (slots:=slots) R root src (localID (A.pos (W.graph.src e)).2))=DescentParallelBase.side name (W.graph.src e) (W.graph.dst e) :=by
  let s:=W.graph.src e;let t:=W.graph.dst e
  have groups : (A.pos t).1=(A.pos s).1:=by
    obtain ⟨u,_,hu⟩:=Finset.mem_map.mp (A.peers e).1;exact (congrArg Prod.fst hu).symm
  have blocks:A.block s=A.block t:=A.same e
  have st:endp root src=(vertex (A.pos s).2.val.1).val:=by simp [Rebase.terminal,seenS,s,number]
  have dt:endp root dst=(vertex (A.pos t).2.val.1).val:=by simp [Rebase.terminal,seenT,t,number]
  have less:=Ranks.compare endp root dst src
  have greater:=Ranks.compare endp root src dst
  have eqn : Ranks.earlier endp root (endp root dst)=Ranks.earlier endp root (endp root src) ↔ endp root dst=endp root src:=by omega
  have comp : shorter (k:=k) (slots:=slots) R root dst (localID (A.pos t).2)<shorter (k:=k) (slots:=slots) R root src (localID (A.pos s).2) ↔
      hostRank rank k slots (A.pos t).2<hostRank rank k slots (A.pos s).2:=by
    simp only [shorter,splitID vertex,DescentOrdinaryDonorHalo.lex (local_bound _) (local_bound _)]
    rw [less,eqn,dt,st]
  unfold DescentParallelBase.side;apply decide_eq_decide.mpr
  rw [comp];change _ ↔ (group (A.pos t).1*pitch (hostRank rank k slots)+hostRank rank k slots (A.pos t).2)*2^age+(A.block t).val<
      (group (A.pos s).1*pitch (hostRank rank k slots)+hostRank rank k slots (A.pos s).2)*2^age+(A.block s).val
  rw [groups,blocks,Nat.add_lt_add_iff_right,Nat.mul_lt_mul_right (Nat.two_pow_pos _),Nat.add_lt_add_iff_left]

/-- An entire recipient observes sources of incoming parents through
possibly different old donors. Ranking the final rack in a common *receiver*
list and appending its merged low slot gives precisely their real `siteFrom`
chronology inside the common current group and block. -/
theorem sites {N : ℕ} (endpoint : Fin hosts→Fin N→ℕ) (observer : Fin hosts) (a b : Fin N) (s t : W.graph.Site)
    (groups : (A.pos s).1=(A.pos t).1) (blocks : A.block s=A.block t)
    (left : endpoint observer a=(vertex (A.pos s).2.val.1).val) (right : endpoint observer b=(vertex (A.pos t).2.val.1).val) :
    (Ranks.earlier endpoint observer (endpoint observer a)*(2^(k+1)*slots)+localID (A.pos s).2<
     Ranks.earlier endpoint observer (endpoint observer b)*(2^(k+1)*slots)+localID (A.pos t).2) ↔ name s<name t :=by
  have less:=Ranks.compare endpoint observer a b;have greater:=Ranks.compare endpoint observer b a
  have equ : Ranks.earlier endpoint observer (endpoint observer a)=Ranks.earlier endpoint observer (endpoint observer b) ↔ endpoint observer a=endpoint observer b:=by omega
  have chart : (Ranks.earlier endpoint observer (endpoint observer a)*(2^(k+1)*slots)+localID (A.pos s).2<
     Ranks.earlier endpoint observer (endpoint observer b)*(2^(k+1)*slots)+localID (A.pos t).2) ↔
      hostRank rank k slots (A.pos s).2<hostRank rank k slots (A.pos t).2:=by
    simp only [splitID vertex,DescentOrdinaryDonorHalo.lex (local_bound _) (local_bound _)]
    rw [less,equ,left,right]
  rw [chart];change _ ↔ (group (A.pos s).1*pitch (hostRank rank k slots)+hostRank rank k slots (A.pos s).2)*2^age+(A.block s).val<
      (group (A.pos t).1*pitch (hostRank rank k slots)+hostRank rank k slots (A.pos t).2)*2^age+(A.block t).val
  rw [groups,blocks,Nat.add_lt_add_iff_right,Nat.mul_lt_mul_right (Nat.two_pow_pos _),Nat.add_lt_add_iff_left]

end
end Hierarchy.DescentOrdinaryParallelSide

end OAI
