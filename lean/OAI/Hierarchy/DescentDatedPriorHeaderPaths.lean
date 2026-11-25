import OAI.Hierarchy.DescentDatedPriorHeaderWords

namespace OAI
/-! A single measured prior adjacency gives all of the original signed
directory, including repeated visits, reciprocal paths, and unused racks. -/
namespace Hierarchy.DescentDatedAddressBook.PriorHeader
open DescentSixParty.Chronology DescentHaloWalkRAM DescentPackedColony DescentSIMDLookup DescentDyadicSpan
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure ProtocolRAM
open scoped Classical Fin.CommRing
noncomputable section
variable {w H G M D:ℕ}
local notation "P"=>breadth D
local notation "N"=>H*P
local notation "L"=>H*(P*P)
local notation "pitch"=>stride H G M D
variable (base:ℕ) (adj:Bank)
local notation "out"=>image H G M D base adj
local notation "col"=>bank H G M D base
local notation "rk4"=>ranks4 H G M D base
local notation "first"=>duplicates H G M D base
local notation "rev"=>reversals H G M D base
local notation "mix"=>pairs H G M D base
local notation "rk8"=>ranks8 H G M D base
variable (ok:Room adj H G M D base w) (m:Memory w) (R:Fin H→Fin D→Option (Fin H))
  (old:∀(v:Fin H) (j:Fin D),m (adj.base+v.val*D+j.val)=(number (R v j):Word w))
include ok old
local notation "R₄"=>Gather.reaching R
local notation "R₈"=>PairRanks.combined R₄
local notation "steps"=>raw_steps base adj ok m

theorem four_words:Ranks.Reads rk4 (Rebase.terminal R) (out m):=by
  have q:=walk_words base adj ok m R old
  have fit:=walk_room H G M D base adj ok
  have cap:=limits H G M D
  constructor
  · intro v p
    rw [←row_rect v p]
    exact (steps.1 (DescentHaloWalkRAM.row v p)).trans (DescentHaloWalkRAM.body_at _ _ fit R (out m) q v p 4)
  · intro v p
    have l:=(Ranks.id v p).isLt.trans_le cap.2.2.1
    refine (literal_word base adj ok m 5 (by omega) (Ranks.id v p).val l).trans (congrArg (fun a:ℕ=>(a:Word w)) ?_)
    change (Ranks.id v p).val/P*P=v.val*P
    rw [show (Ranks.id v p).val=v.val*P+p.val from rect v p,quot v.val p]
  · intro v p
    change number (Gather.reaching R v p)<2^w
    cases Gather.reaching R v p with
    | none=>exact ok.hosts
    | some u=>exact u.isLt.trans ok.hosts

theorem four_rank (v:Fin H) (p:Fin P):
    out m ((localRank H G M D base).base+(Ranks.id v p).val)=(Ranks.earlier (Rebase.terminal R) v (Rebase.terminal R v p):Word w):=
  (steps.2.1 _).trans (Ranks.body_at rk4 _ (four_room H G M D base adj ok 14 (by decide) (by decide))
    (Rebase.terminal R) (out m) (four_words base adj ok m R old) v p)

theorem visits (v:Fin H) (p:Fin P):
    out m ((visited H G M D base).base+(Ranks.id v p).val)=(number (Gather.select R₄ v p):Word w):=by
  have cap:=limits H G M D
  have live:Gather.Reads first R₄ (out m):=⟨four_words base adj ok m R old,fun v p=>by
    refine (literal_word base adj ok m 6 (by omega) (Ranks.id v p).val ((Ranks.id v p).isLt.trans_le cap.2.2.1)).trans (congrArg (fun a:ℕ=>(a:Word w)) ?_)
    change (Ranks.id v p).val%P=p.val
    rw [show (Ranks.id v p).val=v.val*P+p.val from rect v p,rem v.val p]⟩
  exact (steps.2.2.1 _).trans (Gather.row_at first (duplication_room H G M D base adj ok) R₄ (out m) live v p)

theorem reciprocal_words:Rebase.Reads R rev (out m):=by
  have cap:=limits H G M D
  have ray:=four_words base adj ok m R old
  refine ⟨fun v p=>?_,four_rank base adj ok m R old,(walk_words base adj ok m R old).root,fun v=>?_⟩
  · simpa only [reversals,ranks4,row_rect] using ray.endpoints v p
  · simpa [reversals,digits] using (literal_word base adj ok m 7 (by omega) v.val (v.isLt.trans_le cap.2.1))

theorem pair_words:PairRanks.Reads mix R₄ (out m):=by
  have cap:=limits H G M D
  have ray:=four_words base adj ok m R old
  refine ⟨fun v p=>?_,fun v p q=>?_,fun v p q=>?_,(reciprocal_words base adj ok m R old).offsets⟩
  · simpa only [pairs,ranks4,Ranks.id,rect,Rebase.terminal,Gather.reaching] using ray.endpoints v p
  · let j:=PairRanks.pair p q
    have t:=literal_word base adj ok m 8 (by omega) (Ranks.id v j).val ((Ranks.id v j).isLt.trans_le cap.2.2.2.1)
    refine t.trans (congrArg (fun n:ℕ=>(n:Word w)) ?_)
    change (Ranks.id v j).val/(P*P)*P+((Ranks.id v j).val%(P*P))/P=(Ranks.id v p).val
    have rj : (Ranks.id v j).val=v.val*(P*P)+j.val:=rect v j
    have rp : (Ranks.id v p).val=v.val*P+p.val:=rect v p
    rw [rj,quot v.val j,rem v.val j,rp]
    change v.val*P+(finProdFinEquiv (p,q)).val/P=v.val*P+p.val
    rw [rect p q,quot p.val q]
  · let j:=PairRanks.pair p q
    have t:=literal_word base adj ok m 9 (by omega) (Ranks.id v j).val ((Ranks.id v j).isLt.trans_le cap.2.2.2.1)
    refine t.trans (congrArg (fun n:ℕ=>(n:Word w)) ?_)
    change (Ranks.id v j).val%P=q.val
    rw [pair_rect v p q,show v.val*(P*P)+(p.val*P+q.val)=(v.val*P+p.val)*P+q.val by ring]
    exact rem _ q

theorem octets (v:Fin H) (t:Fin (P*P)):
    out m ((priorEnds H G M D base).base+(Ranks.id v t).val)=(number (R₈ v t):Word w):=by
  obtain ⟨⟨p,q⟩,rfl⟩:=finProdFinEquiv.surjective t
  exact (steps.2.2.2.2.2.1 _).trans (PairRanks.eval mix _ (pair_room H G M D base adj ok 18 (by decide) (by decide))
    R₄ (out m) (pair_words base adj ok m R old) v p q)

theorem eight_words:Ranks.Reads rk8 (fun v t=>number (R₈ v t)) (out m):=by
  have cap:=limits H G M D
  refine ⟨fun v p=>?_,fun v p=>?_,fun v p=>?_⟩
  · simpa only [ranks8,Ranks.id,rect] using octets base adj ok m R old v p
  · refine (literal_word base adj ok m 10 (by omega) (Ranks.id v p).val ((Ranks.id v p).isLt.trans_le cap.2.2.2.1)).trans (congrArg (fun a:ℕ=>(a:Word w)) ?_)
    change (Ranks.id v p).val/(P*P)*(P*P)=v.val*(P*P)
    rw [show (Ranks.id v p).val=v.val*(P*P)+p.val from rect v p,quot v.val p]
  · cases h:R₈ v p with
    | none=>simpa [h,number] using ok.hosts
    | some u=>simpa [h,number] using u.isLt.trans ok.hosts

theorem octet_rank (v:Fin H) (t:Fin (P*P)):
    out m ((priorRanks H G M D base).base+(Ranks.id v t).val)=
      (Ranks.earlier (fun u j=>number (R₈ u j)) v (number (R₈ v t)):Word w):=
  (steps.2.2.2.2.2.2 _).trans (Ranks.body_at rk8 _ (eight_room H G M D base adj ok) _ (out m)
    (eight_words base adj ok m R old) v t)

theorem reversed (v:Fin H) (p:Fin P):
    out m ((reversePath H G M D base).base+(Ranks.id v p).val)=(Rebase.value R .path v p:Word w):=
  (steps.2.2.2.2.1 _).trans (Rebase.body_at R rev .path _ (reversal_room H G M D base adj ok 17 (by decide) (by decide))
    (out m) (reciprocal_words base adj ok m R old) v p)


end
end Hierarchy.DescentDatedAddressBook.PriorHeader

end OAI
