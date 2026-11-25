import OAI.Hierarchy.DescentParentFilterRoster
import OAI.Hierarchy.DescentHaloPackedRebase

namespace OAI
/-! # Looking up a source-side parent rank from its original issuing rack -/
namespace Hierarchy.DescentParallelBase.SourceReturn
open DescentHaloWalkRAM DescentSharedCableNames DescentSIMDLookup
open scoped Classical
noncomputable section
variable {D H O c Q : ℕ} (R:Fin H→Fin D→Option (Fin H))
local notation "P" => breadth D
local notation "reach" => Gather.reaching R

private theorem choose_min (v u : Fin H) (xs : List (Fin P)) (order:xs.Pairwise (·<·))
    {q:Fin P} (selected:Rebase.choose R v u xs=some q):
    q∈xs ∧ Rebase.terminal R v q=u.val ∧ ∀a∈xs,a<q→Rebase.terminal R v a≠u.val:=by
  induction xs with
  | nil=>contradiction
  | cons a xs ih=>
    simp only [Rebase.choose] at selected
    obtain ⟨early,sorted⟩:=List.pairwise_cons.mp order
    by_cases hit:Rebase.terminal R v a=u.val
    · rw [ite_eq_left hit] at selected;obtain rfl:=Option.some.inj selected
      refine ⟨List.mem_cons_self,hit,?_⟩;intro x present lower;rcases List.mem_cons.mp present with rfl|member
      · exact False.elim ((lt_irrefl _) lower)
      · exact False.elim ((not_lt_of_ge (early x member).le) lower)
    · rw [ite_eq_right hit] at selected
      obtain ⟨mem,last,minimal⟩:=ih sorted selected
      refine ⟨List.mem_cons_of_mem _ mem,last,?_⟩;intro x present lower;rcases List.mem_cons.mp present with rfl|member
      · exact hit
      · exact minimal x member lower

/-- The native reverse-path word is *the* retained path slot at the new
source, even when many walks return to the same issuing old rack. -/
theorem canonical (v u : Fin H) (p:Fin P) (arrived:reach u p=some v) (recip:∀v u i,R v i=some u→∃j,R u j=some v):
    ∃q:Fin P,Rebase.value R .path u p=q.val ∧ Gather.select reach v q=some u:=by
  obtain ⟨q,back,pathEq,_⟩:=Rebase.actual R recip u v p arrived
  refine ⟨q,pathEq,?_⟩
  have pick:Rebase.choose R v u (List.finRange P)=some q:=by
    change walk R u (path p) 4 = some v at arrived
    simp only [Rebase.value, arrived] at pathEq
    cases chosen:Rebase.choose R v u (List.finRange P) with
    | none=>rw [chosen] at pathEq;exact False.elim ((Nat.ne_of_lt q.isLt) pathEq.symm)
    | some j=>rw [chosen] at pathEq;exact congrArg some (Fin.ext pathEq)
  have min:=(choose_min R v u _ (List.pairwise_lt_finRange _) pick).2.2
  rw [Gather.select,ite_eq_right _];exact back
  rintro ⟨a,lower,same⟩;apply min a (List.mem_finRange a) lower
  exact congrArg number (same.trans back)

variable {E U T X V : Type} [Fintype E] [Fintype X] [Fintype T] [DecidableEq U] {n K L : ℕ} {B : Ends U n}
  (C:Blocks B E) (symm:∀v u i,R v i=some u→∃j,R u j=some v)
  (Z:ParentFilter.Measured C R X T V Q O K L)

/-- Decode the true local `(returnPath,oldRole)` for the actual normalized
source's paid resident position. No successor signed chip is read here. -/
theorem source_order (src:U) (e:Local C src) (p:Fin P)
    (forward:reach (Z.old src e) p=some (Z.venue src).1):
    let index:=(ParentFilter.Measured.roster C R symm Z).address src e
    (finProdFinEquiv.symm index).1.val=Rebase.value R .path (Z.old src e) p ∧
    (finProdFinEquiv.symm index).2=(Z.loc (Z.raw src e)).2:=by
  intro index
  obtain ⟨q,val,selected⟩:=canonical R _ _ p forward symm
  let near:=ParentFilter.Measured.near C R symm Z src
  have read:=Resident.visit_read C src (fun h=>(Z.venue h).1) Z.loc (Z.raw src) reach near e
  have key:=((Gather.once reach (Z.venue src).1 (Z.old src e) (near e)).unique read selected)
  change (finProdFinEquiv.symm (finProdFinEquiv (_, _))).1.val=_ ∧ (finProdFinEquiv.symm (finProdFinEquiv (_, _))).2=_
  simp only [Equiv.symm_apply_apply];exact ⟨(congrArg Fin.val key).trans val.symm,True.intro⟩

end
end Hierarchy.DescentParallelBase.SourceReturn

end OAI
