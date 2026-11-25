import OAI.Hierarchy.DescentIncidentRankIssue
import OAI.Hierarchy.DescentParentFilterRoster
import OAI.Hierarchy.DescentOrdinaryParallelSide

namespace OAI
/-! # Order all incident parents by their compressed native source, then by their donor ticket -/
namespace Hierarchy.DescentParallelBase.Incidence
open DescentHaloWalkRAM DescentSharedCableNames DescentParallelBase.ParentFilter DescentHostDirectory DescentSixParty DescentStageEdgeReceipt
open scoped Classical
noncomputable section
variable {U E X T V : Type} [Fintype E] [DecidableEq U] [Fintype X] [Fintype T]
  {n H D Q O K L:ℕ} {B:Ends U n} (C:Blocks B E) (R:Fin H→Fin D→Option (Fin H))
  (symm:∀v u i,R v i=some u→∃j,R u j=some v) (Z:Measured C R X T V Q O K L)
local notation "P"=>breadth D

def srcKey (h:U) (e:Local C h) : Fin (P*P*Q):=peer R (Z.venue h).1 (Measured.visit C R symm Z h e) (Z.read h e).src

omit [Fintype E] in
theorem native_order (h:U) (e f:Local C h):
    srcKey C R symm Z h e<srcKey C R symm Z h f ↔
    (Z.venue (C.src e.val)).1<(Z.venue (C.src f.val)).1 ∨ (Z.venue (C.src e.val)).1=(Z.venue (C.src f.val)).1 ∧ (Z.venue (C.src e.val)).2<(Z.venue (C.src f.val)).2:=by
  let p:=Measured.visit C R symm Z h e;let q:=Measured.visit C R symm Z h f
  have a:=Measured.fromOld C R symm Z h e;have b:=Measured.fromOld C R symm Z h f
  have s:=Z.reached h e;have t:=Z.reached h f
  have order:=source_before (Gather.reaching R) (Z.venue h).1 (Z.old h e) (Z.old h f) (Z.venue (C.src e.val)).1 (Z.venue (C.src f.val)).1 p (Z.read h e).src.path q (Z.read h f).src.path a b s.src t.src
  have same:=PairRanks.same (Gather.reaching R) (Z.venue h).1 (Z.old h e) (Z.old h f) (Z.venue (C.src e.val)).1 (Z.venue (C.src f.val)).1 p (Z.read h e).src.path q (Z.read h f).src.path a s.src b t.src
  have pairLT {M N:ℕ} (x y:Fin M) (u v:Fin N):finProdFinEquiv (x,u)<finProdFinEquiv (y,v) ↔ x<y ∨ x=y ∧ u<v:=by
    have val (a:Fin M) (b:Fin N):(finProdFinEquiv (a,b)).val=a.val*N+b.val:=by simp only [finProdFinEquiv_apply_val];ring
    rw [Fin.lt_def,val,val,DescentCableDonorNames.digit_lt u.isLt v.isLt];simp only [Fin.lt_def,Fin.ext_iff]
  change finProdFinEquiv (_,_)<finProdFinEquiv (_,_) ↔ _
  rw [pairLT,order,same,s.srcLow,t.srcLow]

/-- The explicit source-key order of the measured normalized stage is exactly
the order that the all-neighbor shared 2-key comparison receives. -/
def of_measured
    (sourceOrder:∀h (e f:Local C h),srcKey C R symm Z h e<srcKey C R symm Z h f ↔ Z.site (Z.src (Z.head h e))<Z.site (Z.src (Z.head h f))):
    Census C (P*P*Q) K L (P*O) where
  addr:=(Measured.roster C R symm Z).address
  source:=srcKey C R symm Z
  ticket:=fun h e=>(Z.read h e).ticket
  mass:=fun h e=>(Z.read h e).weight
  weight:=Z.survives
  chronology h e f:=by
    have same:srcKey C R symm Z h e=srcKey C R symm Z h f ↔ Z.src (Z.head h e)=Z.src (Z.head h f):=by
      constructor
      · intro eqn;apply Z.site.injective;apply le_antisymm
        · apply not_lt.mp;intro no;have bad:=(sourceOrder h f e).mpr no;rw [eqn] at bad;exact (lt_irrefl _) bad
        · apply not_lt.mp;intro no;have bad:=(sourceOrder h e f).mpr no;rw [eqn] at bad;exact (lt_irrefl _) bad
      · intro eqn;apply le_antisymm
        · apply not_lt.mp;intro no;have bad:=(sourceOrder h f e).mp no;rw [eqn] at bad;exact (lt_irrefl _) bad
        · apply not_lt.mp;intro no;have bad:=(sourceOrder h e f).mp no;rw [eqn] at bad;exact (lt_irrefl _) bad
    rw [Z.chronology,grouped_compare _ _ _ _ _ _ (Z.active h e) (Z.active h f),sourceOrder,same]
    by_cases sameSrc:Z.src (Z.head h e)=Z.src (Z.head h f)
    · have old:=(Z.tape.sourceKey_lt Z.src Z.site Z.width _ _ (Z.active h e) (Z.active h f) sameSrc).symm.trans (Z.shortTicket h e f sameSrc)
      rw [old]
    · simp [sameSrc]

end
end Hierarchy.DescentParallelBase.Incidence

end OAI
