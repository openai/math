import OAI.Hierarchy.DescentIncidentMeasuredOrder
import OAI.Hierarchy.DescentDonorSourceReturn
import OAI.Hierarchy.DescentDonorSourceReturnROM

namespace OAI
/-! # The transported source first-slot equals the genuine next cable's source handle -/
namespace Hierarchy.DescentParallelBase.SourceReturn
open DescentHaloWalkRAM DescentSharedCableNames DescentSIMDLookup DescentParallelBase.ParentFilter
open scoped Classical BigOperators Fin.CommRing
noncomputable section
variable {U E X T V : Type} [Fintype E] [DecidableEq U] [Fintype X] [Fintype T]
  {n H D Q O K L G:ℕ} {B:Ends U n} (C:Blocks B E) (R:Fin H→Fin D→Option (Fin H))
  (symm:∀v u i,R v i=some u→∃j,R u j=some v) (Z:Measured C R X T V Q O K L)
local notation "P"=>breadth D
local notation "TQ"=>P*(Q*P)
local notation "reach"=>Gather.reaching R
variable (orders:∀h (e f:Local C h),Incidence.srcKey C R symm Z h e<Incidence.srcKey C R symm Z h f ↔ Z.site (Z.src (Z.head h e))<Z.site (Z.src (Z.head h f)))
local notation "census"=>Incidence.of_measured C R symm Z orders
variable (hosts:Fin Q→Fin H→Fin G→Option U) (fit:∀u,(B.incident u).card≤L)

/-- The physically issued `Incidence.run` word for this absolute source
rack and short candidate address. The old raw-role ordinal is a fixed bank. -/
def sheet (o:Fin O) (low:Fin Q) (back:Fin P):Fin H→Fin G→Cell (Packed.bits L):=
  let f:=Incidence.items C census (hosts low)
  let j:=finProdFinEquiv (back,o)
  Stream.totalWord (f j) f (Incidence.capacity C census (hosts low) fit j)

local notation "shelf"=>sheet C R symm Z orders hosts fit

/-- The executed return sweep can now attach this number at the old donor
before the source and target receive new signed records. All rank digits
in its source table are the actual native all-neighbor comparison results. -/
theorem returned (src:U) (e:Local C src) (g:Fin G) (p:Fin P)
    (forward:reach (Z.old src e) p=some (Z.venue src).1) (present:hosts (Z.venue src).2 (Z.venue src).1 g=some src)
    (choice:Fin H→Fin G→Option (Fin TQ)) (low:Cell (Packed.bits Q)) (lowEq:low.val=(Z.venue src).2.val)
    (issued:Packed.token (choice (Z.old src e) g)=Query.finish P Q (Query.forward P Q (Packed.token (some p)) low)
      (Query.packedRoute R (Z.old src e) (some p))):
    (RAM.output reach (shelf (Z.loc (Z.raw src e)).2) choice (Z.old src e) g).val=Incidence.pos C fit src e:=by
  let loc:=(Measured.roster C R symm Z).address src e
  let tw:Fin P×Fin O:=finProdFinEquiv.symm loc
  have exactOrder:=source_order R C symm Z src e p forward
  have rEq:(Query.packedRoute R (Z.old src e) (some p)).val=tw.1.val:=
    (Query.at_path R _ _).trans exactOrder.1.symm
  have routeAt:choice (Z.old src e) g=some (RAM.key p (Z.venue src).2 tw.1):=by
    have tokens:=issued.trans (Query.certified p (Z.venue src).2 tw.1 low _ lowEq rEq)
    simpa using congrArg (Packed.readToken TQ) tokens
  rw [RAM.actual reach _ choice (Z.old src e) (Z.venue src).1 g p (Z.venue src).2 tw.1 routeAt forward]
  change (∑i,Stream.qty (Incidence.items C census (hosts (Z.venue src).2) (finProdFinEquiv (tw.1,(Z.loc (Z.raw src e)).2)) (Z.venue src).1 g)
    (Incidence.items C census (hosts (Z.venue src).2) i (Z.venue src).1 g))=_
  have index:finProdFinEquiv (tw.1,(Z.loc (Z.raw src e)).2)= (census).addr src e:=by
    rw [←exactOrder.2];exact finProdFinEquiv.apply_symm_apply loc
  rw [index];exact Incidence.at_parent C census (hosts (Z.venue src).2) fit (Z.venue src).1 g src present e

end
end Hierarchy.DescentParallelBase.SourceReturn

end OAI
