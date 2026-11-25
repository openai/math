import OAI.Hierarchy.DescentDepotReceiver
import OAI.Hierarchy.DescentOrdinaryMaterialTicket
import OAI.Hierarchy.DescentPackedRegroup
import OAI.Hierarchy.ProtocolRAMRowChoice

namespace OAI
/-! Reuse the earlier four-hop roster and the true compact successor host pitch for donor reads. -/
namespace Hierarchy.DescentRawCablePanel.DepotRAM.Material.Route
open DescentSIMDLookup DescentPackedZip DescentPackedColony DescentHaloWalkRAM
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure DescriptorExpr
open scoped Classical Fin.CommRing
noncomputable section
variable {H K G r M a w D : ℕ}
local notation "P" => breadth D

def keepPorts (B : DescentOrdinaryDonorRankDirectory.Banks) (v : Ports P) : Ports P := {v with roster:=B.endpoints}

theorem mounted (R : Fin H→Fin D→Option (Fin H)) (B : DescentOrdinaryDonorRankDirectory.Banks) (v : Ports P)
    (m : Memory w) (old : Mounted v (Gather.reaching R) m G M) (ranked : DescentOrdinaryDonorRankDirectory.Reads R B m) :
    Mounted (keepPorts B v) (Gather.select (Gather.reaching R)) m G M :=by
  refine ⟨old.ids,?_,old.offsets,old.chunks⟩
  intro h j
  simpa only [keepPorts,Ranks.id,finProdFinEquiv_apply_val,Nat.add_comm j.val,Nat.mul_comm P h.val,number,target] using ranked.visit h j

def index (H pitch : ℕ) (p : Row K G M) : ℕ :=
  (receiver H pitch p.1).elim (H*chunks G M) (fun old=>(row H G M (old,p.2)).val)

def «prefix» (H K G M pitch : ℕ) (i : ℕ) : ℕ :=
  if yes : i<K*chunks G M then index H pitch ((row K G M).symm ⟨i,yes⟩) else H*chunks G M

def bank (K G M base : ℕ) : Bank := ⟨base,Nat.clog 2 (K*chunks G M+1)⟩

theorem installed (H K G M pitch base : ℕ) (m : Memory w) (p : Row K G M) :
    DescentStaticWordColumn.image base («prefix» H K G M pitch) m (K*chunks G M)
      ((bank K G M base).base+(row K G M p).val)=(index H pitch p:Word w) :=by
  change DescentStaticWordColumn.image _ _ _ _ (base+(row K G M p).val)=_
  rw [DescentStaticWordColumn.read _ _ _ _ (row K G M p).isLt]
  simp only [«prefix»,dite_eq_left (row K G M p).isLt,Fin.eta,Equiv.symm_apply_apply]

def lift (B : Bank) (oldRows : ℕ) (src : Expr) : Expr :=
  let prior:=Expr.lookup B .row
  .branch .eq prior (.lit oldRows) (.lit 0) (src.atRow prior)

private theorem words_zero (h : Fin K) (j : Fin (chunks G M)) :
    (data (fun (_ : Fin K) (_ : Fin G)=>(0:Cell a)) (h,j)).val=0 :=by
  change (finFunctionFinEquiv (fun l : Fin M=>if _:j.val*M+l.val<G then (0:Cell a) else 0)).val=0
  simp

theorem routed (B : Bank) (pitch out : ℕ) (mem : Memory w) (f : Expr) (x : Fin H→Fin G→Cell a)
    (prior : Source f x M mem) (mapFits : B.Fits w out) (size : K*chunks G M≤B.size)
    (safe : H*chunks G M<2^w)
    (mapRead : ∀p : Row K G M,mem (B.base+(row K G M p).val)=(index H pitch p:Word w)) :
    Source (lift B (H*chunks G M) f) (fun (h : Fin K) g=>(receiver H pitch h).elim 0 (fun v=>x v g)) M mem :=by
  rintro ⟨h,j⟩
  let i:=row K G M (h,j)
  have found:= (bank_read B mem (i.isLt.trans_le size) mapFits).trans (mapRead (h,j))
  change (if Comparison.eq.test (B.read mem (i.val:Word w)) ((H*chunks G M:ℕ):Word w) then 0
    else (f.atRow (.lookup B .row)).eval mem (i.val:Word w))=_
  rw [found,eval_atRow]
  change (if Comparison.eq.test ((index H pitch (h,j):ℕ):Word w) _ then 0 else f.eval mem (B.read mem (i.val:Word w)))=_
  rw [found]
  cases got : receiver H pitch h with
  | none=>
    simp only [index,got,Option.elim_none,Comparison.test,beq_iff_eq,ite_true]
    change 0=((data (fun (v : Fin K) g=>(receiver H pitch v).elim 0 (fun q=>x q g)) (h,j)).val:Word w)
    simp [data,got,encode]
  | some u=>
    let old:=row H G M (u,j)
    have ne : (old.val:Word w)≠((H*chunks G M:ℕ):Word w):=by
      intro z;have eqn:=congrArg Fin.val z
      simp only [Fin.val_natCast,Nat.mod_eq_of_lt safe,Nat.mod_eq_of_lt (old.isLt.trans safe)] at eqn
      exact (Nat.ne_of_lt old.isLt) eqn
    simp only [index,got,Option.elim_some,Comparison.test,beq_iff_eq]
    change (if (old.val:Word w) = ((H*chunks G M:ℕ):Word w) then 0 else _) = _
    rw [ite_eq_right ne]
    simpa [data,got] using prior (u,j)

/-- A single group field may be read from an earlier donor census at a different
number of groups. The source can be fed directly by the public overlap/rechunk pass. -/
theorem old_field (R : Fin H→Fin D→Option (Fin H)) (B : DescentOrdinaryDonorRankDirectory.Banks) (ports : Ports P)
    (field mapB : Bank) (pitch out : ℕ) (mem : Memory w) (p : Fin P)
    (hm : 0<M) (hr : 0<r) (x : Fin H→Fin (G*r)→Cell a)
    (source : Reads field x (M*r) mem) (prior : Mounted ports (Gather.reaching R) mem G M)
    (ranks : DescentOrdinaryDonorRankDirectory.Reads R B mem)
    (ok : Accessible (keepPorts B ports) field H G M w out)
    (fit : mapB.Fits w out) (size : K*chunks G M≤ mapB.size) (safe : H*chunks G M<2^w)
    (mapRead : ∀z : Row K G M,mem (mapB.base+(row K G M z).val)=(index H pitch z:Word w)) :
    Source (lift mapB (H*chunks G M) (peerExpr (keepPorts B ports) field H p))
      (fun (h : Fin K) g=>(receiver H pitch h).elim 0 (fun v=>
        (Gather.select (Gather.reaching R) v p).elim 0 (fun u=>groupedRows x u g))) M mem :=by
  apply routed _ pitch out _ _ _ _ fit size safe mapRead
  apply peerSource (keepPorts B ports) field out ok _ mem (mounted R B ports mem prior ranks) _ _ p
  exact regroup_read hm hr field.base mem x source

end
end Hierarchy.DescentRawCablePanel.DepotRAM.Material.Route

end OAI
