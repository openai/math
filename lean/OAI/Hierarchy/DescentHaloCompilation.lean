import OAI.Hierarchy.DescentHaloAtSource
import OAI.Hierarchy.DescentHaloRankProgram
import OAI.Hierarchy.DescentHaloDonorChart
import OAI.Hierarchy.DescentSiteNameRead

namespace OAI
/-! # Native shared donor chart and the previous world’s actual site numbering -/
namespace Hierarchy.DescentHaloCompilation
open DescentHaloWalkRAM DescentHaloDonorChart DescentCableDonorNames DescentOrdinaryDonorHalo
open DescentColonies DescentHostDirectory DescentSixParty DescentStageEdgeReceipt
open Computability.VPVNP.BurstRAM PrivateRAM DescentPacking
open ThreeFlat.RAM PhysicalProcedure ProtocolRAM
open scoped Classical BigOperators Fin.CommRing
noncomputable section
variable {H D w k : ℕ} {F P J V U : Type} [Fintype U] [DecidableEq J] [DecidableEq V]
variable (near : V→Finset V) (name : V↪Fin H) (R : Fin H→Fin D→Option (Fin H))
variable (listed : ∀v u,u∈near v→∃i,R (name v) i=some (name u))
variable (pos : U→J×V) (block : U→Block k) (coord : Function.Injective fun u=>(pos u,block u))

section Prior
variable [Field F] [Fintype J] [Fintype V] {d age : ℕ} {sz : P→ℕ}
  {W : MarkedWorld F d P sz} {G : PoweredGadget F} {price ε : ℝ} (A : GroupStage W G price ε J V age)
variable (groupID : J↪ℕ) (coords : Function.Injective (fun u=>(A.pos u,A.block u)))
  (named : A.SiteNamed (groupRank groupID (name.trans Fin.valEmbedding)))

include named

/-- The multiplicity-counting native rank is valid in the exact canonical
ancestry comparator of `ordinary`. The old group prefix cancels on this
specific chart because all measured walks preserve the group. -/
theorem old_order {Q : Type} (srcKey : Q→Key (J×V)) (v : Q)
    (x y : ↥(siteSet (groupedNear A.near) A.pos (srcKey v)))
    (input : ∀v u,u∈A.near v→∃i,R (name v) i=some (name u)) :
    let h:=atSource A.near name R input A.pos A.block coords srcKey
    h.slot v x<h.slot v y ↔ originalId W.graph.Site x.val<originalId W.graph.Site y.val :=by
  intro h
  let group:=groupRank groupID (name.trans Fin.valEmbedding)
  let number:=A.siteFrom group coords
  have id (p : W.graph.Site) : originalId W.graph.Site p=(DescentPhysicalOrder.physical number p).val:=
    (named p).trans (DescentPhysicalOrder.physical_val number p).symm
  have xgroup:=(common A.near 4 (srcKey v).1 (A.pos x.val) (Finset.mem_filter.mp x.property).2).1
  have ygroup:=(common A.near 4 (srcKey v).1 (A.pos y.val) (Finset.mem_filter.mp y.property).2).1
  rw [id x.val,id y.val]
  refine (ordered A.near name R input A.pos A.block coords (srcKey v) x y).trans ?_
  refine Iff.trans ?_ (DescentPhysicalOrder.physical_lt_iff number x.val y.val).symm
  change _ ↔ (groupID (A.pos x.val).1*pitch (name.trans Fin.valEmbedding)+(name (A.pos x.val).2).val)*2^age+(A.block x.val).val<
    (groupID (A.pos y.val).1*pitch (name.trans Fin.valEmbedding)+(name (A.pos y.val).2).val)*2^age+(A.block y.val).val
  simp only [xgroup,ygroup,Nat.add_mul,Nat.add_assoc,Nat.add_lt_add_iff_left]
end Prior

/-- The two real scans compose at the very same endpoint column. The only
additional read in the second pass is its public per-(rack,path) start. -/
theorem execute (W : DescentHaloWalkRAM.Banks) (T : Ranks.Columns) (out : ℕ)
    (first : Fits W T.endpoints.base H D w) (second : Ranks.Fits T out H (breadth D) w)
    (m : Memory w) (input : Reads W R m)
    (header : ∀(v:Fin H)(p:Fin (breadth D)),m (T.start.base+(Ranks.id v p).val)=((v.val*breadth D:ℕ):Word w))
    (before : T.start.base+T.start.size≤T.endpoints.base) :
    let n:=H*breadth D
    let f:=body W H D 4
    let g:=Ranks.body T (breadth D)
    let mid:=image T.endpoints.base n f m
    let result:=image out n g mid
    ((scan w T.endpoints.base n f).seq (scan w out n g)).Exec m result
       ((4+n*(2*f.work+4))+(4+n*(2*g.work+4))) ∧
      (∀(v:Fin H)(p:Fin (breadth D)),result (out+(row v p).val)=(Ranks.earlier (endpoint R) v (endpoint R v p):Word w)) ∧
      CheapCode ((scan w T.endpoints.base n f).seq (scan w out n g)) :=
  rank_rows R W T out first second m input header before


end
end Hierarchy.DescentHaloCompilation

end OAI
