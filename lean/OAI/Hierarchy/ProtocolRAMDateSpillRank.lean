import OAI.Hierarchy.ProtocolRAMDateSpillDirectory
import OAI.Hierarchy.ProtocolRAMDateSpillEarlier
import OAI.Hierarchy.ProtocolRAMPurchaseInventory
import OAI.Hierarchy.ProtocolRAMTurnReplayed
import OAI.Hierarchy.TaggedWireCoreSpillLayout

namespace OAI
/-! # Native per-date rank of actual weighted spill visits on the original physical wires -/

noncomputable section
namespace Hierarchy.ProtocolRAMDateSpillRank
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage CoreBoard WireTelescope
open LinearAlgebra.SpectralBooks ChordGraph SiteTensor
open ThreeFlat.RAM PhysicalProcedure
open ProtocolRAM ProtocolRAM.Calendar ProtocolRAM.RouteSettlement ProtocolRAMTurnPrefix ProtocolRAMTurnReplayed
open scoped Classical BigOperators Fin.CommRing
variable {W h d k K edges : ℕ} {S : PurchaseSampler} {π : Equiv.Perm (Fin (2^h))}
    {place : Site h d k→Fin K} (B : Mount (S:=S) π place edges)
    (inj : Function.Injective place) (pad : Chord K) (o : CoreRoute.Orders h d k)

def dateBanks (b : Banks) (spill zero : Bank) : Banks :=
  {b with stock:=spill,reserved:=zero,used:=zero}

/-- The actual stock address for a commodity is independent of the position
along its walk. Repeated edges in that walk have distinct entries. -/
def sourceAt (i : Fin (coreCount o)) : Commodity (Fin (2^h)) (Stages h d) k :=
  ((CoreRoute.corePrefix o).symm i).1

def wireAt (i : Fin (coreCount o)) : Fin edges := (spillEnum B o i).edge

def loadAt (spill : Bank) (m : Memory W) (i : Fin (coreCount o)) : ℕ :=
  actual spill m (PurchaseInventory.slot (sourceAt o i))

structure RankRead (lo : ℕ) (spill : Bank) (m out : Memory W) : Prop where
  key : ∀i : Fin (coreCount o), out (lo+(edges+i.val))=((wireAt B o i).val : Word W)
  width : ∀i : Fin (coreCount o),
    out ((weight lo (edges+coreCount o)).base+(edges+i.val))=(loadAt o spill m i : Word W)
  rank : ∀i : Fin (coreCount o),
    out (ranks lo (edges+coreCount o) edges+4*(edges+i.val)+3)=
      (TaggedShorterCommonScan.earlier (wireAt B o) (loadAt o spill m) i.val (wireAt B o i) : Word W)
  frame : ∀a<lo,out a=m a
  total : ∀e : Fin edges, out (counters lo (edges+coreCount o)+e.val)=
    ((∑i : Fin (coreCount o), if wireAt B o i=e then loadAt o spill m i else 0 : ℕ) : Word W)

/-- Coalescing all occurrences recovers the original weighted walk load,
including repeated visits to one wire by a single commodity. -/
theorem RankRead.total_routeLoad {lo : ℕ} {spill : Bank} {m out : Memory W}
    (read : RankRead B o lo spill m out) (e : Fin edges) :
    out (counters lo (edges+coreCount o)+e.val)=
      (routeLoad B.ordinary (fun c=>actual spill m (PurchaseInventory.slot c)) e : Word W) := by
  let stock:=fun c : Commodity (Fin (2^h)) (Stages h d) k=>actual spill m (PurchaseInventory.slot c)
  let f:=fun a : RouteOccurrence B.ordinary (Empty.elim : Empty→List (Fin edges)) =>
    if a.edge=e then a.weight stock Empty.elim Empty.elim else 0
  have order : (∑i, if wireAt B o i=e then loadAt o spill m i else 0)=∑a,f a :=
    (spillEnum B o).sum_comp f
  have accounts : (∑a,f a)=routeLoad B.ordinary stock e := by
    simpa [f,routeLoad] using route_occurrences_sum B.ordinary
      (Empty.elim : Empty→List (Fin edges)) stock Empty.elim Empty.elim e
  exact (read.total e).trans (congrArg (fun n : ℕ=>(n : Word W)) (order.trans accounts))

include inj pad in
/-- This is the native weighted prefix program restricted to the early commodity
rows of the existing kind/index directory. The paid page has been cleared. -/
theorem run (lo : ℕ) (b : Banks) (spill zero : Bank) (m : Memory W)
    (cj : Columns h d×Fin k→ℕ)
    (full : Directory b m (CoreRoute.enum B o) PurchaseInventory.slot cj)
    (capacity : edges≤zero.size) (word : edges≤2^W)
    (cleared : ∀e : Fin edges,m (zero.base+e.val)=0)
    (inputs : ∀cell∈[zero,b.index,b.kind,spill],cell.Fits W lo)
    (room : endAt lo (edges+coreCount o) edges<2^W) (wide : 2<2^W) :
    ∃out,(procedure W lo edges (coreCount o) (dateBanks b spill zero) zero).Exec m out
      (time lo edges (coreCount o) (dateBanks b spill zero) zero) ∧ RankRead B o lo spill m out := by
  let L:=B.spillLayout inj pad
  let ord:=spillEnum B o
  let bank:=dateBanks b spill zero
  let key:=L.nativeEdge ord
  let width:=L.nativeWidth ord (fun _=>0) (fun i=>actual spill m (PurchaseInventory.slot i))
    (fun j : Empty=>actual zero m (Empty.elim j)) (fun j : Empty=>actual zero m (Empty.elim j))
  have old:=restrictDirectory B o b spill m PurchaseInventory.slot cj full
  have present : Directory bank m ord PurchaseInventory.slot Empty.elim :=
    ⟨old.headKind,old.headIndex,old.tailKind,old.tailIndex⟩
  have reads : ∀cell∈[zero,bank.index,bank.kind,bank.stock,bank.reserved,bank.used],cell.Fits W lo := by
    intro cell hi
    exact inputs cell (by simpa [bank,dateBanks,or_assoc,or_left_comm,or_comm] using hi)
  have first : ∀e : Fin edges,width (e.castAdd (coreCount o))=0 := by
    intro e
    simp only [width,SettledMatrix.Layout.nativeWidth,finSumFinEquiv_symm_apply_castAdd]; rfl
  have keyTail : ∀i : Fin (coreCount o),key (i.natAdd edges)=wireAt B o i := by
    intro i
    simp only [key,SettledMatrix.Layout.nativeEdge,finSumFinEquiv_symm_apply_natAdd]; rfl
  have widthTail : ∀i : Fin (coreCount o),width (i.natAdd edges)=loadAt o spill m i := by
    intro i
    simp only [width,SettledMatrix.Layout.nativeWidth,finSumFinEquiv_symm_apply_natAdd]; rfl
  obtain ⟨out,exec,ranksAt,frame,keys,weights,counts⟩:=ProtocolRAMTurnReplayed.run_counts L ord lo bank zero m
    PurchaseInventory.slot Empty.elim (fun _=>0) present capacity word (fun e=>by rw [cleared]; rfl)
    reads room wide (fun j=>j.elim)
  refine ⟨out,exec,?_,?_,?_,frame,?_⟩
  · intro i
    exact (keys (i.natAdd edges)).trans (congrArg (fun e : Fin edges=>(e.val : Word W)) (keyTail i))
  · intro i
    exact (weights (i.natAdd edges)).trans (congrArg (fun v : ℕ=>(v : Word W)) (widthTail i))
  · intro i
    have amount:=ranksAt (i.natAdd edges)
    change out (ranks lo (edges+coreCount o) edges+4*(edges+i.val)+3)=
      (TaggedShorterCommonScan.earlier key width (edges+i.val) (key (i.natAdd edges)) : Word W) at amount
    rw [keyTail,earlier_tail key width (wireAt B o) (loadAt o spill m) first keyTail widthTail] at amount
    exact amount

  · intro e
    have raw:=counts e
    change out (counters lo (edges+coreCount o)+e.val)=
      ((∑i : Fin (edges+coreCount o),if key i=e then width i else 0 : ℕ) : Word W) at raw
    simpa only [Fin.sum_univ_add,first,ite_self,Finset.sum_const_zero,Nat.zero_add,keyTail,widthTail] using raw

end Hierarchy.ProtocolRAMDateSpillRank
end

end OAI
