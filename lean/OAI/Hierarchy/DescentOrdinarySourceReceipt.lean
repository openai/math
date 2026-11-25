import OAI.Hierarchy.DescentIncidentRankReturned
import OAI.Hierarchy.DescentOrdinarySignedRanks

namespace OAI
/-! An ordinary cable's source ordinal traverses two measured four-hop
charts. The first pass returns the genuine source rank to its prior donor.
The second reads that donor at either new endpoint. -/
namespace Hierarchy.DescentParallelBase.SourceReturn
open DescentSharedCableNames DescentSIMDLookup DescentPackedColony DescentHaloWalkRAM DescentPackedZip
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure ProtocolRAM
open scoped Classical Fin.CommRing
noncomputable section
variable {H P Q G b M w base:ℕ}
local notation "T" => P*(Q*P)
local notation "N" => H*chunks G M
local notation "shape" => (Packed.bits T+b)*M
local notation "cost" => T*2*2^shape

theorem mounted_before (ports:Ports P) (chart:Fin H→Fin P→Option (Fin H)) (m m':Memory w) (mounted:Mounted ports chart m G M)
    (prior:Bank) (access:Accessible ports prior H G M w base) (kept:∀u,u<base→m' u=m u):
    Mounted ports chart m' G M:=by
  have word (B:Bank) (f:B.Fits w base) (i:ℕ) (hi:i<B.size):m' (B.base+i)=m (B.base+i):=kept _ ((Nat.add_lt_add_left hi _).trans_le f.2.2)
  constructor
  · intro p i; exact (word _ (access.ids i) _ ((row H G M p).isLt.trans_le (access.idsRoom i))).trans (mounted.ids p i)
  · intro v i;have rv:v.val*P+i.val<H*P:=(Nat.add_lt_add_left i.isLt _).trans_le (by rw [←Nat.succ_mul];exact Nat.mul_le_mul_right _ v.isLt)
    exact (word _ access.roster _ (rv.trans_le access.rosterRoom)).trans (mounted.roster v i)
  · intro v;exact (word _ access.offsets _ (v.isLt.trans_le access.offRoom)).trans (mounted.offsets v)
  · intro p;exact (word _ access.chunks _ ((row H G M p).isLt.trans_le access.chunkRoom)).trans (mounted.chunks p)

def donated (R:Fin H→Fin P→Option (Fin H)) (rank:Fin Q→Fin P→Fin H→Fin G→Cell b) (choice:Fin H→Fin G→Option (Fin T))
    (u:Fin P) (v:Fin H) (g:Fin G):Cell b:=
  (Gather.select R v u).elim 0 (fun old=>RAM.output R rank choice old g)

theorem delivered (R:Fin H→Fin P→Option (Fin H)) (rank:Fin Q→Fin P→Fin H→Fin G→Cell b) (q:Fin H→Fin G→Option (Fin T))
    (ports keep:Ports P) (bank:Fin Q→Fin P→Bank) (query:Expr) (donor:Bank) (destination:ℕ) (u:Fin P) (old:Memory w)
    (prior:Bank) (visit:Accessible keep prior H G M w base)
    (before:∀l r,Accessible ports (bank l r) H G M w base) (queryFits:query.Fits w base)
    (walks:Mounted ports R old G M) (unique:Mounted keep (Gather.select R) old G M) (inputs:Source query (fun v g=>Packed.token (q v g)) M old)
    (ranks:∀l r,Reads (bank l r) (rank l r) M old) (apart:base+cost≤donor.base)
    (ordering:donor.base+N≤destination) (room:destination+N<2^w) (canRead:Accessible keep donor H G M w destination):
    let pages:=RAM.ROM.book P Q b M
    let mounted:=DescentOrdinaryAtomFieldRAM.ROM.mount pages shape w base
    let loaded:=DescentOrdinaryAtomFieldRAM.ROM.after pages shape base old
    let e:=RAM.body (RAM.ROM.table P Q b M base) ports bank query H
    let first:=image donor.base N e loaded
    let f:=peerExpr keep donor H u
    let done:=image destination N f first
    (((mounted.seq (scan w donor.base N e)).seq (scan w destination N f))).Exec old done (((4+10*cost)+(4+N*(2*e.work+4)))+(4+N*(2*f.work+4))) ∧
    (∀p:Row H G M,done (destination+(row H G M p).val)=((data (donated R rank q u) p).val:Word w)) ∧
    (∀a,a<base ∨ destination+N≤a→done a=old a) ∧ CheapCode ((mounted.seq (scan w donor.base N e)).seq (scan w destination N f)):=by
  intro pages mounted loaded e first f done
  have oldRoom:donor.base+N<2^w:=ordering.trans_lt ((Nat.le_add_right destination N).trans_lt room)
  obtain ⟨firstExec,oldRanks,far,firstCheap⟩:=RAM.ROM.fresh (base:=base) R rank q ports bank query donor old before queryFits walks inputs ranks apart oldRoom
  have live:Mounted keep (Gather.select R) first G M:=mounted_before keep _ old first unique prior visit (fun a ha=>far a (.inl ha))
  obtain ⟨nextExec,printed,cheap⟩:=Gather.gather keep donor destination u R (RAM.output R rank q) first canRead live oldRanks room
  refine ⟨firstExec.then nextExec,printed,?_,cheap_seq firstCheap cheap⟩
  intro a away
  rcases away with below|after
  · have order:base≤destination:=(Nat.le_add_right ..).trans (apart.trans ((Nat.le_add_right ..).trans ordering))
    exact (ProtocolRAMGeneratedWrite.frame_image destination N f first a (.inl (below.trans_le order))).trans (far a (.inl below))
  · exact (ProtocolRAMGeneratedWrite.frame_image destination N f first a (.inr after)).trans (far a (.inr (ordering.trans ((Nat.le_add_right ..).trans after))))

section Measured
variable {U E X T₀ V:Type} [Fintype E] [DecidableEq U] [Fintype X] [Fintype T₀]
  {n D O K L:ℕ} {B:Ends U n} (C:Blocks B E) (R:Fin H→Fin D→Option (Fin H))
  (symm:∀v u i,R v i=some u→∃j,R u j=some v) (Z:ParentFilter.Measured C R X T₀ V Q O K L)
local notation "p₀" => breadth D
local notation "rc" => Gather.reaching R
variable (orders:∀h (e f:Local C h),Incidence.srcKey C R symm Z h e<Incidence.srcKey C R symm Z h f ↔ Z.site (Z.src (Z.head h e))<Z.site (Z.src (Z.head h f)))
variable (hosts:Fin Q→Fin H→Fin G→Option U) (fit:∀u,(B.incident u).card≤L)

theorem received_rank (recv src:U) (e:Local C src) (g:Fin G) (p walk:Fin p₀)
    (seen:Gather.select rc (Z.venue recv).1 walk=some (Z.old src e))
    (forward:rc (Z.old src e) p=some (Z.venue src).1) (present:hosts (Z.venue src).2 (Z.venue src).1 g=some src)
    (choice:Fin H→Fin G→Option (Fin (p₀*(Q*p₀)))) (low:Cell (Packed.bits Q)) (lowEq:low.val=(Z.venue src).2.val)
    (issued:Packed.token (choice (Z.old src e) g)=Query.finish p₀ Q (Query.forward p₀ Q (Packed.token (some p)) low)
      (Query.packedRoute R (Z.old src e) (some p))):
    (donated rc (sheet C R symm Z orders hosts fit (Z.loc (Z.raw src e)).2) choice walk (Z.venue recv).1 g).val=Incidence.pos C fit src e:=by
  simp only [donated,seen,Option.elim_some]
  exact returned C R symm Z orders hosts fit src e g p forward present choice low lowEq issued

end Measured
end
end Hierarchy.DescentParallelBase.SourceReturn

end OAI
