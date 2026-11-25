import OAI.Hierarchy.DescentScalarVenueFields
import OAI.Hierarchy.DescentScalarVenueLanding
import OAI.Hierarchy.DescentIssuedDonorChart

namespace OAI
/-! # Connecting finite incidence tickets to the seven actual actor venue tests -/
namespace Hierarchy.DescentScalarVenueMask
open DescentSIMDLookup DescentSharedCableNames DescentPacking.PackedMatch.Local DescentPackedActorMask
open DescentHostDirectory DescentHostDirectory.SiteDecode DescentHaloWalkRAM
open scoped Classical Fin.CommRing
noncomputable section
variable {U I X J V : Type} [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
variable {H D k gain slots low r cap G : ℕ}
local notation "P"=>breadth D
local notation "raw"=>2^(k+1)*slots
local notation "K"=>1+cap*6

omit [DecidableEq J] [DecidableEq V] in
theorem low_injective (a b : Key (J×V)) (legalA : a∈keys k slots) (legalB : b∈keys k slots) :
    a.1=b.1 ∧ localNumber k slots a=localNumber k slots b ↔ a=b :=by
  constructor
  · rintro ⟨top,lowEq⟩
    let id: (J×V)↪ℕ:=(Fintype.equivFin (J×V)).toEmbedding.trans Fin.valEmbedding
    apply packed_inj (rank:=id) id.injective legalA legalB
    have local_ : nodeNumber a.2.1.1 a.2.1.2*slots+a.2.2=nodeNumber b.2.1.1 b.2.1.2*slots+b.2.2:=by simpa [localNumber,packedNumber] using lowEq
    simp only [packedNumber,top,Nat.add_mul,Nat.add_assoc,local_]
  · rintro rfl;exact ⟨rfl,rfl⟩

variable (place : U→J×V) (block_ : U→Fin r) (site : X→U) (actorKey : X→Key (J×V))
variable (slot_ : X→Fin (1+cap*6)) (vertices : V↪Fin H) (groups : J↪Fin G)
variable (adj : Fin H→Fin D→Option (Fin H)) (step : J×V→Fin D→Option (J×V))
    (sr : ∀z i y,step z i=some y→adj (vertices z.2) i=some (vertices y.2)) (preserve : ∀z i y,step z i=some y→y.1=z.1)
local notation "walks"=>Gather.reaching adj
variable (tokens : Fin r→Fin (1+cap*6)→Fin H→Fin G→Ticket (breadth D) (2^(k+1)*slots))
variable (hub : J×V→Bool) (flags : Fin H→Fin G→Cell 1)
    (flagAt : ∀z : J×V,decide (flags (vertices z.2) (groups z.1)≠0)=hub z)

/-- These are reads of the source descriptor, before any geometric
movement. At a legal actor the extracted two-hop route comes from its
owner register. A missing local occupancy or selection has the zero tag. -/
structure Descriptors (slots k : ℕ) (p : U→J×V) (b : U→Fin r) (parent : X→U) (slot : X→Fin (1+cap*6)) (key : X→Key (J×V))
    (vertices : V↪Fin H) (groups : J↪Fin G) (step : J×V→Fin D→Option (J×V))
    (tokens : Fin r→Fin (1+cap*6)→Fin H→Fin G→Ticket (breadth D) (2^(k+1)*slots)) : Prop where
  live : ∀x,∃route : Walk,tokens (b (parent x)) (slot x) (vertices (p (parent x)).2) (groups (p (parent x)).1)=issue D slots (2^(k+1)*slots) route ∧
    walked step (p (parent x)) route (key x)
  absent : ∀b' s h g,(¬∃x,b (parent x)=b' ∧ slot x=s ∧ vertices (p (parent x)).2=h ∧ groups (p (parent x)).1=g)→tokens b' s h g=none

include sr preserve flagAt in
theorem accepted (stock : Descriptors slots k place block_ site slot_ actorKey vertices groups step tokens)
    (valid : ∀x,actorKey x∈keys k slots) (dest : Key (J×V)) (legal : dest∈keys k slots)
    (l : Fin low) (name : localNumber k slots dest=l.val) (d : Fin (P*r)) (s : Fin K) :
    DescentScalarVenueMask.fields walks tokens flags k gain slots low (vertices dest.1.2) (groups dest.1.1) (finProdFinEquiv (d,s))=Packed.token (some l) ↔
      let z : Fin P×Fin r := finProdFinEquiv.symm d
      ∃x,DescentSortedRoster.indexed walks (vertices dest.1.2) z.1=some (vertices (place (site x)).2) ∧ z.2=block_ (site x) ∧
        (place (site x)).1=dest.1.1 ∧ slot_ x=s ∧ mergeHub hub k gain (actorKey x)=dest :=by
  let z:Fin P×Fin r:=finProdFinEquiv.symm d
  let recv:=vertices dest.1.2;let g:=groups dest.1.1
  let absent : returned k gain slots raw low walks z.1 recv (flags recv g) none≠Packed.token (some l):=by
    intro yes;obtain ⟨_,_,impossible,_,_⟩:=(returned_iff ..).1 yes;cases impossible
  simp only [DescentScalarVenueMask.fields,Equiv.symm_apply_apply]
  change returned k gain slots raw low walks z.1 recv (flags recv g)
    ((DescentSortedRoster.indexed walks recv z.1).bind (fun donor=>tokens z.2 s donor g))=Packed.token (some l) ↔ _
  cases h : DescentSortedRoster.indexed walks recv z.1 with
  | none =>
    simp only [Option.bind_none]
    constructor
    · exact fun yes => (absent yes).elim
    · rintro ⟨x,impossible,_⟩
      simp only [reduceCtorEq] at impossible
  | some donor=>
    simp only [Option.bind_some]
    have eqn (x : X) (whereH : donor=vertices (place (site x)).2) (atB : z.2=block_ (site x)) (atG:(place (site x)).1=dest.1.1) (atS:slot_ x=s) :
        returned k gain slots raw low walks z.1 recv (flags recv g) (tokens z.2 s donor g)=Packed.token (some l) ↔ mergeHub hub k gain (actorKey x)=dest:=by
      obtain ⟨route,token,issued⟩:=stock.live x
      have position : DescentSortedRoster.indexed walks recv z.1=some (vertices (place (site x)).2):=h.trans (congrArg some whereH)
      rw [show tokens z.2 s donor g=issue D slots raw route from by rw [atB,←atS,whereH,←show groups (place (site x)).1=g from congrArg groups atG];exact token]
      rw [grouped_landing step vertices adj sr preserve (place (site x)) route (actorKey x) (valid x) issued dest.1 z.1 position atG hub (flags recv g) (flagAt _) l,←name]
      have top :(mergeHub hub k gain (actorKey x)).1=(actorKey x).1:=by unfold mergeHub;split <;> rfl
      rw [←top,low_injective _ _ (merged_mem_keys hub k gain slots (valid x)) legal]
    constructor
    · intro won
      have exists_ : ∃x,block_ (site x)=z.2 ∧ slot_ x=s ∧ vertices (place (site x)).2=donor ∧ groups (place (site x)).1=g:=by
        by_contra no;exact absent ((stock.absent z.2 s donor g no) ▸ won)
      obtain ⟨x,b,sl,pos,group_⟩:=exists_;have same:=groups.injective group_
      exact ⟨x,by simpa only [h] using h.trans (congrArg some pos.symm),b.symm,same,sl,(eqn x pos.symm b.symm same sl).1 won⟩
    · rintro ⟨x,seen,atB,atG,atS,arrived⟩
      have pos : some donor=some (vertices (place (site x)).2):=by simpa only [h] using seen
      exact (eqn x (Option.some.inj pos) atB atG atS).2 arrived

include sr preserve flagAt in
omit [DecidableEq J] [DecidableEq V] in
/-- A hit at any physical address recovers a real source actor, including addresses
for which the receiver has no previously known mathematical key. -/
theorem actor_of_hit (stock : Descriptors slots k place block_ site slot_ actorKey vertices groups step tokens)
    (valid : ∀x,actorKey x∈keys k slots) (h : Fin H) (g : Fin G) (l : Fin low)
    (d : Fin (P*r)) (s : Fin K)
    (hit : DescentScalarVenueMask.fields walks tokens flags k gain slots low h g (finProdFinEquiv (d,s))=Packed.token (some l)) :
    ∃x,vertices (actorKey x).1.2=h ∧ groups (actorKey x).1.1=g ∧
      localNumber k slots (mergeHub hub k gain (actorKey x))=l.val ∧ slot_ x=s :=by
  let z : Fin P×Fin r:=finProdFinEquiv.symm d
  simp only [DescentScalarVenueMask.fields,Equiv.symm_apply_apply] at hit
  change returned k gain slots raw low walks z.1 h (flags h g)
    ((DescentSortedRoster.indexed walks h z.1).bind (fun v=>tokens z.2 s v g))=Packed.token (some l) at hit
  have missing : returned k gain slots raw low walks z.1 h (flags h g) none≠Packed.token (some l):=by
    intro eqn;obtain ⟨_,_,bad,_,_⟩:=(returned_iff ..).1 eqn;cases bad
  cases found : DescentSortedRoster.indexed walks h z.1 with
  | none=>rw [found,Option.bind_none] at hit;exact (missing hit).elim
  | some v=>
    rw [found,Option.bind_some] at hit
    have ex : ∃x,block_ (site x)=z.2 ∧ slot_ x=s ∧ vertices (place (site x)).2=v ∧ groups (place (site x)).1=g:=by
      by_contra no;rw [stock.absent _ _ _ _ no] at hit;exact missing hit
    obtain ⟨x,b,sl,vn,gn⟩:=ex
    obtain ⟨route,printed,truth⟩:=stock.live x
    have issued : tokens z.2 s v g=issue D slots raw route:=by simpa only [b,sl,vn,gn] using printed
    rw [issued] at hit
    have group_ : groups (actorKey x).1.1=g:=(congrArg groups (DescentRawCablePanel.kept_group Prod.fst step preserve truth)).trans gn
    have flag (same : vertices (actorKey x).1.2=h) : decide (flags h g≠0)=hub (actorKey x).1:=by rw [←same,←group_];exact flagAt _
    have target_:= (landing step (fun a=>vertices a.2) adj sr (place (site x)) route (actorKey x) (valid x) truth h z.1
      (found.trans (congrArg some vn.symm)) hub (flags h g) flag l).1 hit
    exact ⟨x,target_.1,group_,target_.2,sl⟩

end
end Hierarchy.DescentScalarVenueMask

end OAI
