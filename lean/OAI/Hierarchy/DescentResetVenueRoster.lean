import OAI.Hierarchy.DescentCompactVenuePeerRead
import OAI.Hierarchy.DescentResetActorPlanes
import OAI.Hierarchy.DescentResetStemRackGeometry
import OAI.Hierarchy.DescentStageVenuePeers
import OAI.Hierarchy.DescentResetHubRectangle

namespace OAI
/-! # The reset's real sorted three-port receiver directory and hub bits -/
namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentCompiler DescentPackedColony DescentSortedRoster DescentResetPeerUnionRAM DescentCompactVenuePeers
open DescentPacking.PackedMatch.Local.Stage DescentGroupPeerOrder DescentDenseHostOrder DescentResetHostSize
open DescentHubBits DescentSIMDLookup ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open DescentPackedExchange
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable {F P:Type} [Field F] {d:ℕ} {bits:P→ℕ} {G:PoweredGadget F} {q ε:ℝ}
  {W:MarkedWorld F d P bits} {S:AtomSchedule} {k age z D n ht C f gain cut tail wire hist:ℕ}
  {ctl:ResetRates G S k D n ht C f gain cut tail}
  {old:Reached W G q ε S k age z D wire hist} (B:ClosedReset old ctl)
  {H R:ℕ}(wide:Fintype.card old.V≤H)(newRoom:Fintype.card B.next.V≤R)
local notation "Z" => B.reset
local notation "T" => B.terminals
local notation "VN" => B.next.V
local notation "A" => B.next.placement
local notation "r" => (Z).k-(T).commonDepth
local notation "height" => GroupStage.depthBound D n f gain
local notation "pool" => DescentDenseHostOrder.roster (Z).graph r height
local notation "all" => H*(pool).card
local notation "sourceId" => (B.frame.host.symm.toEmbedding.trans old.vertex).trans (Fin.castLEEmb wide)
local notation "raw" => (Z).rawHostRank T sourceId
local notation "id_" => B.next.vertex.trans (Fin.castLEEmb newRoom)

variable (found : Fin (H * (DescentDenseHostOrder.roster B.reset.graph (B.reset.k-B.terminals.commonDepth) (GroupStage.depthBound D n f gain)).card) →
    Fin 3 → Option (Fin (H * (DescentDenseHostOrder.roster B.reset.graph (B.reset.k-B.terminals.commonDepth) (GroupStage.depthBound D n f gain)).card)))
  (four : ∀ v : B.next.V, present (selfPeers found) (B.reset.rawHostRank B.terminals ((B.frame.host.symm.toEmbedding.trans old.vertex).trans (Fin.castLEEmb wide)) v) =
    (insert v (B.reset.emittedNear B.terminals v)).map (B.reset.rawHostRank B.terminals ((B.frame.host.symm.toEmbedding.trans old.vertex).trans (Fin.castLEEmb wide))))
  (selfFlag : ∀ v : B.next.V, (∀ j, found (B.reset.rawHostRank B.terminals ((B.frame.host.symm.toEmbedding.trans old.vertex).trans (Fin.castLEEmb wide)) v) j ≠ some (B.reset.rawHostRank B.terminals ((B.frame.host.symm.toEmbedding.trans old.vertex).trans (Fin.castLEEmb wide)) v)) ↔
    v ∉ B.reset.emittedNear B.terminals v)

include four selfFlag in
private theorem realFace (x:VN){j:Fin 3}{a:Fin all}(hit:found (raw x) j=some a):
    ∃u∈(Z).emittedNear T x,raw u=a:=by
  have inside:a∈present found (raw x):=Finset.mem_filter.mpr ⟨Finset.mem_univ _,j,hit⟩
  rw [measured_neighbors found raw ((Z).emittedNear T) x (four x) (selfFlag x)] at inside
  exact Finset.mem_map.mp inside

def rosterDirectory:Directory (R:=all) (H:=R) (Fintype.card VN) where
  uid:=(denseOrder B).symm.toEmbedding.trans raw
  cap:=newRoom
  «raw»:=found
  closed h j a hit:=by
    obtain ⟨v,_,eq⟩:=realFace B wide found four selfFlag ((denseOrder B).symm h) hit
    refine ⟨denseOrder B v, ?_⟩
    exact (congrArg (raw) ((denseOrder B).symm_apply_apply v)).trans eq

local notation "dir" => rosterDirectory B wide newRoom found four selfFlag
/-- Raw peers and the two ranks are exactly the public addresses of the stored directory. -/
theorem resident_directory {w floor:ℕ}(ports:Inputs)(m:Memory w)(ok:Room ports floor w)
    (invSize:Fintype.card VN≤ports.inverse.size)(rankSize:all≤ports.forward.size)
    (peerSize:∀j,all≤(ports.neighbor j).size)(count:m ports.count.base=(Fintype.card VN:Word w))
    (inverse:∀u:VN,m (ports.inverse.base+(B.next.vertex u).val)=((raw u).val:Word w))
    (ranks:∀u:VN,m (ports.forward.base+(raw u).val)=((B.next.vertex u).val:Word w))
    (adj:∀u:VN,∀j,m ((ports.neighbor j).base+(raw u).val)=(DescentPackedColony.target (found (raw u) j):Word w)):
    (dir).Stored ports m:=by
  have here (u:Fin (Fintype.card VN)):B.next.vertex ((denseOrder B).symm u)=u:=(denseOrder B).apply_symm_apply u
  constructor
  · simpa using (DescentPackedZip.bank_read ports.count m (i:=0) ok.count.1 ok.count).trans (by simpa using count)
  · intro u
    rw [DescentPackedZip.bank_read ports.inverse m (u.isLt.trans_le invSize) ok.inverse]
    change m (ports.inverse.base+u.val) = ((raw ((denseOrder B).symm u)).val : Word w)
    simpa only [here] using inverse ((denseOrder B).symm u)
  · intro u
    let v:VN:=(denseOrder B).symm u
    change ports.forward.read m ((raw v).val:Word w)=(u.val:Word w)
    rw [DescentPackedZip.bank_read ports.forward m ((raw v).isLt.trans_le rankSize) ok.forward,ranks,here]
  · intro u j
    let v:VN:=(denseOrder B).symm u
    exact (DescentPackedZip.bank_read _ m ((raw v).isLt.trans_le (peerSize j)) (ok.neighbor j)).trans (adj v j)

private theorem decodeAt (u:VN):(dir).decode (raw u)=some (id_ u):=by
  let id:=denseOrder B u
  have authentic:(dir).uid id=raw u := congrArg (raw) ((denseOrder B).symm_apply_apply u)
  have yes:∃h,(dir).uid h=raw u:=⟨id,authentic⟩
  rw [Directory.decode,dite_eq_left yes,(dir).uid.injective (yes.choose_spec.trans authentic.symm)]
  rfl

private theorem present_real (v:VN):
    present (dir).faces (id_ v)=((Z).emittedNear T v).map id_:=by
  have root:(id_ v).val<Fintype.card VN:=(B.next.vertex v).isLt
  have addr:(dir).uid ⟨(id_ v).val,root⟩=raw v:=by
    change raw ((denseOrder B).symm ((denseOrder B) v))=raw v
    rw [Equiv.symm_apply_apply]
  have faces (j:Fin 3):(dir).faces (id_ v) j=(found (raw v) j).bind (dir).decode:=by
    simp only [Directory.faces,dite_eq_left root,addr];rfl
  apply Finset.ext
  intro y
  constructor
  · intro measured
    obtain ⟨j,hit⟩ := (Finset.mem_filter.mp measured).2
    rw [faces] at hit
    cases step:found (raw v) j with
    | none=>simp [step] at hit
    | some other=>
      obtain ⟨t,ht,eq⟩:=realFace B wide found four selfFlag v step
      subst other
      have resolved : (dir).decode (raw t) = some y := by simpa only [step,Option.bind_some] using hit
      have decoded := decodeAt B wide newRoom found four selfFlag t
      exact Finset.mem_map.mpr ⟨t,ht,Option.some.inj (decoded.symm.trans resolved)⟩
  · intro measured
    obtain ⟨t,ht,rfl⟩ := Finset.mem_map.mp measured
    have see:raw t∈present found (raw v):=by
      rw [measured_neighbors found raw ((Z).emittedNear T) v (four v) (selfFlag v)]
      exact Finset.mem_map.mpr ⟨t,ht,rfl⟩
    obtain ⟨j,jt⟩:=(Finset.mem_filter.mp see).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,j,by rw [faces,jt];exact decodeAt B wide newRoom found four selfFlag t⟩

theorem reset_peer {p:ℕ}(record:B.Recorded p)(h:Fin R)(j:Fin 3):
    indexed (dir).faces h j=B.next.venueRoster newRoom h j:=by
  let number:=(id_).trans Fin.valEmbedding
  by_cases alive:∃v:VN,id_ v=h
  · obtain ⟨v,rfl⟩:=alive
    have seen:∃x:VN,id_ x=id_ v:=⟨v,rfl⟩
    have exactSet:=present_real B wide newRoom found four selfFlag v
    rw [←congrFun (rendered_near B record) v] at exactSet
    have rank (u:↥((A).near v)) :
        before (dir).faces (id_ v) (id_ u.val)=(hostSlot (A) number v u).val:=by
      rw [hostSlot_val,before,exactSet]
      have filt:((((A).near v).map id_).filter (·< id_ u.val))=
          (((A).near v).filter (fun y=>number y<number u.val)).map id_:=by
        ext y
        constructor
        · intro using_
          obtain ⟨entry,low⟩:=Finset.mem_filter.mp using_
          obtain ⟨t,ht,eq⟩:=Finset.mem_map.mp entry
          subst y
          exact Finset.mem_map.mpr ⟨t,Finset.mem_filter.mpr ⟨ht,low⟩,rfl⟩
        · intro actual
          obtain ⟨t,ht,rfl⟩:=Finset.mem_map.mp actual
          exact Finset.mem_filter.mpr ⟨Finset.mem_map.mpr ⟨t,(Finset.mem_filter.mp ht).1,rfl⟩,(Finset.mem_filter.mp ht).2⟩
      rw [filt,Finset.card_map]
    unfold Reached.venueRoster hostRotor
    rw [dite_eq_left seen,(id_).injective seen.choose_spec]
    change indexed (dir).faces (id_ v) j = (hostRoster (A) number v (Fin.cast B.next.branch.symm j)).map (id_)
    apply Option.ext
    intro y
    rw [indexed_iff]
    constructor
    · rintro ⟨mem,ordered⟩
      obtain ⟨t,ht,rfl⟩:=Finset.mem_map.mp (exactSet ▸ mem)
      let u:↥((A).near v):=⟨t,ht⟩
      have ix:hostSlot (A) number v u=Fin.cast B.next.branch.symm j:=Fin.ext ((rank u).symm.trans ordered)
      exact congrArg (Option.map (id_)) ((congrArg (hostRoster (A) number v) ix.symm).trans (DescentGroupPeerOrder.at_host (A) number v u))
    · intro actual
      cases row:hostRoster (A) number v (Fin.cast B.next.branch.symm j) with
      | none=>simp [row] at actual
      | some t=>
        have ey:id_ t=y:=Option.some.inj (by simpa only [row,Option.map_some] using actual)
        subst y
        have memt:= (DescentGroupPeerOrder.hostRoster_mem (A) number v t).mpr ⟨_,row⟩
        let u:↥((A).near v):=⟨t,memt⟩
        have ix:(hostSlot (A) number v u)=Fin.cast B.next.branch.symm j:=by
          unfold hostRoster at row
          split at row
          next active=>exact (show active.choose=u from Subtype.ext (Option.some.inj row)) ▸ active.choose_spec
          next=>contradiction
        exact ⟨exactSet.symm ▸ Finset.mem_map.mpr ⟨t,memt,rfl⟩,(rank u).trans (congrArg Fin.val ix)⟩
  · have missing:¬h.val<Fintype.card VN:=by
      intro t
      exact alive ⟨(denseOrder B).symm ⟨h.val,t⟩,Fin.ext (congrArg (fun x : Fin (Fintype.card VN) => x.val) ((denseOrder B).apply_symm_apply ⟨h.val,t⟩))⟩
    have no:present (dir).faces h=∅:=by
      ext u;simp [present,Directory.faces,missing]
    rw [B.next.venueRoster_missing newRoom h alive j]
    simp [indexed,no]

theorem reset_hub (h:Fin R) :
    ((dir).tagAt (publicTag ctl.board k height) h).toNat=(Census.hub (A) id_ h).val:=by
  by_cases hit:h.val<Fintype.card VN
  · let u:=(denseOrder B).symm ⟨h.val,hit⟩
    have address:id_ u=h:=Fin.ext (congrArg (fun x : Fin (Fintype.card VN) => x.val) ((denseOrder B).apply_symm_apply ⟨h.val,hit⟩))
    have current:(dir).uid ⟨h.val,hit⟩=raw u:=rfl
    rw [Directory.tagAt,dite_eq_left hit,current,←B.public_hub_rom,(Z).hubROM_at T sourceId u,←B.next_hub,←address]
    exact (DescentHubBits.live (A) id_ u).symm
  · rw [Directory.tagAt,dite_eq_right hit,DescentHubBits.absent (A) id_ h (by
      rintro ⟨u,e⟩
      exact hit ((congrArg Fin.val e) ▸ (B.next.vertex u).isLt))]
    rfl

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
