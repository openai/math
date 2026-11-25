import OAI.Hierarchy.DescentOrdinaryVenueIngress

namespace OAI
/-! # Physical donor and all six matched ticket rows read at the ordinary entrance -/
namespace Hierarchy.DescentOrdinaryVenueIngress.Chart
open DescentSIMDLookup DescentPackedZip DescentRawCablePanel DescentPackedColony DescentHaloWalkRAM DescentScalarVenueMask
open DescentSixParty.Chronology DescentPaidResidentCount ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
set_option quotPrecheck false
noncomputable section
variable (v : Chart) (B : Inputs) (base : ℕ) {w : ℕ}
local notation "H₀" => v.hosts
local notation "G₀" => v.groups
local notation "M₀" => v.lanes
local notation "D₀" => v.socket.degree
local notation "α₀" => v.actorBase base
local notation "β₀" => v.haloBase base
local notation "γ₀" => v.rasterBase base
local notation "rs₀" => v.shape base

private theorem preserve {H G M b w base : ℕ} {input output : Memory w} {reg : Bank}
    {val : Fin H→Fin G→Cell b} (prev : Reads reg val M input) (stop : reg.base+reg.size≤base)
    (size : H*chunks G M≤reg.size) (same : ∀i,i<base→ output i=input i) : Reads reg val M output :=by
  intro p; exact (same _ ((Nat.add_lt_add_left ((row H G M p).isLt.trans_le size) _).trans_le stop)).trans (prev p)

def values (parts : Fin H₀→Fin G₀→DepotRAM.Parts v.socket) (active : Fin H₀→Fin G₀→Cell (1*v.socket.blocks))
    (x : Fin v.socket.blocks) (j : Fin (1+v.socket.cap*6)) (h : Fin H₀) (g : Fin G₀) :=
  DepotRAM.ActorInputs.token v.socket v.profile v.slots v.raw (parts h g) (active h g) (x,j)

set_option maxHeartbeats 1000000 in
theorem issued (m : Memory w) (s : v.Room B base w)
    (parts : Fin H₀→Fin G₀→DepotRAM.Parts v.socket) (active : Fin H₀→Fin G₀→Cell (1*v.socket.blocks))
    (hubs : Fin H₀→Cell 1) (peer : Fin H₀→Fin D₀→Option (Fin H₀))
    (panel : Reads B.panel (fun h g=>DepotRAM.combine v.socket (parts h g)) M₀ m)
    (act : Reads B.actors active M₀ m) (one : ∀h : Fin H₀,m (B.hub.base+h.val)=((hubs h).val:Computability.VPVNP.BurstRAM.Word w))
    (near : ∀h j,m (B.adjacency.base+(h.val*D₀+j.val))=(number (peer h j):Computability.VPVNP.BurstRAM.Word w)) :
    let out:=(v.phase B base w).image m
    Reads (v.fieldBank base) (fun h g=>encode (DescentSharedCableNames.Packed.bits v.names) (DescentPackedActorMask.actors (v.paths*v.socket.blocks) v.socket.cap)
      (DescentScalarVenueMask.fields (Gather.reaching peer) (v.values parts active) (fun a _=>hubs a) v.k v.gain v.slots v.names h g)) M₀ out ∧
    Mounted (rs₀).ports (DescentSortedRoster.indexed (Gather.reaching peer)) out G₀ M₀ ∧
    (∀src : Bank,src.Fits w (v.endAddress base)→v.rows ≤ src.size→Accessible (rs₀).ports src H₀ G₀ M₀ w (v.endAddress base)) :=by
  intro out
  obtain ⟨ba,ab,bc,cd,de⟩:=v.ceilings base
  have co:=cd.trans ((Nat.le_add_right ..).trans de);have high:=co.trans_lt s.space
  let hb:=(v.hubPhase B base w).image m
  let ticket:=(v.pairedPhase B base w).image hb
  let roots:=(v.haloPhase B base w).image ticket
  have hs:α₀<2^w:=ab.trans_lt (bc.trans_lt high)
  have fh:= (HubRepeat.any base H₀ G₀ M₀ B.hub m (s.prior _ (by simp)) hs).2.1
  have panelH : Reads B.panel _ M₀ hb:=preserve panel (s.prior _ (by simp)).2.2 s.panelRows (fun j lo=>fh j (.inl lo))
  have activeH : Reads B.actors _ M₀ hb:=preserve act (s.prior _ (by simp)).2.2 s.actorRows (fun j lo=>fh j (.inl lo))
  have actorRoom:=v.actorsRoom B base s
  have fp:=(DepotRAM.ActorInputs.all_runs v.socket v.profile v.slots v.raw α₀ B.panel B.actors hb actorRoom).2
  have cols:=DepotRAM.ActorInputs.columns v.socket v.profile v.slots v.raw α₀ B.panel B.actors hb actorRoom parts active panelH activeH
  have adj:=s.prior B.adjacency (by simp)
  have ok:B.adjacency.Fits w β₀:=⟨adj.1,adj.2.1,adj.2.2.trans (ba.trans ab)⟩
  have edges (h : Fin H₀) (j : Fin D₀) : ticket (B.adjacency.base+(h.val*D₀+j.val))=(number (peer h j):Computability.VPVNP.BurstRAM.Word w):=by
    have inner : h.val*D₀+j.val<H₀*D₀:=(Nat.add_lt_add_left j.isLt _).trans_le (by rw [←Nat.succ_mul];exact Nat.mul_le_mul_right _ h.isLt)
    have prior: B.adjacency.base+(h.val*D₀+j.val)<base:=(Nat.add_lt_add_left (inner.trans_le s.adjacent) _).trans_le adj.2.2
    exact (fp _ (.inl (prior.trans_le ba))).trans ((fh _ (.inl prior)).trans (near h j))
  obtain ⟨_,mounted,ends,access,endFit,endSize,fr,_⟩:=DescentScalarHaloProgram.run H₀ G₀ M₀ D₀ B.adjacency β₀ peer ticket ok s.adjacent edges s.smallH s.smallD s.smallPaths high
  have geom:=v.rasterRoom B base s access endFit endSize
  have hword : Reads (v.packedHub base) (fun h _=>hubs h) M₀ hb:=HubRepeat.issued base H₀ G₀ M₀ B.hub m (s.prior _ (by simp)) s.hubRows hubs one hs
  have roomH:(v.packedHub base).base+(v.packedHub base).size≤α₀:=by dsimp [packedHub,actorBase,Bank.size];omega
  have packed : Reads (v.packedHub base) _ M₀ roots:=preserve (preserve hword roomH v.rowRoom (fun j lo=>fp j (.inl lo))) (roomH.trans ab) v.rowRoom (fun j lo=>fr j (.inl lo))
  have actual : Receiver.Raw (rs₀).ports (rs₀).route (rs₀).key (rs₀).hub (rs₀).ends γ₀ (Gather.reaching peer) (v.values parts active) (fun h _=>hubs h) M₀ roots:=
    ⟨mounted,geom.shape,endFit,endSize,ends,geom.routeFit,geom.routeRoom,
      fun x j=>preserve (cols (x,j)).1 (v.ticketRooms base (x,j)).1 (v.ticketRooms base (x,j)).2.2.1 (fun i lo=>fr i (.inl lo)),
      geom.keyFit,geom.keyRoom,fun x j=>preserve (cols (x,j)).2 (v.ticketRooms base (x,j)).2.1 (v.ticketRooms base (x,j)).2.2.2 (fun i lo=>fr i (.inl lo)),packed⟩
  obtain ⟨_,printed,kept,_⟩:=Raster.run rs₀ v.k v.gain v.slots v.raw v.names H₀ G₀ M₀ γ₀ (Gather.reaching peer) (v.values parts active) (fun h _=>hubs h) roots actual (de.trans_lt s.space)
  have past {b : Bank} (fit : b.Fits w γ₀) {i : ℕ} (lim : i<b.size) : out (b.base+i)=roots (b.base+i):=kept _ (.inl ((Nat.add_lt_add_left lim _).trans_le fit.2.2))
  have grow (bank : Bank) (fit : bank.Fits w γ₀) : bank.Fits w (v.endAddress base):=⟨fit.1,fit.2.1,fit.2.2.trans co⟩
  refine ⟨printed,⟨fun p j=>(past (geom.shape.ids j) ((row H₀ G₀ M₀ p).isLt.trans_le (geom.shape.idsRoom j))).trans (mounted.ids p j),?_,
    fun h=>(past geom.shape.offsets (h.isLt.trans_le geom.shape.offRoom)).trans (mounted.offsets h),
    fun p=>(past geom.shape.chunks ((row H₀ G₀ M₀ p).isLt.trans_le geom.shape.chunkRoom)).trans (mounted.chunks p)⟩,?_⟩
  · intro h p;have index : h.val*v.paths+p.val<H₀*v.paths:=(Nat.add_lt_add_left p.isLt _).trans_le (by rw [←Nat.succ_mul];exact Nat.mul_le_mul_right _ h.isLt)
    exact (past geom.shape.roster (index.trans_le geom.shape.rosterRoom)).trans (mounted.roster h p)
  · intro src bound lim;exact ⟨fun q=>grow _ (geom.shape.ids q),geom.shape.idsRoom,grow _ geom.shape.roster,geom.shape.rosterRoom,
      grow _ geom.shape.offsets,geom.shape.offRoom,grow _ geom.shape.chunks,geom.shape.chunkRoom,bound,lim⟩

end
end Hierarchy.DescentOrdinaryVenueIngress.Chart

end OAI
