import OAI.Hierarchy.DescentOrdinaryVenueClipRun

namespace OAI
/-! # The common earlier program reads the actual matched donor register and every venue ticket -/
namespace Hierarchy.DescentScalarVenueMask.Stage
open DescentSIMDLookup DescentPacking.PackedMatch.Local DescentPacking.PackedMatch.Local.Stage DescentSixParty DescentStageEdgeReceipt
open DescentGroupPeerOrder DescentSharedCableNames DescentPackedColony DescentHaloWalkRAM DescentRawCablePanel DescentPackedZip
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM DescentOrdinaryVenueIngress
open scoped Classical Fin.CommRing
set_option quotPrecheck false
noncomputable section
variable {F P V J : Type} [Field F] [Fintype V] [DecidableEq V] [Fintype J] [DecidableEq J]
    {d k i short a H Z M w : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits} {G : PoweredGadget F} {price ε : ℝ}
variable (A : GroupStage W G price ε J V k) (native : W.graph.Edge↪ℕ) (S : DescentCompiler.AtomSchedule)
    (ready : A.StateBounds S i) (group : J≃Fin Z) (hosts : V↪Fin H) (win : J×V→Fin (2^k)→Cell a)
    (hm : 0<M) (profile dest : ℕ) (m : Memory w) (hub : V→Bool) (lay : Bool) (bytes slots : ℕ)
local notation "grp" => group.toEmbedding
local notation "rank" => groupRank ((grp).trans Fin.valEmbedding) (hosts.trans Fin.valEmbedding)
local notation "near" => hostRotor hosts (hostRoster A (hosts.trans Fin.valEmbedding))
local notation "fmt" => shapeOf (short:=short) A bytes
local notation "state" => nativeParts (short:=short) A native S ready rank win group hosts hm profile dest m near hub lay bytes
local notation "t" => tokens (short:=short) A native S ready rank win profile lay grp hosts

def ingressChart (payload panelPitch actorPitch wider gain names : ℕ) : Clip :=
  ⟨⟨fmt,H,Z,0,k,profile,gain,slots,names⟩,payload,panelPitch,actorPitch,wider⟩

variable (payload actorPitch wider gain names base : ℕ) (B : Inputs)
local notation "c₀" => ingressChart (short:=short) (H:=H) (Z:=Z) A profile bytes slots payload M actorPitch wider gain names

theorem matched_ingress (before : Memory w) (room : (c₀).Room B base w) (activePitch : 0<actorPitch)
    (raw : Reads B.panel (fun h g=>DepotRAM.combine fmt (state h g)) M before)
    (active : Reads B.actors (Prepare.actors A grp hosts) actorPitch before)
    (hs : ∀h : Fin H,before (B.hub.base+h.val)=((Census.hub A hosts h).val:Word w))
    (roster : ∀h j,before (B.adjacency.base+(h.val*A.degree+j.val))=(number (near h j):Word w)) :
    let out:=((c₀).phase B base w).image before
    let walks:=Gather.reaching near;let K:=DescentPackedActorMask.actors ((breadth A.degree)*2^k) A.cap
    Reads ((c₀).fieldBank base) (fun h g=>encode (Packed.bits names) K
      («fields» walks (t slots) (fun h _=>Census.hub A hosts h) k gain slots names h g)) (c₀).working out ∧
    Mounted ((c₀).ports base) (DescentSortedRoster.indexed walks) out Z (c₀).working ∧
    ∀src : Bank,src.Fits w ((c₀).fullEnd base)→(c₀).core.rows ≤ src.size→Accessible ((c₀).ports base) src H Z (c₀).working w ((c₀).fullEnd base):=by
  intro out walks K
  have read:=(c₀).issued B base before room hm activePitch state (Prepare.actors A grp hosts) (Census.hub A hosts) near raw active hs roster
  have authentic : (c₀).core.values state (Prepare.actors A grp hosts)=t slots:=by
    funext x j h g
    exact retained_actor (short:=short) A native S ready group hosts win hm profile dest m hub lay bytes slots x j h g
  refine ⟨?_,read.2⟩
  have values := read.1
  rw [← authentic]
  exact values

end
end Hierarchy.DescentScalarVenueMask.Stage

end OAI
