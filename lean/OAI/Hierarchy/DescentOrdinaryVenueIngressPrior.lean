import OAI.Hierarchy.DescentOrdinaryVenueIngressStage
import OAI.Hierarchy.DescentStageVenuePeers

namespace OAI
/-! # Original pointer banks and matched state at the first ordinary argument scan -/
namespace Hierarchy.DescentSixParty
open DescentSIMDLookup DescentPacking.PackedMatch.Local DescentPacking.PackedMatch.Local.Stage DescentStageEdgeReceipt
open DescentGroupPeerOrder DescentSharedCableNames DescentPackedColony DescentHaloWalkRAM DescentRawCablePanel DescentPackedZip
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM DescentOrdinaryVenueIngress DescentScalarVenueMask DescentScalarVenueMask.Stage
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable {F P : Type} [Field F] {d k age z D wire hist H w short a M : ℕ} {bits : P→ℕ}
    {W : MarkedWorld F d P bits} {G : PoweredGadget F} {q ε : ℝ} {S : DescentCompiler.AtomSchedule}
    (r : Reached W G q ε S k age z D wire hist) (wide : Fintype.card r.V≤H)
    (i : Dated.Operands) (actorPitch countBits floor : ℕ)
local notation "hs" => r.vertex.trans (Fin.castLEEmb wide)
local notation "G₀" => S.groupCount age
local notation "A₀" => r.placement
local notation "near" => hostRotor hs (hostRoster A₀ ((hs).trans Fin.valEmbedding))

def ingressInputs (i : Dated.Operands) (donor : Bank) : Inputs := ⟨donor,i.actors,i.hubs,i.roster⟩

theorem ingress_prior (old now : Memory w) (prior : stageVenue r wide i actorPitch countBits floor (r.venueRoster wide) old)
    (held : ∀a<floor,now a=old a) :
    Reads i.actors (Prepare.actors A₀ (Function.Embedding.refl _) hs) actorPitch now ∧
    (∀h,now (i.hubs.base+h.val)=((Census.hub A₀ hs h).val:Word w)) ∧
    (∀(h : Fin H) (j : Fin (A₀).degree),now (i.roster.base+(h.val*(A₀).degree+j.val))=(number (near h j):Word w)):=by
  have keepRoster:=r.roster_read wide i prior
  obtain ⟨ca,_,active,_,hubFit,hubCount,hub,_,_⟩:=prior
  refine ⟨?_,?_,?_⟩
  · intro t;exact (held _ ((Nat.add_lt_add_left ((row H G₀ actorPitch t).isLt.trans_le ca.srcRoom) _).trans_le ca.source.2.2)).trans (active t)
  · intro h;exact (held _ ((Nat.add_lt_add_left (h.isLt.trans_le hubCount) _).trans_le hubFit.2.2)).trans (hub h)
  · intro h j
    let index:=Fin.cast r.branch j
    have inside : h.val*D+index.val<H*D:=(Nat.add_lt_add_left index.isLt _).trans_le (by rw [←Nat.succ_mul];exact Nat.mul_le_mul_right D h.isLt)
    have bound : i.roster.base+(h.val*(A₀).degree+j.val)<floor:=by
      simpa only [index,Fin.val_cast,r.branch] using ((Nat.add_lt_add_left (inside.trans_le ca.rosterRoom) i.roster.base).trans_le ca.roster.2.2)
    have orderEq : (hs).trans Fin.valEmbedding = r.vertex.trans Fin.valEmbedding := by
      ext v
      rfl
    exact (held _ bound).trans (by simpa only [orderEq, number, Nat.add_assoc] using keepRoster h j)

variable (win : (Fin (S.groupCount age)×r.V)→Fin (2^k)→Cell a) (hm : 0<M) (profile dest : ℕ)
    (stateMem : Memory w) (hub : r.V→Bool) (lay : Bool) (bytes slots extra gain names payload base : ℕ) (donor : Bank)
local notation "rank" => groupRank Fin.valEmbedding ((hs).trans Fin.valEmbedding)
local notation "order" => r.order.trans Fin.valEmbedding
local notation "fmt" => shapeOf (short:=short) A₀ bytes
local notation "state" => nativeParts (short:=short) A₀ order S r.valid rank win (Equiv.refl _) hs hm profile dest stateMem near hub lay bytes
local notation "tok" => tokens (short:=short) A₀ order S r.valid rank win profile lay (Function.Embedding.refl _) hs slots
local notation "c₀" => ingressChart (short:=short) (H:=H) (Z:=G₀) A₀ profile bytes slots payload M actorPitch extra gain names
local notation "B₀" => ingressInputs i donor

theorem ingress_from_donor (old now : Memory w) (prior : stageVenue r wide i actorPitch countBits floor (r.venueRoster wide) old)
    (held : ∀a<floor,now a=old a) (current : Reads donor (fun h g=>DepotRAM.combine fmt (state h g)) M now)
    (actorPos : 0<actorPitch) (room : (c₀).Room B₀ base w) :
    let out:=((c₀).phase B₀ base w).image now
    let walk:=Gather.reaching near
    Reads ((c₀).fieldBank base) (fun h g=>encode (Packed.bits names) (c₀).actorCount
      («fields» walk tok (fun h _=>Census.hub A₀ hs h) k gain slots names h g)) (c₀).working out ∧
    Mounted ((c₀).ports base) (DescentSortedRoster.indexed walk) out G₀ (c₀).working ∧
    ∀src : Bank,src.Fits w ((c₀).fullEnd base)→(c₀).core.rows ≤ src.size→Accessible ((c₀).ports base) src H G₀ (c₀).working w ((c₀).fullEnd base):=by
  obtain ⟨act,one,peers⟩:=ingress_prior r wide i actorPitch countBits floor old now prior held
  exact matched_ingress (short:=short) A₀ order S r.valid (Equiv.refl _) hs win hm profile dest stateMem hub lay bytes slots
    payload actorPitch extra gain names base B₀ now room actorPos current act one peers

end
end Hierarchy.DescentSixParty

end OAI
