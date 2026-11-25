import OAI.Hierarchy.DescentOrdinaryRegisteredRows

namespace OAI
/-! # Original signed, active, adjacency and role words supply each charged ordinary gather job -/
namespace Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary.ArgumentEntry
open DescentDatedPriorOperand DescentOperandStateBanks DescentPackedColony DescentPackedZip DescentSIMDLookup DescentRawCablePanel
open DescentOrdinaryAtomFieldRAM DescentOrdinaryAtomFieldRAM.ScalarOperand DescentOrdinaryReferenceInputs DescentSharedCableNames
open DescentScalarVenueMask
open DescentHaloWalkRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure ProtocolRAM
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable {F P : Type} [Field F] (v : PhysicalOrdinary F P) (A : ArgumentEntry v)

variable (S : A.InputShape v) (floor : ℕ) («matching» : A.Match v floor)
local notation "H₀" => A.clip.venue.hosts
local notation "G₀" => A.clip.venue.groups
local notation "M₀" => A.clip.working
local notation "L₀" => A.population v floor
local notation "P₀" => A.ports v floor
local notation "R₀" => A.directory v floor «matching»
local notation "C₀" => v.refChart floor

local notation "Nv" => v.reference.newNodes
local notation "names₀" => v.reference.nameBits
local notation "count₀" => v.reference.countBits
local notation "actors₀" => v.reference.actors
local notation "donors₀" => v.reference.donors
local notation "Old" => Pages A.previous.operands→Fin A.previous.blocks→Fin A.previous.hosts→Fin A.previous.groups→
      Cell (DescentOrdinaryPriorRetile.digits A.previous)
local notation "Parts" => Fin H₀→Fin G₀→DepotRAM.Parts A.clip.venue.socket
local notation "Roles" => Fin A.previous.blocks→Fin A.previous.hosts→Fin G₀→Cell ((L₀).roleBits*(L₀).nodes)
local notation "HostRoutes" => Fin H₀→Fin (L₀).walks→Option (Fin H₀)
local notation "HostFields" => Fin H₀→Fin G₀→Cell (names₀*actors₀)

local notation "ClipName" => Packed.bits A.clip.venue.names
local notation "width₀" => ClipName*A.clip.actorCount=names₀*actors₀
local notation "RealPeers" => Fin H₀→Fin A.clip.venue.socket.degree→Option (Fin H₀)
local notation "Active" => Fin H₀→Fin G₀→Cell (1*A.clip.venue.socket.blocks)

def venueWord (parts : Parts) (active : Active) (hubs : Fin H₀→Cell 1) (peer : RealPeers)
    (width : width₀) : HostFields :=
  rowsAt rfl rfl width (fun h g=>encode ClipName A.clip.actorCount («fields» (Gather.reaching peer)
    (A.clip.core.values parts active) (fun a _=>hubs a) A.clip.venue.k A.clip.venue.gain
    A.clip.venue.slots A.clip.venue.names h g))

theorem published_rows {w} (m : Memory w) (safe : A.Room v floor w) (space : v.vectorStart floor<2^w)
    (old : Pages A.previous.operands→Fin A.previous.blocks→Fin A.previous.hosts→Fin A.previous.groups→
      Cell (DescentOrdinaryPriorRetile.digits A.previous))
    (parts : Fin H₀→Fin G₀→DepotRAM.Parts A.clip.venue.socket)
    (roles : Fin A.previous.blocks→Fin A.previous.hosts→Fin G₀→Cell ((L₀).roleBits*(L₀).nodes))
    (oldPitch : 0<A.previous.lanes) (panelPitch : 0<A.clip.panelPitch) (rolePitch : 0<A.rolePitch)
    (lower : ∀x p,(previousBank A.previous A.previousBase x p).Fits w (v.signedEnd floor))
    (oldRows : ∀x p,Reads (previousBank A.previous A.previousBase x p) (old p x) A.previous.lanes m)
    (panel : Reads A.venue.panel (fun h g=>DepotRAM.combine A.clip.venue.socket (parts h g)) A.clip.panelPitch m)
    (roleLo : ∀x,(A.role x).base+(A.role x).size≤v.signedEnd floor) (roleRoom : ∀x,A.previous.hosts*chunks G₀ A.rolePitch≤(A.role x).size)
    (roleRows : ∀x,Reads (A.role x) (roles x) A.rolePitch m)
    (active : Active) (hubs : Fin H₀→Cell 1) (peer : RealPeers) (actors : 0<A.clip.actorPitch)
    (act : Reads A.venue.actors active A.clip.actorPitch m)
    (one : ∀h : Fin H₀,m (A.venue.hub.base+h.val)=((hubs h).val:Word w))
    (near : ∀h j,m (A.venue.adjacency.base+(h.val*A.clip.venue.socket.degree+j.val))=(number (peer h j):Word w))
    (width : width₀) (names : (L₀).nameBits=names₀) (ranks : (L₀).donors=donors₀)
    (p : Fin v.vector.pageCount) (q : Fin v.vector.lows) :
    Measured ((R₀).refs p q)
      (A.registeredValues v S floor «matching» old parts roles (Gather.reaching peer)
        (A.venueWord v parts active hubs peer width) names ranks p q)
      Nv v.reference.lanes (v.vectorStart floor) (A.mountedTape v floor m) :=by
  obtain ⟨read,mounted,access⟩:=A.clip.issued A.venue (v.signedEnd floor) m safe.venue panelPitch actors
    parts active hubs peer panel act one near
  exact A.all_registered_rows v S floor «matching» m safe space old parts roles oldPitch panelPitch rolePitch
    lower oldRows panel roleLo roleRoom roleRows _ _ names ranks (reads_at rfl rfl width rfl read) mounted access p q

end
end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary.ArgumentEntry

end OAI
