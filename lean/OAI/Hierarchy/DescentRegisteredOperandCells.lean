import OAI.Hierarchy.DescentOrdinaryPublishedRows

namespace OAI
/-! # The original registered geometry, prior role counts and operand words at a single native cell -/
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


/-- Decode the literal packed word after changing only its numeric shape proof. -/
private theorem uncast_digit {a b n m : ℕ} (bits : a=b) (arity : n=m) (width : a*n=b*m)
    (f : Fin n→Cell a) (j : Fin m) :
    (((encode b m).symm ((encode a n f).cast (congrArg (2^·) width))) j).val=
      (f (j.cast arity.symm)).val:=by
  subst b
  subst m
  simp

variable (old : Pages A.previous.operands→Fin A.previous.blocks→Fin A.previous.hosts→Fin A.previous.groups→
      Cell (DescentOrdinaryPriorRetile.digits A.previous))
    (parts : (Fin A.clip.venue.hosts→Fin A.clip.venue.groups→DepotRAM.Parts A.clip.venue.socket)) (roles : Fin A.previous.blocks→Fin A.previous.hosts→Fin A.clip.venue.groups→Cell ((A.population v floor).roleBits*(A.population v floor).nodes))
    (active : (Fin A.clip.venue.hosts→Fin A.clip.venue.groups→Cell (1*A.clip.venue.socket.blocks))) (hubs : Fin A.clip.venue.hosts→Cell 1) (peer : (Fin A.clip.venue.hosts→Fin A.clip.venue.socket.degree→Option (Fin A.clip.venue.hosts)))
    (width : (Packed.bits A.clip.venue.names * A.clip.actorCount = v.reference.nameBits * v.reference.actors)) (names : (A.population v floor).nameBits=v.reference.nameBits) (ranks : (A.population v floor).donors=v.reference.donors)
    (pg : Fin v.vector.pageCount) (l : Fin v.vector.lows)
local notation "chosenRows" => A.registeredValues v S floor «matching» old parts roles (Gather.reaching peer)
    (A.venueWord v parts active hubs peer width) names ranks pg l

/-- The genuine W-geometry on every physical host: its venue register decodes the actual
signed and active chip words; its count register decodes the complete predecessor role raster. -/
theorem published_geometry_cells (lengths : ClipName=names₀) (actors : A.clip.actorCount=actors₀)
    (h : Fin H₀) (g : Fin G₀) :
    (∀i : Fin actors₀,((chosenRows).venues h g i).val=
      («fields» (Gather.reaching peer) (A.clip.core.values parts active) (fun t _=>hubs t)
        A.clip.venue.k A.clip.venue.gain A.clip.venue.slots A.clip.venue.names h g (i.cast actors.symm)).val) ∧
    (∀j : Fin donors₀,((chosenRows).counts h g j).val=
      (RoleCounts.value (Gather.reaching peer) (A.roleValues v roles) count₀ h g (j.cast ranks.symm)).val) :=by
  constructor
  · intro i
    exact uncast_digit lengths actors width _ i
  · intro j
    exact uncast_digit rfl ranks (congrArg (count₀*·) ranks) _ j

/-- All four remaining fields are read at the very same native page. -/
theorem published_book_fields (h : Fin H₀) (g : Fin G₀) :
    (∀j,(chosenRows).walks h j=Gather.reaching peer h (j.cast «matching».paths.symm)) ∧
    (chosenRows).old=A.oldInput v S floor «matching» old pg ∧
    (chosenRows).born=A.bornInput v S floor «matching» parts pg ∧
    ((chosenRows).wanted h g).val=(Packed.token (some l)).val :=by
  exact ⟨fun _=>rfl,rfl,rfl,rfl⟩

end
end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary.ArgumentEntry

end OAI
