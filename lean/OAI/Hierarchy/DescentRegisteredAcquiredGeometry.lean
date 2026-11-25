import OAI.Hierarchy.DescentRegisteredOperandCells
import OAI.Hierarchy.DescentRegisteredOperandReshape
import OAI.Hierarchy.DescentOrdinaryRangeAcquisition

namespace OAI
/-! Direct expansion of all six W input columns from one measured actor/cable, roster and prior role array. -/
namespace Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary.ArgumentEntry
open DescentDatedPriorOperand DescentOperandStateBanks DescentPackedColony DescentPackedZip DescentSIMDLookup DescentRawCablePanel
open DescentOrdinaryAtomFieldRAM DescentOrdinaryAtomFieldRAM.ScalarOperand DescentOrdinaryReferenceInputs DescentSharedCableNames
open DescentScalarVenueMask DescentDatedPriorOperand.OrdinaryBooks
open DescentHaloWalkRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure ProtocolRAM
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
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


variable (old : Pages A.previous.operands→Fin A.previous.blocks→Fin A.previous.hosts→Fin A.previous.groups→
      Cell (DescentOrdinaryPriorRetile.digits A.previous))
    (parts : (Fin A.clip.venue.hosts→Fin A.clip.venue.groups→DepotRAM.Parts A.clip.venue.socket)) (roles : Fin A.previous.blocks→Fin A.previous.hosts→Fin A.clip.venue.groups→Cell ((A.population v floor).roleBits*(A.population v floor).nodes))
    (active : (Fin A.clip.venue.hosts→Fin A.clip.venue.groups→Cell (1*A.clip.venue.socket.blocks))) (hubs : Fin A.clip.venue.hosts→Cell 1) (peer : (Fin A.clip.venue.hosts→Fin A.clip.venue.socket.degree→Option (Fin A.clip.venue.hosts)))
    (width : (Packed.bits A.clip.venue.names * A.clip.actorCount = v.reference.nameBits * v.reference.actors)) (names : (A.population v floor).nameBits=v.reference.nameBits) (ranks : (A.population v floor).donors=v.reference.donors)
    (pg : Fin v.vector.pageCount) (l : Fin v.vector.lows)
local notation "chosenRows" => A.registeredValues v S floor «matching» old parts roles (Gather.reaching peer)
    (A.venueWord v parts active hubs peer width) names ranks pg l


/-- This representation uses the actual previous-group numbering, before the successor block split. -/
def acquiredRegister (lengths : ClipName=names₀) (actors : A.clip.actorCount=actors₀) :
    Values v.reference.degree v.reference.k v.reference.oldNodes v.reference.capacity H₀ G₀
      v.reference.bits names₀ count₀ where
  walks h j:=Gather.reaching peer h (j.cast «matching».paths.symm)
  old:=A.oldInput v S floor «matching» old pg
  born:=A.bornInput v S floor «matching» parts pg
  wanted _ _:=((Packed.token (some l)).val:Cell names₀)
  venues h g i:=(«fields» (Gather.reaching peer) (A.clip.core.values parts active) (fun t _=>hubs t)
    A.clip.venue.k A.clip.venue.gain A.clip.venue.slots A.clip.venue.names h g (i.cast actors.symm)).cast
      (congrArg (2^·) lengths)
  counts h g j:=RoleCounts.value (Gather.reaching peer) (A.roleValues v roles) count₀ h g (j.cast ranks.symm)

theorem registered_acquired_geometry (lengths : ClipName=names₀) (actors : A.clip.actorCount=actors₀) :
    chosenRows=A.acquiredRegister v S floor «matching» old parts roles active hubs peer ranks pg l lengths actors:=by
  let native_:=A.acquiredRegister v S floor «matching» old parts roles active hubs peer ranks pg l lengths actors
  have own : (chosenRows).wanted=native_.wanted:=by
    funext h g
    apply Fin.ext
    have held:=A.published_book_fields v S floor «matching» old parts roles active hubs peer width names ranks pg l h g
    have small : (Packed.token (some l)).val<2^names₀ :=by
      apply lt_of_eq_of_lt held.2.2.2.symm
      exact ((chosenRows).wanted h g).isLt
    exact held.2.2.2.trans (Fin.val_cast_of_lt small).symm
  have vrows : (chosenRows).venues=native_.venues:=by
    funext h g i
    apply Fin.ext
    exact (A.published_geometry_cells v S floor «matching» old parts roles active hubs peer width names ranks pg l
      lengths actors h g).1 i
  have tally : (chosenRows).counts=native_.counts:=by
    funext h g i
    apply Fin.ext
    exact (A.published_geometry_cells v S floor «matching» old parts roles active hubs peer width names ranks pg l
      lengths actors h g).2 i
  calc
    chosenRows={native_ with wanted:=(chosenRows).wanted,venues:=(chosenRows).venues,counts:=(chosenRows).counts}:=rfl
    _=native_:=by rw [own,vrows,tally]

end
end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary.ArgumentEntry

end OAI
