import OAI.Hierarchy.DescentDatedPrimitiveReturned
import OAI.Hierarchy.DescentDatedRegisterState
import OAI.Hierarchy.DescentDatedPrimitiveRead

namespace OAI
/-! The ordinary register hands its actual primitive pages on to the next date, after the counter write. -/
namespace Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary
open DescentOrdinaryPrimitiveCheckpoint DescentPackedColony DescentSIMDLookup DescentPackedZip DescentDatedAddressBook
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
set_option hygiene false
variable {F P : Type} [Field F] (v : PhysicalOrdinary F P) (floor : ℕ)
  (A : ArgumentEntry v) (chartMatch : A.Match v floor) (radix : v.vector.radix=2^v.reference.k)
local notation "L" => v.paletteShape
local notation "src" => v.primitiveSources floor A chartMatch radix
local notation "oldEnd" => v.operandEnd floor
local notation "base" => v.primitiveFirst oldEnd
local notation "G" => v.gadget
local notation "s" => v.palette.seedWidth
local notation "Z" => v.palette.grainLimit
local notation "op" => v.palette.rotor

variable {w : ℕ}

theorem registered_role_bank (fit : v.PrimitiveRoom floor A w) (size : (L).Capacity src)
    (past : Fin (L).blocks→Fin (L).hosts→Fin (L).oldGroups→Cell ((L).primitiveBits*(L).oldNodes))
    (chip : Fin v.bornBook.hosts→Fin v.bornBook.groups→Cell v.bornBook.chipBits)
    (hosts : (L).hosts=v.bornBook.hosts) (groups : (L).oldGroups=v.bornBook.groups)
    (origin : Fin (L).blocks→Fin (L).successors→Fin (L).groups→Cell ((L).originBits*(L).newNodes))
    (next : Fin (L).hosts→Fin (L).ports→Option (Fin (L).hosts)) (m : Memory w)
    (previous : ∀x,Reads ((src).previous x) (past x) (L).priorLanes m)
    (mass : v.bornBook.rows≤(A.chipBank v floor).size)
    (donor : Reads (A.chipBank v floor) chip v.bornBook.lanes m)
    (ranks : ∀x,Reads ((src).origin x) (origin x) (L).originLanes m)
    (ports : ∀(h : Fin (L).hosts) (i : Fin (L).ports),m ((src).halo.base+(h.val*(L).ports+i.val))=(DescentPackedColony.target (next h i):Word w))
    (top : (v.area.matcher v.old floor).layout.topology.Fits w (v.primitiveEnd floor))
    (room : v.returnedEnd floor<2^w) (x : Fin (L).blocks) :
    let state:=v.paletteStock floor A chartMatch past chip hosts groups origin next
    let post:=(v.primitiveUpdate floor A chartMatch radix w).image m
    Reads ((DatePorts.ordinary v floor).archive.roles.bank x.val) (state.output x) (DatePorts.ordinary v floor).roleLanes
      ((v.counter floor w).image post):=by
  intro state post
  have init:=v.primitive_read floor A chartMatch radix fit size past chip hosts groups origin next m
    previous mass donor ranks ports x
  change Reads ((PriorRolePages.ordinary v floor).bank x.val) _ _ _
  rw [(PriorRolePages.ordinary_pages v floor).2 x]
  exact v.primitive_return floor post x _ top room fit.space init

end
end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary

end OAI
