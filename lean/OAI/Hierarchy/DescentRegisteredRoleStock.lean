import OAI.Hierarchy.DescentOrdinaryRegisteredRoleBank
import OAI.Hierarchy.DescentArchivePaddedNodes

namespace OAI
/-! Publish the physical primitive archive and carry it across the measured ordinary book chart. -/
namespace Hierarchy.DescentOrdinaryPrimitiveCheckpoint.Layout
open ProtocolRAM DescentPackedColony Computability.VPVNP.BurstRAM DescentSIMDLookup
noncomputable section
variable {w : ℕ}
/-- The numeric role bank belonging to every block on this original RAM state. -/
def Published (L : Layout) (stock : L.Stock) (bank : ℕ→Bank) (m : Memory w) : Prop :=
  ∀x : Fin L.blocks,Reads (bank x.val) (stock.output x) L.nextLanes m

theorem Published.chart {L T : Layout} (same : L=T) (stock : L.Stock) {bank : ℕ→Bank} {m : Memory w}
    (read : L.Published stock bank m) : T.Published (same ▸ stock) bank m:=by
  subst T;exact read

end
end Hierarchy.DescentOrdinaryPrimitiveCheckpoint.Layout

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

theorem registered_role_stock (fit : v.PrimitiveRoom floor A w) (size : (L).Capacity src)
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
    (room : v.returnedEnd floor<2^w) :
    let state:=v.paletteStock floor A chartMatch past chip hosts groups origin next
    let post:=(v.primitiveUpdate floor A chartMatch radix w).image m
    (L).Published state ((DatePorts.ordinary v floor).archive.roles.bank) ((v.counter floor w).image post):=by
  intro state post x
  exact v.registered_role_bank floor A chartMatch radix fit size past chip hosts groups origin next m previous mass
    donor ranks ports top room x

end
end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary

namespace Hierarchy.DescentSixParty.Chronology.DatePorts
open DescentColonies DescentKernelHistory DescentLocalArchiveOrder DescentPrimitivePalette DescentSIMDLookup DescentPackedColony
open ProtocolRAM Computability.VPVNP.BurstRAM
noncomputable section
private theorem cast_groups {H G G' b M w : ℕ} (same : G=G') (bank : Bank) (value : Fin H→Fin G→Cell b)
    (m : Memory w) (read : Reads bank value M m) :
    Reads bank (fun h g=>value h (g.cast same.symm)) M m:=by
  subst G';exact read

set_option maxHeartbeats 480000 in
/-- Normalize only the packed axes of the reached cut. The block ordinal is
unchanged by this index transport. -/
theorem primitive_of_cells {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
    {G : PoweredGadget F} {q ε : ℝ} {S : DescentCompiler.AtomSchedule} {k age grain degree wire hist w H N M s Z : ℕ}
    (ports : DatePorts) (r : Reached W G q ε S k age grain degree wire hist) (B : BitDescription W) (ord : Local B)
    (room : RangeRoom ports r B) (op : RotorSpec) (label : NodeOrder.All B→Label G s Z op) (m : Memory w)
    (hosts : H=ports.operandHosts) (nodes : N=ports.nodes) (lanes : M=ports.roleLanes)
    (present : ∀x : Block k,Reads (ports.archive.roles.bank x.val)
      (fun (h : Fin H) (g : Fin (S.groupCount age))=>encode (printedBits G s Z op) N
        (fun j=>(Reached.NodeCells.atPhysical r B ord x j h g).elim 0 (fun y=>token G s Z op (label y)))) M m) :
    ∀x : Fin (2^ports.venue.k),Reads (ports.archive.roles.bank x.val)
      (fun (h : Fin ports.operandHosts) (g : Fin ports.venue.groups)=>encode (printedBits G s Z op) ports.nodes
        (fun j=>(slotAt ports r B ord room x j h g).elim 0 (fun y=>token G s Z op (label y)))) ports.roleLanes m:=by
  subst H;subst N;subst M
  intro x
  let actual : Block k:=x.cast (congrArg (2^·) room.radix.symm)
  unfold slotAt
  exact cast_groups room.groups (ports.archive.roles.bank x.val)
    (fun h g=>encode (printedBits G s Z op) ports.nodes
      (fun j=>(Reached.NodeCells.atPhysical r B ord actual j h g).elim 0 (fun y=>token G s Z op (label y)))) m
    (present actual)

end
end Hierarchy.DescentSixParty.Chronology.DatePorts

end OAI
