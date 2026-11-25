import OAI.Hierarchy.DescentMaterialProgram
import OAI.Hierarchy.DescentOrdinaryMaterialSocket

namespace OAI
/-! # Literal returned, routed and origin sockets of the public material plan -/
namespace Hierarchy.DescentDatedAddressBook.MaterialProgram
open DescentRawCablePanel DescentSIMDLookup DescentPackedColony DescentPackedZip
open DescentSharedCableNames DescentHaloPackedRebase DescentHaloWalkRAM ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open DepotRAM.Material.Route
open scoped Classical Fin.CommRing
noncomputable section
variable (v : MaterialProgram)
local notation "e" => v.extent
local notation "s" => v.depot
local notation "P₀" => breadth v.depot.degree
local notation "b" => v.extent.fieldBits
local notation "M" => v.extent.lanes
local notation "G₁" => v.extent.groups
local notation "B" => v.extent.blocks
local notation "H" => v.extent.oldHosts
local notation "RouteField" => DepotRAM.Material.Route.Port
variable (base : ℕ) (ranks : DescentOrdinaryDonorRankDirectory.Banks) (previous : Ports (breadth v.depot.degree))
def bankSocket (j : Fin (DepotRAM.Material.Sheets.count s)) (path : Fin P₀) (x : Fin B) (f : RouteField) : Expr :=
  let b₄:=(e).projectionStart base
  let src:=v.receivedBank base j
  let mapB:=bank (e).hosts G₁ M (Projection.mapBase b B M b₄)
  let mark:=stampBank (e).hosts G₁ M (Projection.markBase b B M (e).hosts G₁ b₄) f path
  projected ranks previous src mapB mark H G₁ M path (Projection.table b B M b₄ f x)

def materialSocket (path : Fin P₀) (seat : DepotRAM.Material.Seat s) (x : Fin B) (f : RouteField) : Expr :=
  v.bankSocket base ranks previous (DepotRAM.Material.Sheets.id s (donorField f) seat) path x f

def originSocket (seat : DepotRAM.Material.Seat s) (x : Fin B) (low : Bool) : Expr :=
  let f:Fin 9:=if low then 2 else 0
  let src:=v.receivedBank base (DepotRAM.Material.Sheets.id s f seat)
  .lookup (Projection.launchBank b B M ((e).projectionStart base) low x) (.lookup src .row)

end
end Hierarchy.DescentDatedAddressBook.MaterialProgram

end OAI
