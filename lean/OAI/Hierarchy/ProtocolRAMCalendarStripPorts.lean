import OAI.Hierarchy.ProtocolRAMCalendarStripPortBanks
import OAI.Hierarchy.ProtocolRAMCalendarStripChart
import OAI.Hierarchy.ProtocolRAMStripNativeIDs
import OAI.Hierarchy.ProtocolRAMCataloguePaidSupport

namespace OAI
/-! # Installing physical core and acquired edge addresses and the second catalyst radius -/

noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.StripChart
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage CoreBoard BoughtSockets
open StripDirectory PortPadding CatalogueRows
open scoped Classical
variable {z W k q depth w : ℕ}
local notation "N" => Stages z (2^W)
local notation "P" => Fintype.card (PayloadRole N k)
local notation "R" => Fintype.card (PurchasedRole depth k)
local notation "D" => max P R

variable (s : Boards z (2^W) k q depth) (c : Mesh) (b : CatalogueRows.Board)
  (G : PortBanks ((c.inject+c.cool)*c.outerFuel))

/-- Non-catalyst and padding roles carry no second-edge width. -/
def catalystFlag : Attempt → Fin D → Expr
  | .outer .. => extend (fun i : Fin P =>
      .lit (catalystBit ((Fintype.equivFin (PayloadRole N k)).symm i))) (.lit 0)
  | .inner .. => extend (fun i : Fin R =>
      .lit (catalystBit ((Fintype.equivFin (PurchasedRole depth k)).symm i))) (.lit 0)

def radiusMate : Attempt → Fin D → Expr
  | .outer .. => extend (fun i : Fin P =>
      (payloadPortsAt s c G).mate b ((Fintype.equivFin (PayloadRole N k)).symm i)) (.lit b.rows)
  | .inner p a _ _ => extend (fun i : Fin R =>
      (boughtPortsAt s c b G p a).mate b ((Fintype.equivFin (PurchasedRole depth k)).symm i)) (.lit b.rows)

variable (F : Type*) [Field F] [SiteNaming (ColumnSite (PayloadStrip.Columns (Stages z (2^W))) k)]
  [SiteNaming (ColumnSite (ChainStrip.Columns depth) k)]

/-- The doubled catalyst is charged on its two actual center-to-sign core
edges. The second scan uses the live debited role ordinal and its decoded
ball, while the original direct scan already emitted the first radius. -/
def forest (old : Traversals) (a : Attempt) : Traversals :=
  let H := header F (withPorts s c b G) a
  let mask := chooseField D 0 (catalystFlag (z:=z) (W:=W) (k:=k) (depth:=depth) a) H.fieldTerm
  let mate := chooseField D 0 (fun i => ((radiusMate s c b G a i).atRow H.ballTerm)) H.fieldTerm
  b.guardWalk {old with catalystMate:=some (mask,mate)}

theorem forest_mask (old : Traversals) (a : Attempt) :
    let H := header F (withPorts s c b G) a
    let mask := chooseField D 0 (catalystFlag (z:=z) (W:=W) (k:=k) (depth:=depth) a) H.fieldTerm
    let mate := chooseField D 0 (fun i=>((radiusMate s c b G a i).atRow H.ballTerm)) H.fieldTerm
    (forest s c b G F old a).catalystMate=some (mask,b.checkedEdge mate) := rfl

theorem mask_at_role (a : Attempt) (m : Memory w) (occ : Word w) (i : Fin D)
    (fit : D≤2^w) (hit : ((header F (withPorts s c b G) a).fieldTerm.eval m occ).val=i.val) :
    (chooseField D 0 (catalystFlag (z:=z) (W:=W) (k:=k) (depth:=depth) a)
      (header F (withPorts s c b G) a).fieldTerm).eval m occ =
      (catalystFlag (z:=z) (W:=W) (k:=k) (depth:=depth) a i).eval m occ :=
  eval_chooseField _ _ _ _ _ _ i (by simpa using fit) (by simpa using hit)

end Hierarchy.ProtocolRAM.Calendar.StripChart
end

end OAI
