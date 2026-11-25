import OAI.Hierarchy.DescentResetActorClassIssued
import OAI.Hierarchy.DescentRetainedPrimaryToken

namespace OAI
/-! # Recover precisely the selected old endpoint key at the compact retained actor -/
namespace Hierarchy.DescentResetActorClass
open DescentCommonHost DescentContacts DescentHostDirectory DescentSIMDLookup DescentDenseHostOrder DescentDatedAddressBook.ActorSetup
noncomputable section
set_option quotPrecheck false
variable {n h : ℕ} (board : NonlinearExpanders.Graph n h)
local notation "Q" => (DescentCommonPalette.rotor board).Site


def primaryTarget {V : Type} (r : ℕ) : Node V (V×Endpoint (2^n)) Q → Option ℕ
  | .trunk false z=>some (DescentFallbackShapeTable.cell r z.2)
  | _=>none

def targetBook (r height : ℕ) (j : Fin (roster board r height).card) :=
  primaryTarget board r (shapeAt board r height j)

theorem targetBook_cast {n' h' : ℕ} (other : NonlinearExpanders.Graph n' h')
    (dim : n=n') (depth : h=h') (same : HEq board other) (height r r' : ℕ)
    (low : r=r') (size : (roster board r height).card=(roster other r' height).card)
    (u : Fin (roster board r height).card) :
    targetBook other r' height (u.cast size)=targetBook board r height u:=by
  subst n';subst h';subst r';cases eq_of_heq same;rfl

theorem target_shape {V : Type} (r : ℕ) (v : Node V (V×Endpoint (2^n)) Q) :
    primaryTarget board r (shape board v)=primaryTarget board r v:=by
  cases v with
  | trunk side key=>cases side <;>rfl
  | good => rfl
  | fall => rfl
end
end Hierarchy.DescentResetActorClass

namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentCompiler DescentColonies DescentSharedCableNames DescentStageEdgeReceipt DescentResetAttachments
open DescentDenseHostOrder DescentPackedZip DescentSIMDLookup DescentResetActorClass DescentDatedAddressBook.ActorSetup
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM
open scoped Classical Fin.CommRing
noncomputable section
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
  {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k i z D n h C f g cut tail wire hist : ℕ}
  {input : Reached W G q ε S k i z D wire hist} {ctl : ResetRates G S k D n h C f g cut tail}
  (B : ClosedReset input ctl)
set_option quotPrecheck false
local notation "Z" => B.reset
local notation "T" => B.terminals
local notation "height" => GroupStage.depthBound D n f g
local notation "residual" => ((Z).k-(T).commonDepth)
local notation "pool" => roster (Z).graph residual height
local notation "vertex" => B.frame.host.symm.toEmbedding.trans input.vertex
variable {oldHosts hosts groups lanes bw : ℕ} (previous : Fintype.card input.V≤oldHosts)
local notation "rawRank" => (Z).rawHostRank T ((vertex).trans (Fin.castLEEmb previous))

theorem native_target_at (v : B.next.V) :
    targetBook (Z).graph residual height ((Z).hostFields T ((vertex).trans (Fin.castLEEmb previous)) v).2=
      primaryTarget (Z).graph residual v.val:=by
  unfold targetBook
  rw [show shapeAt (Z).graph residual height ((Z).hostFields T ((vertex).trans (Fin.castLEEmb previous)) v).2=
      shape (Z).graph v.val from congrArg Subtype.val ((shapeIndex (Z).graph residual height).symm_apply_apply ((Z).localShape T v))]
  exact target_shape _ _ _

theorem calendar_primary_target (v : B.next.V) :
    targetBook ctl.board k height (((Z).hostFields T ((vertex).trans (Fin.castLEEmb previous)) v).2.cast B.public_hub_slots)=
      primaryTarget (Z).graph residual v.val:=by
  have low : residual=k:=by rw [B.commonDepth,B.keyWidth];omega
  exact (targetBook_cast (Z).graph ctl.board B.dimension rfl B.graph height residual k low B.public_hub_slots _).trans
    (native_target_at B previous v)

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
