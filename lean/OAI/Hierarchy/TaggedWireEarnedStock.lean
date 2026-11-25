import OAI.Hierarchy.ProbeFixedStoredRoleWords
import OAI.Hierarchy.ProbeFixedUniformFailureExpr
import OAI.Hierarchy.ProbeFixedElectionPages
import OAI.Hierarchy.ProtocolRAMCatalystLiveOwners
import OAI.Hierarchy.ProtocolRAMRepairCommodity
import OAI.Hierarchy.TaggedWireInstallShape

namespace OAI
/-! The retained input of an installed strip uses its actual inventory row. -/
noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM ProbeStage ProbeStage.Native AdaptiveProbe StripDirectory PurchaseFrozen CoreBoard
open WireTelescope.ChosenPackets
open scoped Classical Fin.CommRing
variable {F : Type*} [Field F] {k : ℕ} {p q Q σ Λ : ℝ}
  (v : FixedProtocolFormat F k p q Q σ Λ) (P : v.Placement) (h width : ℕ)
local notation "N" => Stages h (2^v.W)
local notation "w" => wordBits h (2^v.W) copies
local notation "B" => v.nativeBoards P h width
local notation "G" => Commodity (Fin (2^h)) N k
local notation "A" => v.privateArena P h width

/-- Convert the native inventory ordinal to the stock prefix of the installed
matrix. Its physical value is unchanged by the catalogue suffix. -/
def earnedStockRow (edges : ℕ) (g : G) : Fin (Fintype.card G+edges) :=
  stockRow (p:=edges) ((finCongr (PurchaseInventory.card_commodity h N k).symm)
    (PurchaseInventory.slotEquiv h N k g))

theorem payload_stored (phase trial : ℕ) (m : Memory w) (i : Fin (2^h)) (u : PayloadStrip.Quotes N k) :
    (v.widePayloadStored P h width phase trial u).eval m (i.val:Word w)=
      ((v.earnedStockRow h P.catalogue.rows (PayloadStrip.rowAddress i u)).val:Word w) :=
  payloadSlot_read m i u

theorem purchased_stored (phase trial slice inner : ℕ) (π : Equiv.Perm (Fin (2^h)))
    (marks : StageAt h (2^v.W)→Fin k×Bool→Finset (Fin (2^h)))
    (path : LiveChains v.sampler π v.depth marks) (m : Memory w)
    (tiles : ∀i : Key h (2^v.W) k, ProtocolRAMPurchaseGateColumns.TileRows
      ((((B).outer phase trial).market.shelf).L v.sampler v.depth i).source
      (Shelf.pathRows v.sampler π v.depth i) m)
    (headers : (stratumHeader h (2^v.W) k v.sampler.degree v.depth ((B).stratumHeader phase trial)).Loaded m)
    (keys : count h (2^v.W) k≤2^w) (room : (v.depth+1)*paths h v.sampler.degree v.depth≤2^w)
    (u : ChainStrip.Axes v.depth k) :
    (v.widePurchaseStored P h width phase trial slice inner u).eval m ((BoughtLocation.relative path).val:Word w)=
      ((v.earnedStockRow h P.catalogue.rows (stripAddress v.sampler π v.depth marks path u)).val:Word w) :=
  relative_stock _ _ marks path m tiles headers keys room u

theorem payload_stored_work (phase trial : ℕ) (u : PayloadStrip.Quotes N k) :
    (v.widePayloadStored P h width phase trial u).work≤v.coordinateWork :=v.payload_coordinate h u

theorem purchased_stored_work (phase trial slice inner : ℕ) (u : ChainStrip.Axes v.depth k) :
    (v.widePurchaseStored P h width phase trial slice inner u).work≤v.coordinateWork :=
  v.purchased_coordinate h _ _ _ u

theorem payload_stored_fits (phase trial out : ℕ) (u : PayloadStrip.Quotes N k) :
    (v.widePayloadStored P h width phase trial u).Fits w out := by
  rcases u with p|⟨s,j⟩
  · trivial
  · exact ⟨trivial,trivial⟩

theorem purchased_stored_fits (phase trial slice inner top : ℕ) (u : ChainStrip.Axes v.depth k)
    (word : top<2^w) (current : (A).base v.mesh (.attempt (.inner phase trial slice inner))≤top)
    (directory : (stratumHeader h (2^v.W) k v.sampler.degree v.depth ((B).stratumHeader phase trial)).stop≤top) :
    (v.widePurchaseStored P h width phase trial slice inner u).Fits w top := by
  let H:=stratumHeader h (2^v.W) k v.sampler.degree v.depth ((B).stratumHeader phase trial)
  obtain ⟨flag,tiles⟩:=v.catalyst_bought_bank_room P h width phase trial slice inner
  apply Expr.fits_of_inputEnd _ _ word
  apply (purchased_before _ _ _ _ top (fun i=>(tiles i).trans current) (flag.trans current) ?_).address u
  change H.ball.base+H.ball.size≤top ∧ H.field.base+H.field.size≤top
  change H.start+H.small≤top ∧ H.start+H.small+H.small≤top
  change H.start+2*H.small+H.large+H.large≤top at directory
  omega

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
