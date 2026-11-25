import OAI.Hierarchy.TaggedWidePacketMenuCost
import OAI.Hierarchy.TaggedWidePacketWantedCost
import OAI.Hierarchy.ProbeFixedWidePacketFields
import OAI.Hierarchy.ProbeFixedPaidOperandWork

namespace OAI
/-! # Fixed input costs of the real party, catalogue, earned histogram and saved selector -/
noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open LinearAlgebra.SpectralBooks ChordGraph
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage ProbeStage.Native CoreBoard HistoryRoles
open BoughtSockets PurchaseFrozen Strip StripChart StripDirectory CatalystArchive CatalogueRows WideCPU WireTelescope
open scoped Classical
open private primaryWork wide_primary_work from OAI.Hierarchy.ProbeFixedPaidOperandWork
variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)
local notation "stat" => publicStages v.W

def packetColumnRate:=56+8*ReportSockets.copies k v.wideJobs+purchasedColumnWork (2^v.W) k v.wideJobs
def packetInputRate:=v.packetColumnRate+v.coordinateWork+primaryWork v+v.payloadQuantityWork stat+
  v.purchaseQuantityWork+v.ballotWork+20

def packetRowsRate:=max (Fintype.card (PayloadRole stat k⊕TreeLink (PayloadStrip.edgeCount stat) k))
  (Fintype.card (PurchasedRole v.depth k⊕TreeLink (ChainStrip.edgeCount v.depth) k))
def packetWantsRate:=max (Fintype.card ((PayloadStrip.Columns stat×Fin k)⊕PayloadStrip.Quotes stat k))
  (Fintype.card ((ChainStrip.Columns v.depth×Fin k)⊕ChainStrip.Axes v.depth k))

def packetValueRate:=let b:=v.packetInputRate
  1+(v.menuCodes stat)*10+v.ballotWork+catalogueWork v.packetRowsRate v.widePacketDegree b+
  SiteDirectory.wantWork (v.menuCodes stat) v.packetWantsRate (b+12)+b+15+
  PacketScan.firstWork v.widePacketDegree (3*(b+12)+7)+
  WireTelescope.PacketTurns.Operands.middleValueRate v.packetRowsRate (CatalogueRows.baseBound b)

variable (h width : ℕ)
local notation "N" => Stages h (2^v.W)
local notation "P" => v.widePlacement h width
local notation "fs" => v.nativeFormats P h width
local notation "budget" => v.packetInputRate

theorem packetRows_eq : v.widePacketRoles h=v.packetRowsRate := by
  simp [widePacketRoles,packetRowsRate,fixed_stage_count]

theorem payload_columns_bound (c : PayloadStrip.Columns N) :
    ((v.payloadPricePorts P h width).column c).work≤v.packetColumnRate := by
  apply (show ((v.payloadPricePorts P h width).column c).work≤56+8*ReportSockets.copies k v.wideJobs from
    ColumnROM.payload_work _ _ _ _ _ _ _ _ _ _).trans
  unfold packetColumnRate;omega

theorem purchase_columns_bound (p t : ℕ) (c : ChainStrip.Columns v.depth) :
    ((v.purchasedPricePorts P h width p t).column c).work≤v.packetColumnRate := by
  apply (show ((v.purchasedPricePorts P h width p t).column c).work≤purchasedColumnWork (2^v.W) k v.wideJobs from
    purchased_column_work _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).trans
  unfold packetColumnRate;omega

theorem widePacket_site_rate (siteROM : ℕ) (a : Attempt) (i : Fin (v.wideBallotParties h a)) :
    (v.wideBallotSite P h width siteROM a i).work≤budget := by
  cases a with
  | outer p t=>
    let c:=((SiteNaming.labels (X:=TreeSite (PayloadStrip.edgeCount N) k)).symm i).1
    have w:=v.payload_columns_bound h width c
    change 1+((v.payloadPricePorts P h width).column c).work+1+5≤_
    unfold packetInputRate;omega
  | inner p t j l=>
    let c:=((SiteNaming.labels (X:=TreeSite (ChainStrip.edgeCount v.depth) k)).symm i).1
    have w:=v.purchase_columns_bound h width p t c
    change 1+((v.purchasedPricePorts P h width p t).column c).work+1+5≤_
    unfold packetInputRate;omega

theorem payload_primary_bound (p t : ℕ) (r : PayloadRole N k) :
    ((v.payloadPricePorts P h width).primary (P).catalogue r).work≤budget :=
  (wide_primary_work v h width (.outer p t) r).trans (by unfold packetInputRate;omega)

theorem purchase_primary_bound (p t j l : ℕ) (r : PurchasedRole v.depth k) :
    ((v.purchasedPricePorts P h width p t).primary (P).catalogue r).work≤budget :=
  (wide_primary_work v h width (.inner p t j l) r).trans (by unfold packetInputRate;omega)

theorem widePacket_base_rate (siteROM : ℕ) (a : Attempt) (i : Fin (v.wideBallotParties h a))
    (c : Fin (v.wideBallotShape P h width (.attempt a)).columns) :
    ((v.wideFields P h width siteROM (.attempt a)).value i c).work≤v.packetValueRate := by
  refine Fin.cases ?_ (Fin.cases ?_ (fun j=>?_)) c
  · change (Ballot.participant (v.menuCodes N) (v.earnedTag P h width a) i).work≤_
    have est:=BoughtSockets.choose_work_bound (v.menuCodes N) 1 1
      (fun j: Fin (v.menuCodes N)=>Expr.lit (j.val*v.wideBallotParties h a+i.val+1)) (v.earnedTag P h width a) (fun _=>le_rfl)
    apply est.trans
    change 1+v.menuCodes N*(7+1+2)≤_;rw [show Stages h (2^v.W)=publicStages v.W from fixed_stage_count h v.W]
    simp only [packetValueRate];omega
  · change 2+1+1≤_;simp only [packetValueRate];omega
  · exact ((v.native_row_work P h width a).fields j).trans (by simp only [packetValueRate];omega)

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat

end
end OAI
