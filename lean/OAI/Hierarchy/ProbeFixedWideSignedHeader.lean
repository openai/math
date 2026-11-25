import OAI.Hierarchy.ProbeFixedWideSignedCore
import OAI.Hierarchy.ProtocolRAMChargedCoreHeader

namespace OAI
/-! # Every original core header field on the replayed terminal memory -/
noncomputable section
set_option quotPrecheck false
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage CoreBoard CoreRoute ReportSockets
open CatalystArchive StripChart CatalogueRows ColumnWires
open scoped Classical Fin.CommRing
variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)
  (h width : ℕ)
local notation "P" => v.widePlacement h width
local notation "s" => v.nativeBoards P h width
local notation "A" => v.privateArena P h width
local notation "E" => v.publicHeader P h width
local notation "D" => 2^v.W
local notation "N" => Stages h D
local notation "r" => Fintype.card (Slots h D k)
local notation "num" => Fintype.card (Columns h D)*k
local notation "w" => Native.wordBits h D Native.copies
local notation "start" => v.catalystStaticStart P h width
local notation "decl" => declaredRows v.mesh (ownerLedger s v.mesh (P).catalogue (P).routes F A)
local notation "cnt" => rowOnlyCount v.mesh decl
local notation "stride" => ownerRowFactor D k v.sampler.degree v.depth
  (max (Fintype.card (StripDirectory.PayloadRole N k)) (Fintype.card (StripDirectory.PurchasedRole v.depth k)))*2^h



local notation "R" => WideMemory.R v.sampler h v.W k
local notation "K" => WideMemory.K h v.W
local notation "H" => WideMemory.H h v.W k v.wideJobs
local notation "dir" => WideMemory.dir h v.W k v.wideJobs
local notation "head" => CoreCatalogue.headBase h v.W K (dir).groups H

theorem wide_signed_header_at (size : ℕ) (fits : (A).endAddress v.mesh ≤ size) (stock : Bank) (M : ℕ)
    (π : Equiv.Perm (Fin (2^h))) (o : Orders h D k) (raw : Boot.Tape h D) (wordRoom : (A).endAddress v.mesh<2^w)
    {output : Boot.Tape h D} (low : ∀x,x<(A).first → output x=v.wideSignedMidAt h width size stock M π o raw x) :
    CoreCatalogue.Header (v.wideOrder h width) head v.wideJobs (CoreCatalogue.groupStart h v.W) M output := by
  have sourcePrefix:=v.wideGeometryPrefix h width
  have first:=v.catalyst_initial_le_first P h width
  have room : (P).joint.initial ≤ size:=first.trans ((Nat.le_add_right ..).trans fits)
  have port : (P).joint.initial≤(E).ports.base:=
    (Nat.le_add_right ..).trans ((JointHeader.order (P).joint h N k).trans (Nat.le_add_right ..))
  have marketsLow (i) : (P).joint.initial≤Boot.low (v.catalystMarkets P h width i):=
    first.trans (v.catalyst_market_low P h width i)
  obtain ⟨_,boot,_,_,_,_,_,_,_⟩:=v.wide_signed_boot_at h width size fits stock M π o raw wordRoom
  have ready : CoreCatalogue.Header (v.wideOrder h width) head v.wideJobs (CoreCatalogue.groupStart h v.W) M
        (v.wideSignedMidAt h width size stock M π o raw):=by
    apply charged_master_core_header (coreEnd:=sourcePrefix.2.2) (ports:=port) (allocated:=room) (marketsLow:=marketsLow)
    exact boot
  apply ready.frame
  intro x _ hi
  let topAt:=CoreCatalogue.top h v.W K (dir).groups H R
  have extent : head+CoreCatalogue.headerWords R≤topAt:=(le_max_left ..).trans (le_max_right ..)
  obtain ⟨keys,outer⟩:=BoughtSockets.Public.borders v.sampler topAt h v.W k v.wideJobs v.depth
  have endDir : topAt≤CoreRoute.directoryBase v.sampler h v.W k v.wideJobs v.depth K (dir).groups H R :=
    (Nat.le_add_right ..).trans (keys.trans outer)
  exact low x (hi.trans_le (extent.trans (endDir.trans ((Nat.le_add_right ..).trans (sourcePrefix.2.2.trans first)))))

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
