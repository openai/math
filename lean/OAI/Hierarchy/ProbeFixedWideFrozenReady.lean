import OAI.Hierarchy.ProbeFixedWideSettlement
import OAI.Hierarchy.ProbeFixedDatedMarket

namespace OAI
/-! # Dated purchase readiness on the original signed, priced, retained input tape -/
noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage CoreBoard CoreRoute ReportSockets BoughtSockets
open CatalystArchive StripChart CatalogueRows ColumnWires
open scoped Fin.CommRing Classical
variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)
  (h width : ℕ)
local notation "P" => v.widePlacement h width
local notation "A" => v.privateArena P h width
local notation "D" => 2^v.W
local notation "w" => Native.wordBits h D Native.copies
local notation "stock" => v.fixedTerminalStock P h width
local notation "order" => wideRouteOrder h D k
local notation "C" => v.wideSignedChart h width stock

/-- A fixed lower threshold pays for both the finite menu and the true purchase sampler. -/
def wideMarketHeight := max (2*k+v.sampler.degree) (max v.menu.maximum ⌊2*v.toleranceAt*(v.precision:ℝ)⌋₊)

theorem wide_market_ready (size : ℕ) (extent : (A).endAddress v.mesh ≤ size) (M : ℕ)
    (π : Equiv.Perm (Fin (2^h))) (raw : Boot.Tape h (2^v.W)) (a : Attempt) (prior later : List Event)
    (split : events v.mesh=prior++Event.attempt a::later) (age : v.wideMarketHeight≤h)
    (room : (A).endAddress v.mesh<2^w)
    (ran : Calendar.mounted C prior (v.wideSignedMidAt h width size stock M π order raw)) :
    ((C).frozen a).ready ((guard C a).apply (run C prior (v.wideSignedMidAt h width size stock M π order raw))) := by
  let coreStart:=CoreCatalogue.top h v.W (WideMemory.K h v.W) (WideMemory.dir h v.W k v.wideJobs).groups
    (WideMemory.H h v.W k v.wideJobs) (WideMemory.R v.sampler h v.W k)
  have sourcePrefix:=v.wideGeometryPrefix h width
  have keyEnd:=(Public.borders v.sampler coreStart h v.W k v.wideJobs v.depth).2
  have dir : (StripDirectory.stratumHeader h D k v.sampler.degree v.depth (P).routes.directory.keysBase).stop≤(P).joint.initial :=
    keyEnd.trans ((Nat.le_add_right ..).trans sourcePrefix.2.2)
  have hfit : h<2^w := (Nat.lt_two_pow_self (n:=h)).trans (v.date_prefix_fit h)
  have limit:=v.wide_signed_boot_at h width size extent stock M π order raw room
  exact v.dated_market_ready P h width _ _ _ _ _ _ π _ _ limit.2.1 a prior later split ran sourcePrefix.2.1 room
    ((Nat.le_max_left ..).trans age)
    (((Nat.le_max_left ..).trans ((Nat.le_max_right ..).trans age)).trans_lt hfit)
    (((Nat.le_max_right ..).trans ((Nat.le_max_right ..).trans age)).trans_lt hfit) dir

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
