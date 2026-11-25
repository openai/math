import OAI.Hierarchy.TaggedWideTimelineWidthPins
import OAI.Hierarchy.TaggedWideFullGates
import OAI.Hierarchy.TaggedWideWindowResident
import OAI.Hierarchy.TaggedWideParentTariffs

namespace OAI
/-! # The complete history padding circuit at the actual parent's dated role tables -/
noncomputable section
set_option quotPrecheck false
set_option hygiene false
set_option maxRecDepth 8192
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open LinearAlgebra.SpectralBooks ChordGraph
open ThreeFlat Routing Diagonal TraceWords
open Computability.VPVNP.BurstRAM PrivateRAM ProbeStage ProbeStage.CoreBoard HistoryRoles
open Tagged Tagged.WideControlJoin WireTelescope CalendarTape
open scoped Classical BigOperators Fin.CommRing

variable {F Ex Se : Type} [Field F] [Fintype Ex] [Fintype Se] {k : ℕ} {p q Q σ Λ κ A : ℝ}
    (v : FixedProtocolFormat F k p q Q σ Λ) (x : WideParent κ A)
    (m ell short : ℕ) (u : ℝ→ℝ) (δ ξ : ℝ) (unitCost : ℕ)
local notation "n" => x.h
local notation "w" => x.w
local notation "es" => events v.mesh
local notation "dated" => v.wideDated x.h x.w ell unitCost
local notation "l" => v.wideInstalledLayout x m ell short u δ ξ unitCost dated
local notation "S" => v.wideInstalledSize x m ell unitCost dated
local notation "roles" => HistoryRoles.ceiling v.sampler (h:=n) (W:=v.W) (k:=k) (attempts:=v.wideJobs)
  v.mesh unitCost v.keepLimit (CatalystArchive.fuel v.mesh) w
local notation "R" => Public v.sampler n v.W k v.wideJobs
local notation "cap" => v.wideHistoryUnit unitCost*w
local notation "N" => ((es).length+1)*Fintype.card ((r:R)×Fin (roles r))
local notation "Data" => v.parentShared x m ell short unitCost ((es).length+1)
variable (lim : v.FullGateRoom x m ell short u δ ξ unitCost)
local notation "G" => (v.wideFullGates x m ell short u δ ξ unitCost lim).2
local notation "B" => WideParent.columnBits cap
local notation "V" => SitePins Ex Se Data G
local notation "index" => fun r:R=>(shelfSlot v.sampler r : Fin (dated).roleWords)

theorem wide_history_inside : (dated).workEnd S≤(G).u := by
  have upper:=v.wideInstalled_upper x m ell short u δ ξ unitCost dated
  have after:=v.wide_window_after_terminal x ((dated).workEnd S)
  have endRoom:=v.wide_full_end x m ell short u δ ξ unitCost lim
  have extra : (l).floor≤WindowSeries.finish (l).floor (l).need:=Nat.le_add_right ..
  omega

local notation "inside" => v.wide_history_inside x m ell short u δ ξ unitCost lim
local notation "cover" => HistoryRoles.ceiling_le v.sampler v.mesh unitCost v.keepLimit (CatalystArchive.fuel v.mesh) w
variable (low : B≤(G).W+1)
local notation "datum" => fun i : Fin N=>(.inr (.inr (.inl (.inr (.inr (.inl i))))) : V)

def wideHistoryGate := observedTimeGuard (F:=F) es roles cap cover dated S G inside index low datum
local notation "net" => v.wideHistoryGate (Ex:=Ex) (Se:=Se) x m ell short u δ ξ unitCost lim low

theorem wide_history_fee : (net).cells+(net).internal≤N*(200*B+65) :=
  timeGuard_cost ..

theorem wide_history_read {K:ℕ} {X:Type} (slot:Event→WireTelescope.CalendarTape.Slot X) (wire:X→Widths K)
    (cells:∀state,((s:Fin K)×SiteBit (wire state) s)↪((r:R)×Fin (roles r)))
    (start:X) (path:Path slot es start) (final : Memory (G).W) (volts:V→Bool) (bits:Fin N→Bool)
    (snapshot : ∀t r j,volts (observedWidthPin (Ex:=Ex) (Se:=Se) («Data»:=Data) es cap dated S G inside index low t r j)=
      (G).terminal final (observedWidthRow es dated S G inside index t r,j.castLE low))
    (word : ∀t (r:R),(final ((dated).roleStart S t+1+(index r).val)).val≤cap)
    (states : ∀t (z:(r:R)×Fin (roles r)),z∈Set.range (cells (boundaryState slot es start path t)) ↔
      z.2.val<(final ((dated).roleStart S t+1+(index z.1).val)).val)
    (shared : ∀i,volts (datum i)=bits i) :
    TypedWiring.value net volts = if ∀i,bits i=true→i∈Set.range (timelineFin slot wire cells es start path)
      then 1 else 0 := by
  apply observedTimeGuard_value es roles cap cover dated S G inside index low slot wire cells start path
    final datum volts bits _ snapshot shared word states
  intro t r
  rfl

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat

end
end OAI
