import OAI.Hierarchy.TaggedWideInstalledHistory
import OAI.Hierarchy.TaggedWidePrivateReceipt
import OAI.Hierarchy.TaggedWidePrivateTariff

namespace OAI
/-! # The paid reporter's private-equality circuit in the full fixed parent frame -/
noncomputable section
set_option quotPrecheck false
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage ProbeStage.Native CoreBoard PhysicalTerm
open HistoryRoles ReportSockets Tagged TaggedPrune Tagged.WideStack Tagged.WideControlJoin
open ThreeFlat Routing
open scoped Classical Fin.CommRing BigOperators
variable {F Ex Se : Type} [Field F] [Fintype Ex] [Fintype Se] {k : ℕ} {p q Q σ Λ κ A : ℝ}
    (v : FixedProtocolFormat F k p q Q σ Λ) (x : WideParent κ A)
    (m ell short : ℕ) (u : ℝ→ℝ) (δ ξ : ℝ) (unitCost : ℕ)
local notation "P" => v.widePlacement x.h x.w
local notation "board" => (P).catalogue
local notation "order" => v.wideOrder x.h x.w
local notation "g" => v.wideDated x.h x.w ell unitCost
local notation "S" => v.wideInstalledSize x m ell unitCost g
local notation "W" => wordBits x.h (2^v.W) copies
local notation "D" => v.parentShared x m ell short unitCost ((events v.mesh).length+1)
local notation "dst" => CatalystArchive.TerminalLayout.destination (v.wideSignedPage x.h x.w (v.fixedTerminalStock P x.h x.w))
local notation "cap" => v.widePrivateUnit unitCost*x.w
variable (lim : v.FullGateRoom x m ell short u δ ξ unitCost)
local notation "G" => (v.wideFullGates x m ell short u δ ξ unitCost lim).2
local notation "V" => SitePins Ex Se D G

theorem wide_private_report_inside : dst+9*(board).rows≤(G).u := by
  have original:=v.wide_report_before_root x
  have cells:=ProtocolRAMPurchaseSampler.lt_span (3*(board).rows)
  have rom:=v.wide_installed_root_le_size x m ell unitCost g
  have span : S≤(g).workEnd S:=by
    unfold WideCPU.Dated.workEnd WideCPU.Dated.slotStart WideCPU.Dated.maskStart WideCPU.Dated.controlStart
      WideCPU.Dated.rolesEnd WideCPU.endOf
    omega
  have seen:=v.wide_history_inside x m ell short u δ ξ unitCost lim
  omega

local notation "area" => v.wide_private_report_inside x m ell short u δ ξ unitCost lim
local notation "pairPin" => fun (side:Bool) (r:(board).Private order) (j:Fin cap)=>
  (.inr (.inr (.inl (.inr (.inl (side,⟨r,j⟩))))) : V)

def widePrivateGate (low : WideParent.columnBits cap≤(G).W+1) : WideCalendarSites.Net F V := by
  exact (board).privatePaired (F:=F) order G dst area low pairPin
local notation "net" narrow => v.widePrivateGate (Ex:=Ex) (Se:=Se) x m ell short u δ ξ unitCost lim narrow

theorem wide_private_fee (low : WideParent.columnBits cap≤(G).W+1) : (net low).cells+(net low).internal≤2*Fintype.card ((board).Private order)*cap*
      (200*WideParent.columnBits cap+65)+Fintype.card ((board).Private order)*cap := by
  exact (board).privateBits_cost (F:=F) order (WideParent.column_lt cap).le
    ((board).privateWidthPin (E:=Ex) (Se:=Se) («D»:=D) G dst area low) pairPin

theorem wide_private_read (low : WideParent.columnBits cap≤(G).W+1) (raw : Fin (board).rows→ProtocolRAMEmit.Row) (initial final : Memory W) (volts : V→Bool)
    (frame : ∀a,dst≤a→a<dst+9*(board).rows→final a=ProtocolRAMEmit.emitted dst raw initial a)
    (reads : ∀i j,volts ((board).privateWidthPin (E:=Ex) (Se:=Se) («D»:=D) G dst area low i j)=
      (G).terminal final ((board).privateWidthRow G dst area i,j.castLE low))
    (bound : ∀i:(board).Private order,(raw i.val).width≤cap) (fits : cap<2^W) :
    TypedWiring.value (net low) volts =
      if EndsPadded (fun i=>(raw i.val).width) (fun _ : (board).Private order=>cap)
        (fun side i j=>volts (pairPin side i j))
      then ∏i : (board).Private order,if ∀j : Fin cap,j.val<(raw i.val).width→
        volts (pairPin false i j)=volts (pairPin true i j) then 1 else 0 else 0 := by
  exact (board).privatePaired_read order G dst area low pairPin raw initial final volts
    (fun _=>rfl) frame reads bound (fun i=>(bound i).trans_lt fits)

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat

end
end OAI
