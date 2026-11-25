import OAI.Hierarchy.ProbeFixedActivationCoordinates
import OAI.Hierarchy.ProbeFixedGuardPages
import OAI.Hierarchy.ProbeFixedStockCap

namespace OAI
/-! # Concrete price ROM cells at the measured reserve replay -/
noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage ProbeStage.Native StockCommit StripChart StripDirectory
open scoped Classical Fin.CommRing
variable {F : Type*} [Field F] {k : ℕ} {p q Q σ Λ : ℝ}
    (v : FixedProtocolFormat F k p q Q σ Λ) (P : v.Placement) (z width : ℕ)
    (r : ℕ) (banks : RouteSettlement.Banks) (src tab dst : ℕ) (owners : Bank)
local notation "N" => CoreBoard.Stages z (2^v.W)
local notation "W" => wordBits z (2^v.W) copies
local notation "C" => v.nativeChart P z width r banks src tab dst owners
local notation "A" => v.billedAccount P z width r banks src tab dst owners
local notation "G" => v.privateArena P z width
local notation "f" => v.nativeFormats P z width
local notation "H" => v.publicHeader P z width
local notation "g₀" => JointHeader.scores P.joint z N k
local notation "pr" => DeadlineROM.prices v.mesh v.finish (v.basePhase width)
local notation "quotes[" t "]" => PurchaseCT.publicPhase (publicStages v.W) v.a v.radius v.W (probeHeat v.W) t width v.precision

/-- The price word for each live commodity at the replay, obtained from the
initialized scalar-price page and the offset bank installed for this date.
The capped chronological inventory supplies the price page's stock index. -/
theorem activation_quote_cells (init : Memory W) (phase trial layer tick : ℕ)
    (hp : phase<v.mesh.inject+v.mesh.cool) (hh : trial<v.mesh.outerFuel)
    (hj : layer<v.mesh.reserveSteps) (hb : tick<v.mesh.innerFuel)
    (resident : (H).Resident init) (stock : ℕ→ℕ)
    (mountedPrices : InitialPrices P.joint z N k pr stock init)
    (bounded : StockBound.Run C (v.stockBanks P z width) init z N k (v.keepLimit*width))
    (stride : v.keepLimit*width<(g₀).stride) :
    let ev:=Attempt.inner phase trial layer tick
    let surface:=(v.nativeBoards P z width).inner phase trial layer tick
    let tested:=replayScoreMemory C init phase trial layer tick
    let base:=(f ev).market.shelf.stockBase
    QuoteCells (quotes[reserveTime v.mesh v.finish phase layer]) tested surface.price
      (GlobalTests.offsets surface.globalTests) {surface.old with base:=base}
      PurchaseInventory.slot PurchaseInventory.lane
      (fun i : Commodity (Fin (2^z)) N k=>PurchaseInventory.stock base tested i) (g₀).stride := by
  intro ev surface tested base
  let entry:=innerState C init phase trial layer tick
  let guardMem:=(guard C ev).apply entry
  let bs:=v.issued P z width r banks src tab dst owners
  let phasePage:=DeadlineROM.scorePage v.mesh g₀ z N k ev
  let t:=DeadlineROM.index v.mesh ev
  obtain ⟨tail,cut⟩:=inner_slot C init phase trial layer tick hp hh hj hb bounded.mounted_all
  have buffers:=v.guard_pages_at_slot P z width r banks src tab dst owners ev _ tail init entry cut resident stock mountedPrices
  have date : dateInTable v.mesh ev:=⟨hp.le,hj.le⟩
  have lower:=v.activation_stock_floor P z width ev
  have atGate:=v.activation_guard_floor P z width r banks src tab dst owners ev
  have word:=cut.currentReady.1.2
  change (C).stopAt ev+1<2^W at word
  have rowFit : GlobalTests.rows z N k≤2^W := by
    change PurchaseInventory.footprint z N k≤2^W
    omega
  have cap:=v.stock_cap C rfl G f P.joint.initial (v.emptyReserve P z width).base width bs init bounded
  have lim (i : Commodity (Fin (2^z)) N k) : (entry ((A).stockAt ev i)).val<(g₀).stride :=
    (cap.2 phase hp trial hh layer hj tick hb.le i).trans_lt stride
  have cells:=v.row_quote_cells P z width bs ev entry guardMem date buffers.1.scalar buffers.2 rowFit
    (v.guard_quote_stock P z width bs r banks src tab dst owners ev entry) lim
  have keep (address : ℕ) (early : address<(G).base v.mesh (.attempt ev)) : tested address=guardMem address := by
    have now:=replay_prior C init phase trial layer tick address cut.currentReady
      (v.event_prefix P z width r banks src tab dst owners (.attempt ev) address early).1
    exact now.trans ((v.row_buffer_frame P z width r banks src tab dst owners ev entry cut.currentReady address early).1).symm
  have read (bank : Bank) (early : bank.base+bank.size≤(G).base v.mesh (.attempt ev)) (ix : Word W) :
      bank.read tested ix=bank.read guardMem ix :=
    keep _ ((Nat.add_lt_add_left (Nat.mod_lt ix.val (Nat.two_pow_pos bank.bits)) bank.base).trans_le early)
  have pages:=v.election_public P z width ev
  have sc : (GlobalTests.offsets phasePage).base+(GlobalTests.offsets phasePage).size≤(G).base v.mesh (.attempt ev) := by
    have lowerPage : phasePage.base≤GlobalTests.stop phasePage z N k:=by
      change phasePage.base≤phasePage.base+GlobalTests.rows z N k+2*GlobalTests.span phasePage N k
      omega
    exact (Nat.add_le_add_right lowerPage _).trans pages.2.1
  have oldEnd : (f ev).stockSource.old.base+(f ev).stockSource.old.size≤(G).base v.mesh (.attempt ev) := by
    rw [v.stock_old_size P z width ev]
    exact v.stock_padded_old P z width ev
  have actual (i : Commodity (Fin (2^z)) N k) :
      PurchaseInventory.stock base tested i=(entry ((A).stockAt ev i)).val := by
    change PurchaseInventory.stock base tested i=(entry ((v.nativeAccount P z width bs).stockAt ev i)).val
    rw [v.stock_pointer P z width bs ev i]
    exact congrArg Fin.val (v.activation_replay_word P z width r banks src tab dst owners init phase trial
      layer tick hp hh hj hb bounded.mounted_all i)
  constructor
  · intro i
    exact (read (GlobalTests.offsets phasePage) sc _).trans (cells.offset i)
  · intro i
    rw [actual]
    exact (read (f ev).stockSource.old oldEnd _).trans (cells.stock i)
  · intro i
    rw [actual]
    exact (read ((H).scalar.bank t) pages.1 _).trans (cells.rom i)

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
