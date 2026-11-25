import OAI.Hierarchy.ProbeFixedPacketAtom
import OAI.Hierarchy.ProbeFixedNativeBoards
import OAI.Hierarchy.ProbeStripSizeGuard

namespace OAI
/-! # Literal payload and purchase strip capacities on the calibrated native boards -/

noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage ProbeStage.Native CoreBoard
open StripChart StripDirectory CatalogueRows StockCommit PurchaseStage RepairHistogram CatalystArchive
open scoped Fin.CommRing Classical

variable {F : Type*} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)

def payloadMaximum (N : ℕ) :=
  letI : Nonempty (PayloadRole N k) := ⟨.catalyst (PayloadStrip.first N 0) ⟨0,v.positive⟩⟩
  (PacketWidths.ofMenu (v.payloadPacketMenu N)).maximum

def purchaseMaximum :=
  letI : Nonempty (PurchasedRole v.depth k) := ⟨.catalyst (ChainStrip.inlet v.depth 0) ⟨0,v.positive⟩⟩
  (PacketWidths.ofMenu v.purchasePacketMenu).maximum

def stripPorts (N : ℕ) := max (Fintype.card (PayloadRole N k)) (Fintype.card (PurchasedRole v.depth k))

def purchaseCounterHeight :=
  let g:=publicStages v.W*(2*k)
  let t:=v.sampler.degree^v.depth
  (1+g)+(v.depth+1)*t+g*t

/-- This public height is fixed by the two compact catalogues, role counts and socket tables. -/
def stripHeight := max (v.stripPorts (publicStages v.W) + v.menu.alphabet +
  (1+v.menuCodes (publicStages v.W)) + v.menu.maximum) v.purchaseCounterHeight

variable (P : v.Placement) (z width : ℕ)
set_option quotPrecheck false
local notation "N" => Stages z (2^v.W)
local notation "D" => v.stripPorts N
local notation "sig" => (catalogue F (v.configured (v.seed P z width)) v.cost).alphabet
local notation "bits" => wordBits z (2^v.W) copies
local notation "s" => v.nativeBoards P z width

private theorem menu_caps : v.payloadMaximum N ≤ v.menu.maximum ∧ v.purchaseMaximum ≤ v.menu.maximum := by
  rw [show N=publicStages v.W from fixed_stage_count z v.W]
  let : Nonempty (PayloadRole (publicStages v.W) k) :=
    ⟨.catalyst (PayloadStrip.first (publicStages v.W) 0) ⟨0,v.positive⟩⟩
  let : Nonempty (PurchasedRole v.depth k) := ⟨.catalyst (ChainStrip.inlet v.depth 0) ⟨0,v.positive⟩⟩
  let a := PacketWidths.ofMenu (v.payloadPacketMenu (publicStages v.W))
  let b := PacketWidths.ofMenu v.purchasePacketMenu
  exact ⟨CatalystArchive.left_maximum a b,CatalystArchive.right_maximum a b⟩

theorem strip_scalar_room (late : v.stripHeight≤z) (payload : width≤2^z) :
    ScalarRoom D sig (v.menu.copiesAt v.copyScale width) (v.menuCodes N) v.menu.maximum bits := by
  apply ScalarRoom.at_height
  · rw [(v.catalogue_words (v.seed P z width) width).1,show N=publicStages v.W from fixed_stage_count z v.W]
    exact (le_max_left ..).trans late
  · exact (Nat.div_le_self ..).trans payload

private abbrev payloadOn {letters : ℕ} (board : Boards z (2^v.W) k letters v.depth)
    (phase trial incoming : ℕ) :=
  let b := board.outer phase trial
  let surface := {b with market := {b.market with sampler := board.sampler, depth := v.depth}}
  surface.build (payloadFormat F z (2^v.W) k letters board.positive board.radius board.radius_nonneg
    board.tolerance board.tolerance_pos (board.tree (.outer phase trial)) (board.tree_nonneg _) board.minimum) incoming

private abbrev purchaseOn {letters : ℕ} (board : Boards z (2^v.W) k letters v.depth)
    (phase trial layer tick incoming : ℕ) :=
  let b := board.inner phase trial layer tick
  let surface := {b with market := {b.market with sampler := board.sampler, depth := v.depth}}
  surface.build (purchasedFormat F z (2^v.W) k letters v.depth (board.stratumHeader phase trial)
    (board.outer phase trial).market.shelf board.sampler board.positive board.radius board.radius_nonneg
    board.tolerance board.tolerance_pos (board.tree (.inner phase trial layer tick)) (board.tree_nonneg _)
    board.minimum) incoming

abbrev payloadRaw (phase trial incoming : ℕ) := payloadOn v z s phase trial incoming

abbrev purchaseRaw (phase trial layer tick incoming : ℕ) := purchaseOn v z s phase trial layer tick incoming

private theorem payload_fields {letters : ℕ} (board : Boards z (2^v.W) k letters v.depth)
    (phase trial incoming resolved : ℕ) :
    let raw := payloadOn v z board phase trial incoming
    let built := build F board (.outer phase trial) incoming
    let loaded := build F board (.outer phase trial) resolved
    let padded := PortPadding.format D (board.outer phase trial).start (payloadChannels z N k).slot raw
    raw.histMass = loaded.histMass ∧ raw.batch.batch.maxWidth = loaded.batch.batch.maxWidth ∧
      padded.pricedArea.start+raw.coordinates = built.pricedArea.start+built.pricedArea.goods :=
  ⟨rfl,rfl,rfl⟩

private theorem purchase_fields {letters : ℕ} (board : Boards z (2^v.W) k letters v.depth)
    (phase trial layer tick incoming resolved : ℕ) :
    let raw := purchaseOn v z board phase trial layer tick incoming
    let built := build F board (.inner phase trial layer tick) incoming
    let loaded := build F board (.inner phase trial layer tick) resolved
    let channels := purchasedChannels (z:=z) (d:=2^v.W) (k:=k) (board.outer phase trial).market.shelf
      board.sampler v.depth (board.stratumHeader phase trial)
    let padded := PortPadding.format D (board.inner phase trial layer tick).start channels.slot raw
    raw.histMass = loaded.histMass ∧ raw.batch.batch.maxWidth = loaded.batch.batch.maxWidth ∧
      padded.pricedArea.start+raw.coordinates = built.pricedArea.start+built.pricedArea.goods :=
  ⟨rfl,rfl,rfl⟩

variable (C : Chart (wordBits z (2^v.W) copies)
    (catalogue F (v.configured (v.seed P z width)) v.cost).alphabet (v.stripPorts (Stages z (2^v.W))))
  (before : Memory (wordBits z (2^v.W) copies)) (labels : LabelSource) (src : Sources)
  (batch : Batch (catalogue F (v.configured (v.seed P z width)) v.cost).alphabet (v.stripPorts (Stages z (2^v.W))))

set_option cleanup.letToHave false in
/-- The observed seeded stock-copy address bound and the fixed public catalogue
suffice for every field in the real outer row decoder. -/
theorem payload_size_room (phase trial incoming : ℕ) (late : v.stripHeight≤z) (payload : width≤2^z)
    (ready : Calendar.ready C (.attempt (.outer phase trial)) before)
    (installed : C.commit (.outer phase trial)=pricedSegment (build F s (.outer phase trial) incoming).pricedArea src labels bits batch) :
    StripSizes.Room (v.payloadRaw P z width phase trial incoming) (payloadChannels z N k).slot
      ((s).outer phase trial).start D (Fintype.card (v.payloadPacketMenu N).index) (v.payloadMaximum N) bits := by
  let addr := resolvedStock v.mesh (v.privateArena P z width) P.joint.initial (build F s) (.outer phase trial)
  have fields := payload_fields v z s phase trial incoming addr
  have dims := v.ordinary_dimensions P z width (.outer phase trial)
  have bank := priced_bank_fit C _ before _ src labels batch ready installed
  exact StripSizes.Room.of_scalars _ _ (v.strip_scalar_room P z width late payload) (le_max_left ..) (le_max_left ..)
    (v.menu_caps z).1 (fields.1.trans dims.2) (fields.2.1.trans dims.1) (fields.2.2.trans_lt bank)

set_option cleanup.letToHave false in
/-- The same copy count and alphabet are mounted at every purchased tick; the
charged seed pass gives its own address bound at its own incoming shelf. -/
theorem purchased_size_room (phase trial layer tick incoming : ℕ) (late : v.stripHeight≤z) (payload : width≤2^z)
    (ready : Calendar.ready C (.attempt (.inner phase trial layer tick)) before)
    (installed : C.commit (.inner phase trial layer tick)=pricedSegment
      (build F s (.inner phase trial layer tick) incoming).pricedArea src labels bits batch) :
    StripSizes.Room (v.purchaseRaw P z width phase trial layer tick incoming)
      (purchasedChannels (z:=z) (d:=2^v.W) (k:=k) ((s).outer phase trial).market.shelf (s).sampler v.depth
        ((s).stratumHeader phase trial)).slot ((s).inner phase trial layer tick).start D
      (Fintype.card v.purchasePacketMenu.index) v.purchaseMaximum bits := by
  let addr := resolvedStock v.mesh (v.privateArena P z width) P.joint.initial (build F s) (.inner phase trial layer tick)
  have fields := purchase_fields v z s phase trial layer tick incoming addr
  have dims := v.ordinary_dimensions P z width (.inner phase trial layer tick)
  have bank := priced_bank_fit C _ before _ src labels batch ready installed
  exact StripSizes.Room.of_scalars _ _ (v.strip_scalar_room P z width late payload) (le_max_right ..) (le_max_right ..)
    (v.menu_caps z).2 (fields.1.trans dims.2) (fields.2.1.trans dims.1) (fields.2.2.trans_lt bank)

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
