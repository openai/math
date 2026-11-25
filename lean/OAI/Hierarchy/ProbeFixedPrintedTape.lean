import OAI.Hierarchy.ProbeFixedPrintedOperands
import OAI.Hierarchy.ProbeFixedFailureEconomy
import OAI.Hierarchy.ProbeFixedNativeStrips

namespace OAI
/-! # The actual selected failure tape assigns computed geometric prices to cash roles -/

noncomputable section
set_option quotPrecheck false
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage ProbeStage.Native CoreBoard
open StripChart StripDirectory CatalogueRows StockCommit PurchaseStage PortPadding CatalystArchive
open ThreeFlat.RAM
open scoped Classical Fin.CommRing
attribute [local irreducible] permutationFabric
variable {F : Type*} [Field F] {k : ℕ} [Nonempty (Fin k)] {p q Q σ Λ : ℝ}
  (v : FixedProtocolFormat F k p q Q σ Λ) (P : v.Placement) (z width r : ℕ)
  (banks : RouteSettlement.Banks) (src tab dst : ℕ) (owners : Bank)
local notation "N" => Stages z (2^v.W)
local notation "W" => wordBits z (2^v.W) copies
local notation "n₀" => Fintype.card (PayloadRole N k)
local notation "n₁" => Fintype.card (PurchasedRole v.depth k)
local notation "D" => max n₀ n₁
local notation "C" => v.nativeChart P z width r banks src tab dst owners
local notation "board" => P.catalogue
local notation "fmt" => v.nativeFormats P z width
local notation "g" => v.stamp P z width r banks src tab dst owners
local notation "H" => StripChart.header F (v.nativeBoards P z width)

omit [Nonempty (Fin k)] in
private theorem cash_id {A B U V I : Type*} (idx : A→I) (r : ColumnWires.Role U V (A⊕B) k)
    (cash : ColumnWires.account idx r=none) : ColumnWires.account _root_.id r=none := by
  cases r with
  | extra t => cases t <;> simp_all [ColumnWires.account]
  | catalyst | radius | horizontal | cross => rfl

/-- The reported link address reads the same word after the two pricing preambles. -/
private theorem printed_weight {bits letters fields : ℕ}
    (area : StockCommit.Area) (sources : StockCommit.Sources) (labels : StockCommit.LabelSource)
    (batch : Batch letters fields) (prior : Memory bits)
    (plan : PortPlan (fresh area sources) batch (stageInput area sources labels prior) area.rows)
    (mounted : ((fresh area sources).native bits area.rows batch).ready (stageInput area sources labels prior))
    (bcast : BroadcastRoom (fresh area sources) batch area.rows bits)
    (purchase : PurchaseStage.Repair letters fields) (routes : Fin area.goods → ℕ)
    (charge : Fin area.occurrences → ℕ → ℝ) (tree : Fin area.rows → ℕ → ℝ)
    (e : Fin area.occurrences) :
    ((fresh area sources).tape batch (stageInput area sources labels prior) plan mounted bcast
      (reportedKeys area labels purchase routes) charge tree).weight e =
      charge e (((pricedSegment area sources labels bits batch).after prior) (labels.out + e.val)).val := by
  change charge e ((((fresh area sources).native bits area.rows batch).after
    (stageInput area sources labels prior)) (labels.out + e.val)).val = _
  exact congrArg (fun state : Memory bits => charge e (state (labels.out + e.val)).val)
    (priced_after area sources labels batch prior).symm

open ColumnWires CatalystArchive LinearAlgebra.SpectralBooks.ChordGraph in
/-- Port-plan transport keeps the native row-major ordinal of every strip occurrence. -/
private theorem compiled_role_ordinal
    {α β ι η K : Type*} [Fintype α] [Fintype β] [Fintype ι] [Fintype η] [Field K]
    {axes sites stages machineWidth height dimension terms ports : ℕ}
    [Nonempty (Fin sites)] [Nonempty (Fin axes)] [Nonempty (Role ι η (α ⊕ β) axes)]
    {cost tolerance tree : ℝ} {length : η → ℝ} {capacity : α → ℝ}
    {edge : Role ι η (α ⊕ β) axes → Chord sites}
    {menu : Probe.FixedMenu K edge
      (demand (I:=ι) («H»:=η) (k:=axes) (Sum.inl (α:=α) (β:=β)))
      ((fun y : α → ℝ => quote (I:=ι) (k:=axes) cost length (LocalCommodity.extraPrice (B:=β) y)) ''
        Set.Icc 0 capacity) tolerance tree stages}
    (x : CatalystArchive.StripInput (A:=α) (B:=β) («C»:=ι) («H»:=η) (k:=axes)
      menu machineWidth height dimension terms ports)
    (nativeForm : Format height dimension axes terms ports) (batch : Batch terms ports) (tape : Memory machineWidth)
    (formatEq : x.form=nativeForm) (batchEq : x.ballot=batch) (tapeEq : x.mem=tape)
    (row : Fin nativeForm.market.rows) (field : Fin ports) :
    ((x.alignedPlan nativeForm batch tape formatEq batchEq tapeEq).enum ⟨row,field⟩).val =
      field.val + ports * row.val := by
  subst nativeForm batch tape
  rfl

/-- A price read at the installed port agrees with the bill at its physical header index. -/
private theorem price_at_coordinate {first indexed quoted printed : ℝ}
    (same : first = indexed) (read : indexed = quoted) (paid : quoted = printed) :
    first = printed :=
  same.trans (read.trans paid)

omit [Nonempty (Fin k)] in
/-- The installed header uses the same row-major enumeration as the funded format. -/
private theorem printed_role_ordinal (a : Attempt) (row : Fin (H a).rows) (field : Fin D) :
    (v.roleOccurrence P z width a row field).val = field.val + D * row.val := rfl

section
set_option maxRecDepth 4096
set_option maxHeartbeats 2500000
variable (phase trial : ℕ) (entry : Memory (wordBits z (2^v.W) copies))
local notation "ev" => (Attempt.outer phase trial)
local notation "post" => postOutput ((C).layout ev) (repair C ev) (prepared C ev entry)
variable (fitted : v.payloadStageSizes P z width r banks src tab dst owners phase trial entry)
local notation "π" => v.payloadStage_compile P z width r banks src tab dst owners phase trial entry fitted
variable (layout : StockBound.TrialLayout (v.nativeChart P z width r banks src tab dst owners) (.outer phase trial)
  (v.nativeFormats P z width (.outer phase trial)).pricedArea (v.nativeFormats P z width (.outer phase trial)).stockSource
  (v.stamp P z width r banks src tab dst owners (.outer phase trial)) v.keepLimit width
  ((v.privateArena P z width).base v.mesh (.attempt (.outer phase trial))))
  (live : Calendar.ready (v.nativeChart P z width r banks src tab dst owners) (.attempt (.outer phase trial)) entry)
local notation "T" => v.selectedTape P z width r banks src tab dst owners ev entry layout live π

/-- The actual payload plan and the pricing program refer to the same header occurrence. -/
private theorem payload_plan_coordinate (row : Fin (H ev).rows) (field : Fin D) :
    ((π).enum ⟨row,field⟩) = v.roleOccurrence P z width ev row field := by
  apply Fin.ext
  refine Eq.trans ?_ (printed_role_ordinal v P z width ev row field).symm
  dsimp only [payloadStage_compile, taskCommit]
  exact compiled_role_ordinal (α := PayloadStrip.Quotes N k) (β := Empty)
    (ι := PayloadStrip.Columns N) (η := Fin (PayloadStrip.edgeCount N)) (K := F)
    (axes := k) (machineWidth := W) (height := z) (dimension := 2^v.W) (ports := D)
    (v.payloadStageInput P z width r banks src tab dst owners phase trial entry fitted) (fmt ev)
    (v.ballot P z width r banks src tab dst owners ev) (v.stage P z width r banks src tab dst owners ev entry)
    (v.payloadStage_format P z width r banks src tab dst owners phase trial entry fitted)
    (v.payloadStage_ballot P z width r banks src tab dst owners phase trial entry fitted)
    (v.payloadStage_memory P z width r banks src tab dst owners phase trial entry fitted) row field

/-- The payload cash term in the selected-row quote is the word in the
actual native signed-tape row after pricing, seeding and committing it. -/
theorem payload_printed_tape (row : Fin (H ev).rows) (idx : PayloadStrip.Quotes N k→Fin (fmt ev).coordinates)
    (headBefore : (H ev).stop≤(g ev).out) (room : (board).rows<2^W) (wide : 0<W)
    (order : Fin (board).coreRows≃Edges v.sampler z (2^v.W) k)
    (loaded : CoreLookup.Loaded P.routes.core order post)
    (codes : ∀f,(board).core.lengthCode.eval post ((order.symm f).val:Word W)=(coreCode v.sampler v.radius f:Word W))
    (fits : ∀f : Edges v.sampler z (2^v.W) k,coreCode v.sampler v.radius f<2^W)
    (global : PayloadStrip.Columns N → Columns z (2^v.W))
    (columns : ∀c,(((v.payloadPricePorts P z width).column c).eval post (row.val:Word W)).val=((Fintype.equivFin _) (global c)).val)
    (horizontal : ∀e l,∃f : Edges v.sampler z (2^v.W) k,
      ((v.payloadPricePorts P z width).horizontal e l).eval post (row.val:Word W)=((order.symm f).val:Word W) ∧
      (coreCode v.sampler v.radius f:ℝ)=PayloadStrip.length N e)
    (role : PayloadRole N k) (cash : ColumnWires.account idx role=none) :
    (T).weight ((π).enum ⟨row,inject (Nat.le_max_left n₀ n₁) ((Fintype.equivFin _) role)⟩)=
      ColumnWires.printed v.radius (PayloadStrip.length N) role := by
  have archived : (H ev).Loaded (v.stage P z width r banks src tab dst owners ev entry):=fitted.loaded
  have pre : (H ev).Loaded post:=archived.frame (fun addr _ high=>
    (stage_frame (fmt ev).pricedArea (fmt ev).stockSource (g ev) post addr (high.trans_le headBefore)
      (Nat.le_add_right _ _)).symm)
  have actual:=v.payload_printed P z width phase trial row post (v.ballot P z width r banks src tab dst owners ev)
    pre fitted.portFit room wide order loaded codes fits global columns horizontal role (cash_id idx role cash)
    live.2.2.2.2.2.2.2.2.2.2.1
  let field : Fin D := inject (Nat.le_max_left n₀ n₁) ((Fintype.equivFin _) role)
  let occurrence : Fin (fmt ev).pricedArea.occurrences := v.roleOccurrence P z width ev row field
  let quoteAt (e : Fin (fmt ev).pricedArea.occurrences) : ℝ :=
    v.printedCharge P z width ev e
      (((pricedSegment (fmt ev).pricedArea (fmt ev).stockSource (g ev) W
        (v.ballot P z width r banks src tab dst owners ev)).after post) ((g ev).out + e.val)).val
  have weighted (e : Fin (fmt ev).pricedArea.occurrences) : (T).weight e = quoteAt e :=
    printed_weight (fmt ev).pricedArea (fmt ev).stockSource (g ev)
      (v.ballot P z width r banks src tab dst owners ev) post π
      (v.entered P z width r banks src tab dst owners ev entry live)
      (fresh_broadcastRoom (fmt ev).pricedArea (fmt ev).stockSource
        (v.ballot P z width r banks src tab dst owners ev) layout.inputs layout.window.room)
      (repair C ev) (fun _ => 0) (v.printedCharge P z width ev)
      (fun _ _ => v.cost.atAttempt ev) e
  have coordinate := payload_plan_coordinate v P z width r banks src tab dst owners phase trial
    entry fitted row field
  have charged : quoteAt occurrence = ColumnWires.printed v.radius (PayloadStrip.length N) role := by
    dsimp only [quoteAt, occurrence, field, stamp, Format.labelSource, CatalogueRows.Board.sink]
    exact actual
  refine price_at_coordinate ?_ (weighted occurrence) charged
  first
  | exact congrArg (T).weight coordinate
end

section
set_option maxRecDepth 4096
set_option maxHeartbeats 2500000
variable (phase trial j t : ℕ) (entry : Memory (wordBits z (2^v.W) copies))
local notation "ev" => (Attempt.inner phase trial j t)
local notation "post" => postOutput ((C).layout ev) (repair C ev) (prepared C ev entry)
variable (fitted : v.purchasedStageSizes P z width r banks src tab dst owners phase trial j t entry)
local notation "π" => v.purchasedStage_compile P z width r banks src tab dst owners phase trial j t entry fitted
variable (layout : StockBound.TrialLayout (v.nativeChart P z width r banks src tab dst owners) (.inner phase trial j t)
  (v.nativeFormats P z width (.inner phase trial j t)).pricedArea (v.nativeFormats P z width (.inner phase trial j t)).stockSource
  (v.stamp P z width r banks src tab dst owners (.inner phase trial j t)) v.keepLimit width
  ((v.privateArena P z width).base v.mesh (.attempt (.inner phase trial j t))))
  (live : Calendar.ready (v.nativeChart P z width r banks src tab dst owners) (.attempt (.inner phase trial j t)) entry)
local notation "T" => v.selectedTape P z width r banks src tab dst owners ev entry layout live π

/-- The actual purchased plan and the pricing program refer to the same header occurrence. -/
private theorem purchased_plan_coordinate (row : Fin (H ev).rows) (field : Fin D) :
    ((π).enum ⟨row,field⟩) = v.roleOccurrence P z width ev row field := by
  apply Fin.ext
  refine Eq.trans ?_ (printed_role_ordinal v P z width ev row field).symm
  dsimp only [purchasedStage_compile, taskCommit]
  exact compiled_role_ordinal (α := ChainStrip.Axes v.depth k) (β := Unit)
    (ι := ChainStrip.Columns v.depth) (η := Fin (ChainStrip.edgeCount v.depth)) (K := F)
    (axes := k) (machineWidth := W) (height := z) (dimension := 2^v.W) (ports := D)
    (v.purchasedStageInput P z width r banks src tab dst owners phase trial j t entry fitted) (fmt ev)
    (v.ballot P z width r banks src tab dst owners ev) (v.stage P z width r banks src tab dst owners ev entry)
    (v.purchasedStage_format P z width r banks src tab dst owners phase trial j t entry fitted)
    (v.purchasedStage_ballot P z width r banks src tab dst owners phase trial j t entry fitted)
    (v.purchasedStage_memory P z width r banks src tab dst owners phase trial j t entry fitted) row field

/-- The purchased cash term in the selected-row quote is the word in the
actual native signed-tape row after pricing, seeding and committing it. -/
theorem purchased_printed_tape (row : Fin (H ev).rows) (idx : ChainStrip.Axes v.depth k→Fin (fmt ev).coordinates)
    (headBefore : (H ev).stop≤(g ev).out) (room : (board).rows<2^W) (wide : 0<W)
    (order : Fin (board).coreRows≃Edges v.sampler z (2^v.W) k)
    (loaded : CoreLookup.Loaded P.routes.core order post)
    (codes : ∀f,(board).core.lengthCode.eval post ((order.symm f).val:Word W)=(coreCode v.sampler v.radius f:Word W))
    (fits : ∀f : Edges v.sampler z (2^v.W) k,coreCode v.sampler v.radius f<2^W)
    (global : ChainStrip.Columns v.depth → Columns z (2^v.W))
    (columns : ∀c,(((v.purchasedPricePorts P z width phase trial).column c).eval post (row.val:Word W)).val=((Fintype.equivFin _) (global c)).val)
    (horizontal : ∀e l,∃f : Edges v.sampler z (2^v.W) k,
      ((v.purchasedPricePorts P z width phase trial).horizontal e l).eval post (row.val:Word W)=((order.symm f).val:Word W) ∧
      (coreCode v.sampler v.radius f:ℝ)=ChainStrip.length v.depth e)
    (birth : (board).coreRows≤(((v.purchasedPricePorts P z width phase trial).probe ()).eval post (row.val:Word W)).val)
    (role : PurchasedRole v.depth k) (cash : ColumnWires.account idx role=none) :
    (T).weight ((π).enum ⟨row,inject (Nat.le_max_right n₀ n₁) ((Fintype.equivFin _) role)⟩)=
      ColumnWires.printed v.radius (ChainStrip.length v.depth) role := by
  have archived : (H ev).Loaded (v.stage P z width r banks src tab dst owners ev entry):=fitted.loaded
  have pre : (H ev).Loaded post:=archived.frame (fun addr _ high=>
    (stage_frame (fmt ev).pricedArea (fmt ev).stockSource (g ev) post addr (high.trans_le headBefore)
      (Nat.le_add_right _ _)).symm)
  have actual:=v.purchased_printed P z width phase trial j t row post (v.ballot P z width r banks src tab dst owners ev)
    pre fitted.portFit room wide order loaded codes fits global columns horizontal birth role (cash_id idx role cash)
    live.2.2.2.2.2.2.2.2.2.2.1
  let field : Fin D := inject (Nat.le_max_right n₀ n₁) ((Fintype.equivFin _) role)
  let occurrence : Fin (fmt ev).pricedArea.occurrences := v.roleOccurrence P z width ev row field
  let quoteAt (e : Fin (fmt ev).pricedArea.occurrences) : ℝ :=
    v.printedCharge P z width ev e
      (((pricedSegment (fmt ev).pricedArea (fmt ev).stockSource (g ev) W
        (v.ballot P z width r banks src tab dst owners ev)).after post) ((g ev).out + e.val)).val
  have weighted (e : Fin (fmt ev).pricedArea.occurrences) : (T).weight e = quoteAt e :=
    printed_weight (fmt ev).pricedArea (fmt ev).stockSource (g ev)
      (v.ballot P z width r banks src tab dst owners ev) post π
      (v.entered P z width r banks src tab dst owners ev entry live)
      (fresh_broadcastRoom (fmt ev).pricedArea (fmt ev).stockSource
        (v.ballot P z width r banks src tab dst owners ev) layout.inputs layout.window.room)
      (repair C ev) (fun _ => 0) (v.printedCharge P z width ev)
      (fun _ _ => v.cost.atAttempt ev) e
  have coordinate := purchased_plan_coordinate v P z width r banks src tab dst owners phase trial j t
    entry fitted row field
  have charged : quoteAt occurrence = ColumnWires.printed v.radius (ChainStrip.length v.depth) role := by
    dsimp only [quoteAt, occurrence, field, stamp, Format.labelSource, CatalogueRows.Board.sink]
    exact actual
  refine price_at_coordinate ?_ (weighted occurrence) charged
  first
  | exact congrArg (T).weight coordinate
end

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
