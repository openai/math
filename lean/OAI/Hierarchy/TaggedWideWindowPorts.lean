import OAI.Hierarchy.TaggedWideWindowSlotRead
import OAI.Hierarchy.ProbeFixedWideDated
import OAI.Hierarchy.TaggedWireWidePaidCoordinates
import OAI.Hierarchy.TaggedWireDatedResolved
import OAI.Hierarchy.TaggedWireAlignedSlots

namespace OAI
/-! # Original physical ports in the scaled endpoint pages of the funded dated run -/

noncomputable section
set_option quotPrecheck false
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage CoreBoard CoreRoute ReportSockets
open CoreBoard.HistoryRoles CoreBoard.HistoryRoles.RoleProgram
open ThreeFlat.RAM PhysicalProcedure
open CatalystArchive StripChart CatalogueRows ColumnWires StripDirectory PurchaseFrozen WireTelescope ProtocolRAMEmit ProtocolRAMReportedPorts
open TaggedShorterBudget TaggedShorterSupergroups
open scoped Classical Fin.CommRing
variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)
  (h width : ℕ)
local notation "P" => v.widePlacement h width
local notation "boards" => v.nativeBoards P h width
local notation "A" => v.privateArena P h width
local notation "E" => v.publicHeader P h width
local notation "D" => 2^v.W
local notation "N" => Stages h D
local notation "r" => Fintype.card (Slots h D k)
local notation "num" => Fintype.card (Columns h D)*k
local notation "w" => Native.wordBits h D Native.copies
local notation "start" => v.catalystStaticStart P h width
local notation "decl" => declaredRows v.mesh (ownerLedger boards v.mesh (P).catalogue (P).routes F A)
local notation "cnt" => rowOnlyCount v.mesh decl
local notation "stride" => ownerRowFactor D k v.sampler.degree v.depth
  (max (Fintype.card (PayloadRole N k)) (Fintype.card (PurchasedRole v.depth k)))*2^h



open CoreBoard.HistoryRoles CoreBoard.HistoryRoles.RoleProgram
local notation "directory" => WideMemory.dir h v.W k v.wideJobs
local notation "rows" => (P).catalogue.rows
local notation "order" => v.wideOrder h width


local notation "stock" => v.fixedTerminalStock P h width
local notation "page" => v.wideSignedPage h width stock
local notation "old" => TerminalLayout.settlement page stock
local notation "original" => TerminalLayout.reserve start cnt page
local notation "L" => ownerLedger boards v.mesh (P).catalogue (P).routes F (TerminalLayout.ownerArea page stride)
local notation "sink" => (P).catalogue.sink r old (TerminalLayout.source page) (TerminalLayout.table page)
  (TerminalLayout.destination page) (sinkBank start cnt r rows)
local notation "C" => v.wideSignedChart h width stock
local notation "g" => CoreRoute.source v.sampler h v.W k v.wideJobs v.depth (WideMemory.K h v.W) (directory).groups
  (WideMemory.H h v.W k v.wideJobs) (WideMemory.R v.sampler h v.W k)
local notation "routes" => CoreRoute.stages old (routeBanks start cnt r) g v.sampler h v.W k v.wideJobs
local notation "supply" => fuel v.mesh*width


local notation "o" => wideRouteOrder h D k


variable (size M : ℕ) (π : Equiv.Perm (Fin (2^h))) (raw : Boot.Tape h (2^v.W))
local notation "bits" => v.maxBits
local notation "ss" => v.widePaidSlices h width bits
local notation "seed" => v.wideFundedRaw h width bits raw
local notation "mid" => v.wideSignedMidAt h width size stock M π o seed
local notation "chk" => v.wideSignedCheckoutAt h width size stock M π o seed
local notation "hi" => v.wideRoleStart h width stock ss
local notation "full" => v.wideFundedSize h width bits

local notation "K" => WideMemory.K h v.W
local notation "H" => WideMemory.H h v.W k v.wideJobs
local notation "R" => WideMemory.R v.sampler h v.W k
local notation "pub" => BoughtSockets.Public.join (v.wideSources h width).2 v.sampler h v.W k v.depth K (directory).groups H R
local notation "coreTop" => CoreCatalogue.top h v.W K (directory).groups H R
local notation "coreHead" => CoreCatalogue.headBase h v.W K (directory).groups H

local notation "place" => siteNumber h D k
local notation "mount" => (P).catalogue.coreMount π place order chk
local notation "ord" => CoreRoute.enum mount o
local notation "ci" => fun i : Commodity (Fin (2^h)) N k=>PurchaseInventory.slot i
local notation "lw" => v.wideWidthLayout h width ss

variable (horizon : v.wideFundedSize h width v.maxBits ≤ size) (age : v.wideFundedHeight≤h)
  (budget : v.keepLimit*width+1≤2^h) (small : width≤2^h) (operandAge : v.wideOperandHeight≤h)
  {entries : ℕ} (card : entries = rowOnlyCount v.mesh (declaredRows v.mesh
    (ownerLedger (v.nativeBoards (v.widePlacement h width) h width) v.mesh
      (v.widePlacement h width).catalogue (v.widePlacement h width).routes F
      (v.privateArena (v.widePlacement h width) h width))))
  (who : Fin entries→Fin (Fintype.card (Columns h (2^v.W))*k))
  (dur : Fin entries→ℕ)
  (cj : Columns h (2^v.W)×Fin k→Fin (Fintype.card (Columns h (2^v.W))*k))
local notation "archive" => result routes (result ((L).scans v.mesh num) (PaidWidths.output (old).width rows
  (TerminalLayout.source page) ss chk))
local notation "closed" => ReserveUse.output original old supply who dur archive
local notation "settled" => (sink).output closed ord ci (fun j=>(cj j).val)
local notation "rawRow" => (sink).terminalRows closed ord ci (fun j=>(cj j).val)
local notation "counts" => fun e : Fin rows=>(rawRow e).width
variable (marks : Marks h v.W k v.wideJobs) (unique : Exclusive marks)

private abbrev windowCatalogueAlignment :=
  Alignment (P).catalogue v.sampler π v.depth marks M rawRow counts
    ((P).catalogue.original v.sampler π v.depth marks order (v.wideBoughtOrdinal h width π marks))

variable (A₀ : windowCatalogueAlignment v h width size M π raw who dur cj marks)

local notation "z" => RoleRoom.shape («R»:=R) v.sampler directory rows
local notation "head" => CoreCatalogue.headBase h v.W K ((directory).groups) H
local notation "free" => (z).free hi
local notation "super" => CoreCatalogue.superStart h v.W
local notation "ptr" => CoreCatalogue.pointBits h v.W
local notation "corePort" => coreInputs head free R ptr super K k v.wideJobs
local notation "boughtPort" => boughtInputs pub v.sampler h v.W k v.depth K
local notation "acquired" => v.wideBoughtOrdinal h width π marks
local notation "stage" => (fun _ : Fin rows=>0)
local notation "oldRows" => Tagged.WideStack.atScale ((P).catalogue.transport order) stage 0 rawRow
local notation "Live" => {i : Fin rows // 0<pieces oldRows width i}
variable (ell unitCost work : ℕ) (positive : 0<width)
local notation "anc" => (Alignment.location v.sampler π v.depth marks unique (P).catalogue order acquired
  rawRow A₀ stage 0 width positive).trans (ReportSockets.packed directory)
local notation "B" => v.wideDated h width ell unitCost

/-- The original core-port and bought-port input operands, including both
arms of the resolved physical orientation, fit before the pair of scans. -/
theorem wideWindow_ordered_fits (target : ℕ) (above : full≤target)
    (stop : target<2^w) (side : Bool) : ((B).orderedSlot side).Fits w target := by
  have fullFit : (z).ceiling hi<2^w := above.trans_lt stop
  have targetLow : (A).endAddress v.mesh≤target :=
    (v.wide_funded_extent h width bits).trans above
  let src:=v.wide_catalogue_sources h width old (TerminalLayout.source page) (TerminalLayout.table page)
    (TerminalLayout.destination page) (sinkBank start cnt r rows) (targetLow.trans_lt stop)
  have lift (e : Expr) := ProtocolRAMGeneratedWrite.fits_mono («w»:=w) e targetLow
  obtain ⟨⟨c₁,c₂,c₃,c₄,c₅⟩,⟨b₁,b₂,b₃,b₄,b₅⟩⟩:=src
  have fits (s : Bool) : (v.widePaidPorts h width hi s).Fits w target :=
    RoleRoom.catalogue_fits z (P).catalogue pub v.sampler h v.W k v.depth K ((directory).groups) H
      head R ptr (CoreCatalogue.siteBase h v.W K) super hi
      ⟨lift _ c₁,lift _ c₂,lift _ c₃,lift _ c₄,lift _ c₅⟩
      ⟨lift _ b₁,lift _ b₂,lift _ b₃,lift _ b₄,lift _ b₅⟩ rfl above fullFit s
  have safe (s : Bool) := (RoleRoom.socket_fits z _ (fits s) above fullFit).1
  change (sortedRead _ _ side _ _).Fits w target
  cases side <;> exact ⟨safe false,safe true,(fits _).slot,(fits _).slot⟩

include horizon age budget small operandAge card in
/-- On the authentic prefix after settlement the two ordered slot operands
equal the two packed column anchors of every positive masked original row. -/
theorem wideWindow_literal_ports (m : Memory w) (keep : ∀a,a<full→m a=settled a)
    (highFit : full<2^w) (i : Live) (side : Bool) :
    ((B).orderedSlot side).eval m (i.val.val:Word w)=((anc (i,side)).2.val:Word w) := by
  have inputs:=v.wide_funded_turn_inputs h width size M π raw bits horizon age budget small (entries:=entries) card who dur
    (I:=Commodity (Fin (2^h)) N k) (J:=Columns h D × Fin k)
    (core:=(mount).ordinary) (center:=(mount).centers) ord ci (fun t=>(cj t).val) m keep
  have seen:=inputs.2.2.2.1
  have capacity:=v.wide_signed_room h width stock (v.fixedTerminalStock_end P h width)
    ((le_max_left ..).trans age) budget
  have sizes:=v.wide_operand_room h width operandAge capacity.2
  have signed : (z).signedSites≤(z).ceiling hi := by
    simp only [RoleRoom.Sizes.ceiling,RoleRoom.Sizes.stop,RoleRoom.Sizes.offset,RoleRoom.Sizes.positive,
      RoleRoom.Sizes.axis,RoleRoom.Sizes.ext,RoleRoom.Sizes.free,RoleRoom.Sizes.pub]
    omega
  have axes : (siteLast h D k+1)*(2*k)≤2^w:=signed.trans highFit.le
  have factor : 1≤2*k:=by have hk:=v.positive;omega
  have sites : siteLast h D k+1≤2^w :=
    (by simpa only [Nat.mul_one] using Nat.mul_le_mul_left (siteLast h D k+1) factor : _≤_).trans axes
  have rowFit : rows<2^w := by
    have oldFit : (z).old≤(z).ceiling hi := by
      simp only [RoleRoom.Sizes.ceiling,RoleRoom.Sizes.stop,RoleRoom.Sizes.offset,RoleRoom.Sizes.positive,
        RoleRoom.Sizes.axis,RoleRoom.Sizes.ext,RoleRoom.Sizes.free,RoleRoom.Sizes.pub]
      omega
    have count : (z).old=rows+(PurchaseInventory.footprint h N k+num) := v.wide_old_rows h width
    have goods : 0<PurchaseInventory.footprint h N k := by unfold PurchaseInventory.footprint; positivity
    exact (show rows<(z).old from by omega).trans_le (oldFit.trans highFit.le)
  apply Alignment.literal_slot v.sampler π v.depth marks unique (P).catalogue order acquired rawRow A₀
    directory stage 0 width positive ((z).chart hi) m corePort boughtPort sites _ _ i side
  · intro q t
    exact v.wide_resolved_paid h width hi M π marks unique A₀ m inputs.2.2.2.2.1 seen inputs.1 inputs.2.1
      (fun e=>inputs.2.2.2.2.2.1 e.1 _) sizes.1 highFit rowFit sizes.2.1 sizes.2.2.1 sizes.2.2.2 q.val q.property t
  · exact v.wide_paid_coordinates h width hi M π marks unique m inputs.2.2.2.2.1 seen
      (fun e=>inputs.2.2.2.2.2.1 e.1 _) sizes.1 rowFit sizes.2.1 sizes.2.2.1 sizes.2.2.2

include horizon age budget small operandAge card in
/-- Two adjacent native scatter programs install the positive row's scaled
physical port, and the terminal's low-memory frame keeps its original read. -/
theorem wideWindow_ports (m : Memory w) (keep : ∀a,a<full→m a=settled a)
    (above : full≤(B).slotStart work) (room : (B).workEnd work<2^w)
    (port : Bool→Fin rows→Fin H) (pin : ∀j side,(anc (j,side)).2=port side j.val) :
    ∃out,((((B).slotPage work false).code w).seq (((B).slotPage work true).code w)).Exec m out
      (((B).slotPage work false).ticks+((B).slotPage work true).ticks) ∧
      (∀a,a<(B).slotStart work→ out a=m a) ∧ ∀later : Memory w,
      (∀a,a<(B).workEnd work→later a=out a) → ∀side (j : Live),
        (if side then (B).slotBank work true else (B).slotBank work false).read later
          (j.val.val:Word w)=((port side j.val).val*2^ell:ℕ) := by
  have startFit : (B).slotStart work<2^w :=
    (show (B).slotStart work≤(B).workEnd work from Nat.le_add_right ..).trans_lt room
  have literal:=v.wideWindow_literal_ports h width size M π raw horizon age budget small operandAge card
    who dur cj marks unique A₀ ell unitCost positive m keep (above.trans_lt startFit)
  have fits:=v.wideWindow_ordered_fits h width ell unitCost _ above startFit
  obtain ⟨out,exec,frame,reads⟩:=WideCPU.slot_pair_ports B work m fits room
    (fun j : Live=>j.val) (fun side j=>port side j.val) (fun j side=>
      (literal j side).trans (congrArg (fun x : Fin H => (x.val:Word w)) (pin j side)))
  refine ⟨out,exec,frame,?_⟩
  intro later low side j
  cases side <;> exact reads later low _ j

private abbrev windowSettledMemory := settled

variable (m : Memory (Native.wordBits h (2^v.W) Native.copies))
  (keep : ∀a, a < v.wideFundedSize h width v.maxBits →
    m a = windowSettledMemory v h width size M π raw who dur cj a)
local notation "physical" => Alignment.physicalPort (Nat.two_pow_pos _ : 0<H) ((z).chart hi)
  (P).catalogue corePort boughtPort m

include horizon age budget small operandAge card keep in
/-- The total physical port used by the terminal paid barrel agrees on both
sides with the packed socket anchor used to initialize the purchased window. -/
theorem wideWindow_physical_pins (highFit : full<2^w)
    (i : Live) (side : Bool) : (anc (i,side)).2=physical side i.val := by
  have groups : 1≤(directory).groups :=
    (Nat.zero_le _).trans_lt ((anc (i,side)).1.isLt)
  have product : (z).groups*(z).slots≤(z).ceiling hi := by
    simp only [RoleRoom.Sizes.ceiling,RoleRoom.Sizes.stop,RoleRoom.Sizes.offset]
    omega
  have portFit : H≤2^w :=
    (by simpa only [Nat.one_mul] using Nat.mul_le_mul_right H groups : H≤(directory).groups*H).trans
      (product.trans highFit.le)
  apply (Alignment.physicalPort_read (Nat.two_pow_pos _ : 0<H) ((z).chart hi) (P).catalogue
    corePort boughtPort m side i.val _ portFit _).symm
  exact v.wideWindow_literal_ports h width size M π raw horizon age budget small operandAge card
    who dur cj marks unique A₀ 0 0 positive m keep highFit i side

include keep in
/-- The original-numbering port can be taken at the settlement itself. Higher
writes performed by all native dated sheets preserve even its total fallback. -/
theorem wideWindow_physical_before (highFit : full<2^w) (side : Bool) (j : Fin rows) :
    physical side j=Alignment.physicalPort (Nat.two_pow_pos _ : 0<H) ((z).chart hi)
      (P).catalogue corePort boughtPort settled side j := by
  have operand:=v.wideWindow_ordered_fits h width 0 0 full le_rfl highFit side
  have same : (Slot.ordered ((z).chart hi) (P).catalogue corePort boughtPort side).eval m (j.val:Word w)=
      (Slot.ordered ((z).chart hi) (P).catalogue corePort boughtPort side).eval settled (j.val:Word w) :=
    eval_below _ _ settled m operand keep
  unfold Alignment.physicalPort
  rw [same]

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
