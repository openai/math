import OAI.Hierarchy.ProbeFixedWideCountedPrefix
import OAI.Hierarchy.ProbeFixedWideFundedSpace
import OAI.Hierarchy.ProbeFixedWidePaidTotal

namespace OAI
/-! # One genuine funded paid CPU, uniformly over admissible wide parents -/
noncomputable section
set_option quotPrecheck false
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage CoreBoard CoreRoute ReportSockets
open CatalystArchive StripChart CatalogueRows ColumnWires
open ThreeFlat.RAM PhysicalProcedure
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
  (max (Fintype.card (PayloadRole N k)) (Fintype.card (PurchasedRole v.depth k)))*2^h



open CoreBoard.HistoryRoles CoreBoard.HistoryRoles.RoleProgram
local notation "directory" => WideMemory.dir h v.W k v.wideJobs
local notation "rows" => (P).catalogue.rows
local notation "order" => v.wideOrder h width
local notation "sizes" => RoleRoom.shape (R:=WideMemory.R v.sampler h v.W k) v.sampler directory rows
local notation "sheet" => v.wideSignedPage h width


local notation "stock" => v.fixedTerminalStock P h width
local notation "page" => v.wideSignedPage h width stock
local notation "old" => TerminalLayout.settlement page stock
local notation "original" => TerminalLayout.reserve start cnt page
local notation "L" => ownerLedger s v.mesh (P).catalogue (P).routes F (TerminalLayout.ownerArea page stride)
local notation "sink" => (P).catalogue.sink r old (TerminalLayout.source page) (TerminalLayout.table page)
  (TerminalLayout.destination page) (sinkBank start cnt r rows)
local notation "C" => v.wideSignedChart h width stock
local notation "last" => (events v.mesh).length
local notation "g" => CoreRoute.source v.sampler h v.W k v.wideJobs v.depth (WideMemory.K h v.W) (directory).groups
  (WideMemory.H h v.W k v.wideJobs) (WideMemory.R v.sampler h v.W k)
local notation "routes" => stages old (routeBanks start cnt r) g v.sampler h v.W k v.wideJobs
local notation "supply" => fuel v.mesh*width


local notation "own" => TerminalLayout.ownerArea page stride
local notation "incoming" => resolvedStock v.mesh A (P).joint.initial (build F (withPorts s v.mesh (P).catalogue (P).routes))
local notation "pay" => cashWidthBase F s v.mesh (P).catalogue (P).routes incoming
local notation "market" => v.catalystMarkets P h width
local notation "o" => wideRouteOrder h D k



open Filter
variable (bits : ℕ)
local notation "ss" => v.widePaidSlices h width bits
local notation "full" => v.wideFundedSize h width bits
local notation "mx" => 2^page

structure CountedReady : Prop where
  height : v.wideFundedHeight≤h
  credit : v.keepLimit*width+1≤2^h
  size_le : width≤2^h
  lengths : ∀t∈ss,t.count≤ mx
  ceiling : v.wideScanEnd h width ss mx<2^w
  totals : ∀size,full ≤ size → ∀(π : Equiv.Perm (Fin (2^h))) (raw : Boot.Tape h D),
    let checkpoint:=v.wideSignedCheckoutAt h width size stock v.radius π o (v.wideFundedRaw h width bits raw)
    checkpoint ((A).endAddress v.mesh)=0 → ∀e : Fin (P).catalogue.rows,PaidWidths.total ss checkpoint e<2^w

/-- The parent geometry and single honest checked-revenue calculation provide every
numerical hypothesis. Only the original admission flag and original finite extent
are supplied at use. -/
theorem cofinal_counted_ready {κ B : ℝ} :
    ∃ K : ℕ,∀ᶠ x : Tagged.WideParent κ B in Tagged.WideParent.large κ B,
      let arena:=v.widePlacement x.h x.w
      let base:=v.fixedTerminalStock arena x.h x.w
      let scanCap:=2^v.wideSignedPage x.h x.w base
      CountedReady v x.h x.w bits ∧ v.wideScanEnd x.h x.w (v.widePaidSlices x.h x.w bits) scanCap≤K*2^x.h := by
  obtain ⟨K,space⟩:=v.cofinal_funded_scan (κ:=κ) (X:=B)
  have grows : Tendsto (Tagged.WideParent.h (κ:=κ) («A»:=B)) (Tagged.WideParent.large κ B) atTop:=tendsto_comap
  refine ⟨K,?_⟩
  filter_upwards [space,v.cofinal_paid_total_fits (κ:=κ) (B:=B) bits,
    grows.eventually (eventually_ge_atTop v.wideFundedHeight),
    Tagged.WideParent.fixed_mul_width (κ:=κ) («A»:=B) v.keepLimit,
    Tagged.WideParent.fixed_mul_width (κ:=κ) («A»:=B) 1] with x report total height funded small
  let h:=x.h
  let width:=x.w
  intro arena base scanCap
  obtain ⟨lengths,volume,upper⟩:=report bits
  refine ⟨⟨height,funded,by simpa using (Nat.le_of_lt (show 1*x.w<2^x.h from small)),lengths,upper,?_⟩,volume⟩
  intro size extent π raw checkpoint accepted
  exact total size ((v.wide_funded_extent h width bits).trans extent) π (v.wideFundedRaw h width bits raw) accepted

/-- Choose all CPU code and global cutoffs first. Only the parent tag, signed selector
bits and the truth of the original gate are supplied to the execution theorem. -/
abbrev CountedReady.execute (ready : CountedReady v h width bits) (size : ℕ) (extent : full ≤ size)
    (π : Equiv.Perm (Fin (2^h))) (raw : Boot.Tape h D) (state : Word w)
    (accepted : v.wideSignedCheckoutAt h width size stock v.radius π o (v.wideFundedRaw h width bits raw)
      ((A).endAddress v.mesh)=0) :=
  v.wide_counted_prefix_at h width size v.radius π raw bits extent ready.height ready.credit ready.size_le
    state mx ready.ceiling ready.lengths (ready.totals size extent π raw accepted)

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
