import OAI.Hierarchy.ProbeFixedWideReplayArchive
import OAI.Hierarchy.ProtocolRAMCalendarPrefixDebits

namespace OAI
/-! # The true finite paid, reserve and retained-role banks fit their replay prefix -/
noncomputable section
set_option quotPrecheck false
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage CoreBoard CoreRoute ReportSockets
open CatalystArchive StripChart CatalogueRows ColumnWires
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
variable {F : Type} [_root_.Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)
  (h width : ℕ)

section NativePrefix
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
local notation "routes" => CoreRoute.stages old (routeBanks start cnt r) g v.sampler h v.W k v.wideJobs
local notation "supply" => fuel v.mesh*width


variable (slices : List PaidWidths.Slice)
local notation "lw" => v.wideWidthLayout h width slices
local notation "lr" => v.wideReserveLayout h width slices
local notation "replay" => v.wideReplayArchive h width slices

theorem wide_prefix_starts : 28*2^page≤(lw).archive := by
  let high:=v.wideRoleStart h width stock slices
  have htop : 28*2^page ≤ high := (le_max_left ..).trans (le_max_right ..)
  change 28*2^page ≤ (sizes).ceiling high
  refine htop.trans ?_
  simp only [RoleRoom.Sizes.ceiling,RoleRoom.Sizes.stop,RoleRoom.Sizes.offset,
    RoleRoom.Sizes.positive,RoleRoom.Sizes.axis,RoleRoom.Sizes.ext,RoleRoom.Sizes.free,RoleRoom.Sizes.pub]
  omega

theorem wide_prefix_fixtures (room : (lr).scratch<2^w) :
    (replay).kind.Fits w (lw).archive ∧ (replay).pointer.Fits w (lw).archive ∧ (replay).history.Fits w (lw).archive := by
  let B:=2^page
  have adm:=v.wide_prefix_starts h width slices
  have f : TerminalLayout.footprint v.mesh A stock stride rows r num cnt<B := Nat.lt_log2_self
  unfold TerminalLayout.footprint at f
  have emb : (A).first≤(A).endAddress v.mesh:=Nat.le_add_right ..
  have ptrEnd : start+2*2^((2*cnt).log2+1)≤(A).first :=
    (TerminalLayout.static_below start cnt r rows A (v.catalyst_static_end P h width A).le).2
  have high : (lw).archive<2^w := by
    have bound := room
    rw [show (lr).scratch=(lw).archive+(last+1)*(2^(lw).bits+1)+(2*last+2)*(2^((num).log2+1)+1) from
      PrefixWidths.Layout.reserve_scratch ..] at bound
    omega
  have bank (b : Bank) (endAt : b.base+b.size≤(lw).archive) : b.Fits w (lw).archive :=
    ⟨Nat.two_pow_pos _,by omega,endAt⟩
  refine ⟨bank _ ?_,bank _ ?_,bank _ ?_⟩
  · change start+2^((2*cnt).log2+1)≤(lw).archive; omega
  · change start+2^((2*cnt).log2+1)+2^((2*cnt).log2+1)≤(lw).archive; omega
  · change 0+2^(page+2)≤(lw).archive
    rw [pow_add]
    change 0+B*4≤(lw).archive
    omega

theorem wide_prefix_slots (maxRows : ℕ) (bound : (lr).scratch+2*max maxRows cnt<2^w) :
    (old).width.base≤(lw).archive ∧ TerminalLayout.source page≤(lw).scratch ∧
    (∀j≤last,((lw).bank j).base+rows<(lw).scratch) ∧ (lw).scratch+2*maxRows<2^w ∧
    ((lw).bank last).base+rows≤(lr).archive ∧ (∀j≤last,((lr).bank (2*j+1)).base+num≤(replay).scratch) ∧
    (replay).scratch+2*cnt<2^w := by
  have high:=v.wide_prefix_starts h width slices
  have le : (lw).archive≤(lw).scratch := Nat.le_add_right ..
  have small : (lw).scratch≤(lr).scratch := Nat.le_add_right ..
  have ts := le_max_left maxRows cnt
  have ns := le_max_right maxRows cnt
  have axes : num≤2^((num).log2+1) := Nat.lt_log2_self.le
  refine ⟨?_,?_,?_,by omega,PrefixWidths.Layout.reserve_after lw _ last axes,?_,
    by change (lr).scratch+2*cnt<2^w; omega⟩
  · change 1*2^page≤(lw).archive; omega
  · change 9*2^page≤(lw).scratch; omega
  · intro j hj
    exact PrefixWidths.Layout.packed_scratch (v.wideRoleSize h width stock slices) ((rows).log2+1)
      last (show rows≤2^((rows).log2+1) from Nat.lt_log2_self.le) j hj
  · intro j hj
    exact PrefixWidths.Layout.reserve_temporary lw _ last axes hj

end NativePrefix

theorem public_cost {count payload : ℕ} (c : Mesh) (x : Attempt→Entry count payload)
    (s : Attempt→ℕ) (shape : ∀a,(x a).rows=s a) (last : ℕ) :
    PrefixReserve.cost count (PrefixReserve.countAt c x) last=
    PrefixReserve.cost count (PrefixReserve.publicCount c s) last := by
  induction last with
  | zero=>simp only [PrefixReserve.cost,PrefixReserve.public_count_eq c x s shape]
  | succ j ih=>simp only [PrefixReserve.cost,ih,PrefixReserve.public_count_eq c x s shape]

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
