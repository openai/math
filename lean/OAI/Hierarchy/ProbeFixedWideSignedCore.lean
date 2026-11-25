import OAI.Hierarchy.ProbeFixedWideSettlement
import OAI.Hierarchy.ProtocolRAMCatalystTerminalLower
import OAI.Hierarchy.ProtocolRAMCoreRoutePaid

namespace OAI
/-! # The original core catalogue, permutation and directory on the paid terminal output -/

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



/-- The true terminal verdict write and every original calendar event leave the
entire prefix preceding the private calendar intact on the charged master tape. -/
theorem wide_signed_checkout_below (stock : Bank) (M : ℕ) (π : Equiv.Perm (Fin (2^h))) (o : Orders h D k)
    (raw : Boot.Tape h D) (size x : ℕ) (low : x<(A).first)
    (live : Calendar.mounted (v.wideSignedChart h width stock) (events v.mesh)
      (v.wideSignedMidAt h width size stock M π o raw)) :
    v.wideSignedCheckoutAt h width size stock M π o raw x=v.wideSignedMidAt h width size stock M π o raw x := by
  let C:=v.wideSignedChart h width stock
  let m:=v.wideSignedMidAt h width size stock M π o raw
  change checkedOut C ((A).endAddress v.mesh) m x=m x
  have below : x<(A).endAddress v.mesh := low.trans_le (Nat.le_add_right _ _)
  rw [checkedOut,ProtocolRAMGeneratedWrite.frame_image ((A).endAddress v.mesh) 1 _ _ x (.inl below)]
  exact run_frame C _ _ x live (fun e _=>(v.event_prefix P h width r _ _ _ _ _ e x
    (low.trans_le (Nat.le_add_right ..))).1)

/-- Original core operand expressions, the core-occurrence lookup and all original
permutation words remain valid on the very same output at which the paid widths and
the sparse affirmative purchased probes are read. -/
theorem wide_signed_core_output (stock : Bank) (M : ℕ) (π : Equiv.Perm (Fin (2^h))) (o : Orders h D k)
    (raw : Boot.Tape h D) (size : ℕ) (fits : (A).endAddress v.mesh ≤ size) (wordRoom : (A).endAddress v.mesh<2^w)
    (slices : List PaidWidths.Slice) (site : Fin cnt→Fin num) (debit : Fin cnt→ℕ)
    {I J : Type*} [Fintype I] [Fintype J] {core : I→List (Fin (P).catalogue.rows)} {center : J→List (Fin (P).catalogue.rows)}
    (route : Fin r≃RouteOccurrence core center) (ci : I→ℕ) (cj : J→ℕ) :
    let page:=v.wideSignedPage h width stock
    let dir:=WideMemory.dir h v.W k v.wideJobs
    let mid:=v.wideSignedMidAt h width size stock M π o raw
    let L:=ownerLedger s v.mesh (P).catalogue (P).routes F (TerminalLayout.ownerArea page stride)
    let b:=TerminalLayout.settlement page stock
    let a:=TerminalLayout.reserve start cnt page
    let src:=TerminalLayout.source page
    let owners:=sinkBank start cnt r (P).catalogue.rows
    let sink:=(P).catalogue.sink r b src (TerminalLayout.table page) (TerminalLayout.destination page) owners
    let C:=v.wideSignedChart h width stock
    let checked:=v.wideSignedCheckoutAt h width size stock M π o raw
    let g:=CoreRoute.source v.sampler h v.W k v.wideJobs v.depth (WideMemory.K h v.W) dir.groups
      (WideMemory.H h v.W k v.wideJobs) (WideMemory.R v.sampler h v.W k)
    let recipes:=routeBanks start cnt r
    let moves:=CoreRoute.stages b recipes g v.sampler h v.W k v.wideJobs
    let archive:=result moves (result (L.scans v.mesh num) (PaidWidths.output b.width (P).catalogue.rows src slices checked))
    let output:=sink.output (ReserveUse.output a b (fuel v.mesh*width) site debit archive) route ci cj
    Calendar.mounted C (events v.mesh) mid → PaidWidths.Mounted b.width (P).catalogue.rows src slices checked →
      Seen (v.wideOrder h width) M (WideMemory.groups h v.W) dir (v.wideSources h width).2 v.depth π output ∧
        (∀i : Fin (2^h),output i.val=((π i).val:Word w)) ∧ ∀x,x<(A).first → output x=mid x := by
  intro page dir mid L b a src owners sink C checked g recipes moves archive output live funded
  obtain ⟨_,_,boot,_,_,_,_,_,_⟩:=v.wide_signed_boot_at h width size fits stock M π o raw wordRoom
  have first : (A).first≤(A).endAddress v.mesh:=Nat.le_add_right ..
  have sourcePrefix:=v.wideGeometryPrefix h width
  have coreEnd:=sourcePrefix.2.2.trans (v.catalyst_initial_le_first P h width)
  have population:=sourcePrefix.1.trans (v.catalyst_initial_le_first P h width)
  have access (x : ℕ) (low : x<(A).first) : output x=mid x := by
    have level : TerminalLayout.footprint v.mesh A stock stride (P).catalogue.rows r num cnt<2^page:=Nat.lt_log2_self
    unfold TerminalLayout.footprint at level
    have before : x<2^page:=by omega
    exact (TerminalLayout.settled_below v.mesh A (P).catalogue L stock stride start (fuel v.mesh*width) site debit
      v.sampler v.wideJobs recipes g route ci cj checked slices x rfl before funded).trans
      (v.wide_signed_checkout_below h width stock M π o raw size x low live)
  have final:=boot.frame (coreEnd.trans_lt (first.trans_lt wordRoom)) (fun x hx=>access x (hx.trans_le coreEnd))
  refine ⟨final,?_,access⟩
  intro i
  have read:=final.board.input i
  change output (0+(i.val:Word w).val%2^h)=_ at read
  rw [Fin.val_cast_of_lt (i.isLt.trans_le (population.trans (first.trans wordRoom.le))),Nat.mod_eq_of_lt i.isLt,
    Nat.zero_add] at read
  exact read

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
