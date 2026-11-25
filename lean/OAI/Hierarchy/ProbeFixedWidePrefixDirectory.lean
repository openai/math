import OAI.Hierarchy.ProbeFixedWideReserveOrigin
import OAI.Hierarchy.ProtocolRAMPrefixNativeDirectory
import OAI.Hierarchy.ProtocolRAMCatalystTerminalLower

namespace OAI
/-! # The original fixed two-level debit addresses in the real paid terminal output -/
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


local notation "own" => TerminalLayout.ownerArea page stride
local notation "incoming" => resolvedStock v.mesh A (P).joint.initial (build F (withPorts s v.mesh (P).catalogue (P).routes))
local notation "pay" => cashWidthBase F s v.mesh (P).catalogue (P).routes incoming
local notation "market" => v.catalystMarkets P h width
local notation "o" => wideRouteOrder h D k

variable (size M : ℕ) (π : Equiv.Perm (Fin (2^h))) (raw : Boot.Tape h (2^v.W))
local notation "mid" => v.wideSignedMidAt h width size stock M π o raw
local notation "chk" => v.wideSignedCheckoutAt h width size stock M π o raw

set_option maxRecDepth 8192 in
set_option cleanup.letToHave false in
set_option maxHeartbeats 1000000 in
/-- This uses the signed original input tape, every actual chronological pointer,
and only the history addresses named by those pointers. The width bank overlaps
the larger history address interval, so keeping its entire interval is unnecessary. -/
abbrev wide_final_directory_at (extent : (A).endAddress v.mesh ≤ size) (wordRoom : 28*2^page<2^w)
    (slices : List PaidWidths.Slice) (scratch : ℕ)
    (dates : Dates («w»:=w) C mid L pay num width) (pos : 0<num)
    (live : Calendar.mounted C (events v.mesh) mid) (paid : PaidWidths.Mounted (old).width rows (TerminalLayout.source page) slices chk)
    {I J : Type*} [Fintype I] [Fintype J] {core : I→List (Fin rows)} {center : J→List (Fin rows)}
    (enum : Fin r≃RouteOccurrence core center) (ci : I→ℕ) (cj : J→Fin num) :=
  let issues:=CatalystArchive.issued dates
  let nativeOwner:=nativeSite L v.mesh issues pos chk
  let dur:=debit v.mesh issues
  let archive:=result routes (result ((L).scans v.mesh num) (PaidWidths.output (old).width rows (TerminalLayout.source page) slices chk))
  let final:=(sink).output (ReserveUse.output original old supply nativeOwner dur archive) enum ci (fun j=>(cj j).val)
  fun (record : Whole.Reconciliation sink original supply nativeOwner dur enum ci cj archive) =>
    show PrefixReserve.Directory {original with scratch:=scratch} nativeOwner dur final from by
      let B:=2^page
      have span : TerminalLayout.footprint v.mesh A stock stride rows r num cnt < B := Nat.lt_log2_self
      unfold TerminalLayout.footprint at span
      have emb : (A).first≤(A).endAddress v.mesh:=Nat.le_add_right ..
      have lowArea : (A).endAddress v.mesh < B := by omega
      have canSee : (A).endAddress v.mesh<2^w := by change 28*B<2^w at wordRoom; omega
      have issuedSize : recordCount v.mesh issues=cnt :=
        recordCount_rowOnly v.mesh issues decl (issued_rows dates)
      have ptrSpan : start+2*2^((2*cnt).log2+1)≤(A).first :=
        (TerminalLayout.static_below start cnt r rows A (v.catalyst_static_end P h width A).le).2
      have ptrCap : 2*recordCount v.mesh issues≤2^((2*cnt).log2+1) := issuedSize ▸ Nat.lt_log2_self.le
      have boot:=v.wide_signed_origin_at h width size extent stock M π o raw canSee live
      have initial:=boot.issued v.mesh issues decl (issued_rows dates) ((own).base v.mesh) pay
      have archiveKeeps (x : ℕ) (small : x<6*B) (off : x<B ∨ B+rows≤x) : final x=archive x :=
        TerminalLayout.archive_prefix_at page start cnt supply (P).catalogue stock nativeOwner dur enum ci
          (fun j=>(cj j).val) archive x small off
      have firstPage (x : ℕ) (hx : x<B) : final x=chk x :=
        TerminalLayout.settled_below_at v.mesh A (P).catalogue L stock stride start cnt supply nativeOwner dur
          v.sampler v.wideJobs (routeBanks start cnt r) g enum ci (fun j=>(cj j).val) chk slices x rfl hx paid
      have ptrLow (j : ℕ) (hj : j<2*recordCount v.mesh issues) :
          (original).kind.base+j<B ∧ (original).pointer.base+j<B := by
        change start+j<B ∧ start+2^((2*cnt).log2+1)+j<B
        omega
      have kindFit : (original).kind.base+2*recordCount v.mesh issues≤(original).pointer.base :=
        Nat.add_le_add_left ptrCap _
      have word : 2*recordCount v.mesh issues≤2^w := by rw [issuedSize]; change 28*B<2^w at wordRoom; omega
      let any:=sourceAt v.mesh issues ((own).base v.mesh)
      let cash:=sourceAt v.mesh issues pay
      have srcLow (x : ℕ) (hx : x<B) : archive x=chk x :=
        (archiveKeeps x (by omega) (.inl hx)).symm.trans (firstPage x hx)
      have origin (j : ℕ) (hj : j<2*recordCount v.mesh issues) :=
        And.intro ((srcLow _ (ptrLow j hj).1).trans (initial.kept j hj).1)
          ((srcLow _ (ptrLow j hj).2).trans (initial.kept j hj).2)
      have survived (j : ℕ) (hj : j<2*recordCount v.mesh issues) :=
        And.intro (archiveKeeps _ (by have:=(ptrLow j hj).1; omega) (.inl (ptrLow j hj).1))
          (archiveKeeps _ (by have:=(ptrLow j hj).2; omega) (.inl (ptrLow j hj).2))
      have historySize : (original).history.size=4*B := by
        change 2^(page+2)=4*2^page
        simp [pow_add,Nat.mul_comm]
      have geometry (i : Fin (recordCount v.mesh issues)) : 2*B≤any i ∧ any i<3*B ∧ cash i<B := by
        let z:=(rank v.mesh issues).symm i
        let e:=(events v.mesh).get z.1
        have inTime : e∈events v.mesh := (events v.mesh).get_mem z.1
        have offset : z.2.val<(L).rows e :=
          z.2.isLt.trans_eq (issued_shape dates z.1 (fun _=>rfl))
        have bound : (L).rows e ≤ stride:=ledger_owner_rows s v.mesh (P).catalogue (P).routes F own e
        have ownEnd := (own).within v.mesh e inTime
        have cashEnd := (A).within v.mesh e inTime
        have tx : pay e+(L).rows e≤(A).base v.mesh e+(A).stride := by
          simpa only [v.catalyst_boards] using v.catalyst_amount_room P h width own e
        change 2*B≤(own).base v.mesh e+z.2.val ∧ (own).base v.mesh e+z.2.val<3*B ∧ pay e+z.2.val<B
        have lower : 2*B ≤ (own).base v.mesh e := Nat.le_add_right ..
        change (own).base v.mesh e+stride≤2*B+(events v.mesh).length*stride at ownEnd
        have slots : (events v.mesh).length*stride < B := by omega
        have ownerTail : 2*B+(events v.mesh).length*stride < 3*B := by omega
        exact ⟨lower.trans (Nat.le_add_right ..),
          (Nat.add_lt_add_left (offset.trans_le bound) _).trans_le (ownEnd.trans ownerTail.le),
          ((Nat.add_lt_add_left offset _).trans_le tx).trans_le (cashEnd.trans lowArea.le)⟩
      exact PrefixReserve.Directory.after_write original scratch old supply nativeOwner dur any cash raw archive final
        record.archive kindFit ptrCap ptrCap word origin survived
        (fun i=>by
          obtain ⟨lo,hi,_⟩:=geometry i
          change 28*B<2^w at wordRoom
          refine ⟨by rw [historySize]; omega,by omega,?_⟩
          simpa only [show (original).history.base=0 from rfl,Nat.zero_add] using
            archiveKeeps (any i) (by omega) (.inr (by omega)))
        (fun i=>by
          have hi:=(geometry i).2.2
          change 28*B<2^w at wordRoom
          refine ⟨by rw [historySize]; omega,by omega,?_⟩
          simpa only [show (original).history.base=0 from rfl,Nat.zero_add] using
            archiveKeeps (cash i) (by omega) (.inl hi))

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
