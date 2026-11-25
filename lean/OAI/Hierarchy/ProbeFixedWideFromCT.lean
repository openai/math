import OAI.Hierarchy.ProbeFixedWideCountedCode
import OAI.Hierarchy.ProbeFixedWideFundedTail
import OAI.Hierarchy.ProbeFixedWidePrefixTariff

namespace OAI
/-! # Authentic signed native paid controller after a compact subdivision boot -/
noncomputable section
set_option quotPrecheck false
set_option maxRecDepth 8192
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage CoreBoard CoreRoute ReportSockets
open CatalystArchive StripChart CatalogueRows ColumnWires StripDirectory
open ThreeFlat.RAM PhysicalProcedure
open ProbeStage.Native (text text_seq)
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
local notation "routes" => CoreRoute.stages old (routeBanks start cnt r) g v.sampler h v.W k v.wideJobs
local notation "supply" => fuel v.mesh*width


local notation "own" => TerminalLayout.ownerArea page stride
local notation "incoming" => resolvedStock v.mesh A (P).joint.initial (build F (withPorts s v.mesh (P).catalogue (P).routes))
local notation "pay" => cashWidthBase F s v.mesh (P).catalogue (P).routes incoming
local notation "market" => v.catalystMarkets P h width
local notation "o" => wideRouteOrder h D k


variable (size M : ℕ) (π : Equiv.Perm (Fin (2^h))) (raw : Boot.Tape h (2^v.W)) (bits : ℕ)
local notation "ss" => v.widePaidSlices h width bits
local notation "seed" => v.wideFundedRaw h width bits raw
local notation "mid" => v.wideSignedMidAt h width size stock M π o seed
local notation "chk" => v.wideSignedCheckoutAt h width size stock M π o seed
local notation "hi" => v.wideRoleStart h width stock ss
local notation "full" => v.wideFundedSize h width bits



local notation "compile" => v.wideEventSlices h width bits
local notation "lw" => v.wideWidthLayout h width ss
local notation "lr" => v.wideReserveLayout h width ss
local notation "a" => v.wideReplayArchive h width ss
local notation "n" => PrefixReserve.publicCount v.mesh decl
local notation "subs" => PrefixWidths.prefixRows (events v.mesh) compile
local notation "initial" => Boot.initial market size (v.wideSignedWords h width stock M π o seed)

attribute [local irreducible] CheapCode

theorem wide_from_ct_cheap (boot : Procedure w) (cheap : CheapCode boot) : CheapCode (v.wideFromCT h width bits boot) := by
  let settle := v.wideAfterCT h width bits
  let widths := PrefixWidths.program lw subs w last
  let reserve := PrefixReserve.program lr old a n supply w last
  have terminalCode : CheapCode settle := CatalystArchive.terminal_cheap C L routes ((A).endAddress v.mesh)
    sink (TerminalLayout.source page) ss original num cnt supply
  have widthCode : CheapCode widths := PrefixWidths.cheap lw subs last
  have reserveCode : CheapCode reserve := PrefixReserve.cheap lr old a n supply last
  exact @cheap_seq w ((boot.seq settle).seq widths) reserve
    (@cheap_seq w (boot.seq settle) widths (@cheap_seq w boot settle cheap terminalCode) widthCode) reserveCode

section
attribute [local irreducible] ThreeFlat.RAM.PhysicalProcedure.Procedure.Exec
  CatalystArchive.recordCount CatalystArchive.issued CatalystArchive.nativeSite CatalystArchive.debit

open Lean Elab Term in
local elab "replacementDates " cert:ident : term => do
  let proof ← Meta.getFVarFromUserName cert.getId
  let reconciliation ← Meta.whnf (← Meta.inferType proof)
  unless reconciliation.getAppFn.isConstOf ``Whole.Reconciliation do
    throwError "expected the prefix settlement reconciliation"
  let some recordRows := reconciliation.getAppArgs[7]? | throwError "expected the settlement record count"
  let count ← Meta.whnf recordRows
  unless count.getAppFn.isConstOf ``CatalystArchive.recordCount do
    throwError "expected the native record count"
  let issues ← Meta.whnf count.getAppArgs.back!
  unless issues.getAppFn.isConstOf ``CatalystArchive.issued do
    throwError "expected the dated issues"
  return ← instantiateMVars issues.getAppArgs.back!

set_option maxHeartbeats 4000000 in
/-- A replacement subdivision executes on the genuine complete header and reaches the genuine
complete boot memory. The paid terminal, signed board state, and all subsequent writes are literal. -/
abbrev wide_from_ct_run (extendsTape : full ≤ size) (height : v.wideFundedHeight≤h)
    (budget : v.keepLimit*width+1≤2^h) (small : width≤2^h) (state : Word w)
    (maxRows : ℕ) (room : (lr).scratch+2*max maxRows cnt<2^w) (lengths : ∀t∈ss,t.count≤ maxRows)
    (sized : ∀e : Fin rows,PaidWidths.total ss chk e<2^w) (boot : Procedure w) (ticks : ℕ)
    (started : boot.Exec initial mid ticks) :=
  let funded:=v.wide_funded_prefix_high_at h width size M π raw bits extendsTape height budget small state maxRows room lengths sized
  let receipt:=funded.1.1.1
  let dates := replacementDates receipt
  let board := (P).catalogue.coreMount π (siteNumber h D k) (v.wideOrder h width) chk
  let accounts : 0 < Fintype.card (Columns h D)*k :=
    Nat.mul_pos (Fintype.card_pos_iff.mpr ⟨.inl ⟨0, Nat.two_pow_pos _⟩⟩) v.positive
  let terminalRun:=v.wide_funded_tail_exec h width size M π raw bits extendsTape height budget small
    (dates:=dates) (pos:=accounts) (core:=board.ordinary) (center:=board.centers)
    (enum:=CoreRoute.enum board o) (ci:=PurchaseInventory.slot) (cj:=pairKeys (Columns h D) k) receipt
  let joined:=started.then terminalRun
  let extent:=(v.wide_funded_extent h width bits).trans extendsTape
  let adequate:=v.wide_signed_room h width stock (v.fixedTerminalStock_end P h width) ((le_max_left ..).trans height) budget
  let live:=(v.wide_funded_stock_at_size h width M π raw bits size extendsTape height budget small).mounted_all
  let paid:=v.wide_funded_paid_at_size h width M π raw bits size extendsTape height budget small
  let replay:=v.wide_append_for_dates h width size M π seed compile (boot.seq (v.wideAfterCT h width bits))
    (ticks+v.wideAfterCTTime h width bits) extent adequate.1 (dates:=dates) (pos:=accounts)
    (core:=board.ordinary) (center:=board.centers) (enum:=CoreRoute.enum board o)
    (ci:=PurchaseInventory.slot) (cj:=pairKeys (Columns h D) k) live paid maxRows room lengths sized receipt joined
  And.intro funded (And.intro replay.1 funded.2)

end

/-- Literal native text and ticks on the replacement boot. The only repeated charges
are the original paid and reserve scans in the genuine post-subdivision terminal. -/
theorem wide_from_ct_price (boot : Procedure w) (ticks : ℕ) :
    v.wideFromCTTime h width bits ticks≤ticks+(last+2)*v.wideAfterCTTime h width bits ∧
    text (v.wideFromCT h width bits boot)≤text boot+(last+2)*text (v.wideAfterCT h width bits) := by
  let pc:=PaidWidths.clock (old).width rows ss
  let rc:=19+12*num+160*cnt
  let paid:=PaidWidths.native w rows (TerminalLayout.source page) (old).width ss
  have sinkBanks : (sink).banks = old := rfl
  have c : pc+rc≤v.wideAfterCTTime h width bits := by
    unfold wideAfterCTTime CatalystArchive.terminalTime
    rw [sinkBanks, ReserveUse.clock_eq]
    change PaidWidths.clock (old).width rows ss+(19+12*num+160*cnt)≤_
    omega
  have t : text paid+218≤text (v.wideAfterCT h width bits) := by
    unfold wideAfterCT CatalystArchive.terminal
    simp only [text_seq,sinkBanks,PrefixReserve.native_text]
    change text (PaidWidths.native w rows (TerminalLayout.source page) (old).width ss)+218≤_
    omega
  have cap : PrefixWidths.time lw subs last≤(last+1)*pc :=
    PrefixWidths.time_prefix_le lw (events v.mesh) compile (old).width last
  have rom : text (PrefixWidths.program lw subs w last)≤(last+1)*text paid :=
    PrefixWidths.text_prefix_le w lw (events v.mesh) compile (old).width (TerminalLayout.source page) last
  have repay : PrefixReserve.cost num n last≤(last+1)*rc:=PrefixReserve.cost_le _ _
  have charge:=Nat.add_le_add cap repay
  rw [←Nat.mul_add] at charge
  have sum:=charge.trans (Nat.mul_le_mul_left _ c)
  have code:=Nat.add_le_add_right rom ((last+1)*218)
  rw [←Nat.mul_add] at code
  have bill:=code.trans (Nat.mul_le_mul_left _ t)
  constructor
  · unfold wideFromCTTime
    rw [Nat.succ_mul (last+1) (v.wideAfterCTTime h width bits)]
    omega
  · unfold wideFromCT
    simp only [text_seq,PrefixReserve.program_text]
    rw [Nat.succ_mul (last+1) (text (v.wideAfterCT h width bits))]
    omega

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
